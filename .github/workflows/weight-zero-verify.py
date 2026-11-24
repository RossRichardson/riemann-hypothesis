#!/usr/bin/env python3
"""Compile the touched modules from source on a single Linux runner, using attested dependencies."""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import statistics
import subprocess
import sys
import time
import traceback

TOOLCHAIN = "leanprover/lean4:v4.37.0-rc1"
RECEIPT = "1cd97d8aa4a16681b109389ab18eefa4b2ba36d8"
PREFIX = "Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory."
COMMON = [PREFIX + s for s in ("LaConv", "WtMatFix")]
SHARED = PREFIX + "WeightZeroPeriodMatrices"
ALL = [*COMMON, SHARED]


def load(path):
    spec = importlib.util.spec_from_file_location(path.stem, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def source(module):
    return Path("src", *module.split(".")).with_suffix(".lean")


def tree(root):
    inventory = subprocess.check_output(["git", "-C", root, "ls-tree", "-r", "-z", "HEAD", "src"])
    return {path.decode(): metadata for entry in inventory.split(b"\0") if entry
            for metadata, path in [entry.split(b"\t", 1)]}


def main():
    base = Path("baseline").resolve()
    head = Path("candidate").resolve()
    temp = Path(os.environ["RUNNER_TEMP"])
    output = temp / "weight-zero-results"
    state = temp / "weight-zero-state"
    output.mkdir()
    state.mkdir()
    log = {"status": "started", "samples": [], "scope": "changed Lean modules"}
    begin = time.monotonic()

    def save():
        (output / "result.json").write_text(json.dumps(log, indent=2) + "\n")

    ci = load(base / "scripts/ci-build.py")
    prep = load(base / "scripts/ci-prepare.py")
    quick = load(base / "scripts/quick-check.py")
    client = load(base / "scripts/ci-cache-get.py")

    def run(name, command, directory, environment, timeout=2400):
        print(f"Running {name}", flush=True)
        before = Path.cwd()
        started = time.monotonic()
        try:
            os.chdir(directory)
            with (output / (name + ".log")).open("wb") as stream:
                code = ci.supervised_build(command, environment, stream, [state], 2, timeout_seconds=timeout)
        finally:
            os.chdir(before)
        elapsed = round(time.monotonic() - started, 3)
        print(f"{name}: exit {code}, {elapsed} s", flush=True)
        if code:
            print((output / (name + ".log")).read_text(errors="replace")[-16000:], flush=True)
            raise RuntimeError(f"{name} exited {code}")
        return elapsed

    try:
        approved = client.settings.for_toolchain(TOOLCHAIN)
        ids = {}
        for label, root, expected in (("before", base, os.environ["BASE_SHA"]),
                                      ("after", head, os.environ["GITHUB_SHA"])):
            if ci.git(root, "rev-parse", "HEAD") != expected:
                raise ValueError(f"wrong {label} checkout")
            ids[label] = client.current_identity(root)
            if ids[label]["toolchain"] != TOOLCHAIN or ids[label]["manifest_sha256"] != approved.DEPENDENCIES:
                raise ValueError(f"unexpected {label} toolchain or dependency lockfile")
        for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
            if (base / name).read_bytes() != (head / name).read_bytes():
                raise ValueError("changed configuration: " + name)
        trees = [tree(root) for root in (base, head)]
        changed = {name for name in trees[0].keys() | trees[1].keys() if trees[0].get(name) != trees[1].get(name)}
        if changed != {str(source(m)) for m in ALL} or (base / source(SHARED)).exists():
            raise ValueError(f"expected two changed consumers and one new module; got {sorted(changed)}")
        version = subprocess.check_output(["lean", "--version"], text=True).strip()
        if not version.startswith(f"Lean (version {approved.VERSION},") or approved.COMMIT not in version:
            raise ValueError("unexpected compiler: " + version)
        tc = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
        log.update(lean=version, threads=1, source_identities=ids, baseline=os.environ["BASE_SHA"],
                   candidate=os.environ["GITHUB_SHA"], changed=sorted(changed),
                   runner=os.uname().machine, free_bytes_at_start=shutil.disk_usage(state).free)
        save()

        targets = {"before": COMMON, "after": ALL}
        closures = {label: set(quick.dependency_closure(root, targets[label], maximum=20000))
                    for label, root in (("before", base), ("after", head))}
        selected = set.union(*closures.values())
        log["project_ancestors_including_targets"] = {k: len(v) for k, v in closures.items()}
        raw = client.fetch(f"ci/revisions/{RECEIPT}.json", client.MAX_RECEIPT)
        receipt = client.matching_record(raw, ids["before"]) if raw else None
        if receipt is None or receipt["candidate_head"] != RECEIPT:
            raise ValueError("no successful receipt for the exact original source and configuration")
        _, digests, rows = client.validated_blobs(receipt, ids["before"])
        (output / "receipt.json").write_bytes(raw)
        rows = [row for row in rows if row[0] in selected and row[0] not in ALL]
        cached_names = {row[0] for row in rows}
        if selected - cached_names - set(ALL):
            raise ValueError(f"dependency receipt misses {sorted(selected - cached_names - set(ALL))}")
        log["cached_project_modules"] = len(rows)
        save()

        deps = state / "dependencies"
        deps.mkdir()
        (deps / "src").mkdir()
        for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
            shutil.copyfile(base / name, deps / name)
        host = prep.clean_env()
        host.update(ELAN_TOOLCHAIN=TOOLCHAIN, MATHLIB_CACHE_GET_URL="https://cache.mathlib.org/mathlib4",
                    LEAN_NUM_THREADS="1", LEAN_ABORT_ON_PANIC="1")
        external = {dep for root, cone in ((base, closures["before"]), (head, closures["after"]))
                    for module in cone for dep in quick.imports(root / source(module))
                    if dep.startswith(("Mathlib.", "Batteries.", "Aesop.")) or dep == "Mathlib"}
        run("mathlib-cache", ["lake", "exe", "mathlib/cache", "get", *sorted(external)], deps, host)
        packages = deps / ".lake/packages"
        ci.validate_packages(base, packages)

        control, result, cache, project = [state / name for name in ("control", "result", "cache", "project")]
        for directory in (control, result, cache / "artifacts", project):
            directory.mkdir(parents=True)
        mapping = control / "scoped.map"
        client.write_map(mapping, [(key, archive) for _, key, archive in rows])
        hashes = control / "hashes.json"
        hashes.write_text(json.dumps({archive: digests[archive] for _, _, archive in rows}))
        run("project-cache", [sys.executable, "-I", str(client.FETCH_ARTIFACTS), str(mapping), str(cache),
                              "--sha256", str(hashes), "--verify-existing",
                              "--base-url", f"{client.PUBLIC_BASE}/artifacts/{client.REPOSITORY}/",
                              "--user-agent", client.USER_AGENT], deps, host)
        log["downloaded_project_bytes"] = sum(p.stat().st_size for p in (cache / "artifacts").iterdir())
        save()
        ci.snapshot(base, os.environ["BASE_SHA"], project)
        (project / ".lake/packages").mkdir(parents=True)
        overrides = ci.package_overrides(project, control)
        private = ci.private_package_builds(project, packages, state / "private-packages")
        sandbox = ci.sandbox(tc, project, packages, cache, result, control, 1, private)
        sandbox += ["env", "LEAN_ABORT_ON_PANIC=1", "LAKE_RESTORE_ARTIFACTS=false", "LAKE_ARTIFACT_CACHE=false"]
        warm = client.unpack_jobs(project, cache, rows)
        for job in warm:
            for directory in map(Path, job["base"]):
                directory.mkdir(parents=True, exist_ok=True)
            job["base"] = ["/work/project/" + str(Path(d).relative_to(project)) for d in job["base"]]
            job["file"] = "/work/cache/" + str(Path(job["file"]).relative_to(cache))
        jobs = control / "unpack.json"
        jobs.write_text(json.dumps(warm))
        with jobs.open("rb") as stream:
            subprocess.run([*sandbox, "/opt/lean/bin/leantar", "--jobs", "4", "-f", "-x", "-j", "-"],
                           stdin=stream, env=ci.trusted_env(), check=True, timeout=900)
        # The trace contains the attested input hash; Lake checks it against current inputs.
        # Reclaim the compressed copies before preparing multiple fresh compiler samples.
        shutil.rmtree(cache / "artifacts")
        (cache / "artifacts").mkdir()
        lake = ["/opt/lean/bin/lake", "--packages", overrides, "--rehash", "build"]
        direct = {m for root, label in ((base, "before"), (head, "after")) for t in targets[label]
                  for m in quick.imports(root / source(t)) if m in selected and m not in ALL}
        run("preflight-dependencies", [*sandbox, *lake, *("+" + m for m in sorted(direct))],
            project, ci.trusted_env())
        # ABBAAB puts three cold-target measurements of each variant on the same runner.
        for index, label in enumerate(("before", "after", "after", "before", "before", "after"), 1):
            root = base if label == "before" else head
            for module in ALL:
                path = source(module)
                if (root / path).exists():
                    shutil.copyfile(root / path, project / path)
                else:
                    (project / path).unlink(missing_ok=True)
                for directory in ("lib/lean", "ir"):
                    stem = project / ".lake/build" / directory / Path(*module.split("."))
                    for artifact in stem.parent.glob(stem.name + ".*"):
                        if artifact.is_file() or artifact.is_symlink():
                            artifact.unlink()
            name = f"{index}-{label}"
            command = [*sandbox, "/usr/bin/time", "-o", "/work/result/" + name + ".time",
                       "-f", "%e %U %S %M", *lake, *("+" + m for m in targets[label])]
            run(name, command, project, ci.trusted_env())
            wall, user, system, peak = (result / (name + ".time")).read_text().strip().split()
            sizes = {}
            for module in targets[label]:
                olean = project / ".lake/build/lib/lean" / Path(*module.split(".")).with_suffix(".olean")
                if not olean.is_file() or not olean.stat().st_size:
                    raise ValueError("fresh build did not produce " + str(olean))
                sizes[module] = olean.stat().st_size
            sample = dict(case=label, wall_s=float(wall), user_s=float(user), system_s=float(system),
                          peak_process_rss_kib=int(peak), olean_bytes=sizes)
            log["samples"].append(sample)
            save()
            print(json.dumps(sample), flush=True)
        ci.verify_private_packages(project, packages, private)
        log["medians"] = {label: {field: statistics.median(sample[field] for sample in log["samples"]
                                                            if sample["case"] == label)
                                  for field in ("wall_s", "user_s", "system_s", "peak_process_rss_kib")}
                          for label in targets}
        log["status"] = "passed"
    except BaseException as error:
        log.update(status="failed", error=f"{type(error).__name__}: {error}")
        (output / "exception.txt").write_text(traceback.format_exc())
        raise
    finally:
        log.update(elapsed_s=round(time.monotonic() - begin, 3), free_bytes_at_end=shutil.disk_usage(state).free)
        save()
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as out:
            print("## Weight-zero period matrix compilation", file=out)
            print("Both consumers are compiled from source in each sample. Candidate samples also compile the new shared module.", file=out)
            print("\n```json\n" + json.dumps({k: log[k] for k in ("status", "medians", "error") if k in log}, indent=2)
                  + "\n```", file=out)


if __name__ == "__main__":
    main()
