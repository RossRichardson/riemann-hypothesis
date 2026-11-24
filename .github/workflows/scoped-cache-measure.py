#!/usr/bin/env python3
"""Independent inventory of the real public receipt and the before/after checkout."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys


def load(script):
    spec = importlib.util.spec_from_file_location(script, Path("scripts", script + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def write(file, value):
    file.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n")


def main():
    action = sys.argv[1]
    output = Path(os.environ["RUNNER_TEMP"]) / "scoped-results"
    state = output / "inventory.json"
    root = Path.cwd()
    target = os.environ["TARGET"]
    if action == "receipt":
        client = load("ci-cache-get")
        quick = load("quick-check")
        identity = client.current_identity(root)
        receipt = client.find_record(root, identity)
        if receipt is None:
            receipt, _ = client.baseline_record(identity)
        if receipt is None:
            raise RuntimeError("no published successful receipt for this checkout")
        _, _, rows = client.validated_blobs(receipt, identity)
        closure = quick.dependency_closure(root, [target], maximum=20_000)
        published = {name: archive for name, _, archive in rows}
        if target not in closure or "Statements" in closure or not set(closure) < published.keys():
            raise RuntimeError("expected a strict subset of this public receipt")
        write(output / "receipt.json", receipt)
        write(state, {"published": published, "closure": closure})
        print(f"{len(closure)} project modules in the independently parsed import closure; {len(rows)} in the receipt")
        return

    inventory = json.loads(state.read_text())
    published = inventory["published"]
    wanted = set(inventory["closure"] if action == "scoped" else published)
    lib = root / ".lake/build/lib/lean"
    built = {".".join(path.relative_to(lib).with_suffix("").parts) for path in lib.rglob("*.olean")}
    built.intersection_update(published)
    if built != wanted:
        raise RuntimeError(f"build differs from requested closure: missing={sorted(wanted-built)[:10]}, "
                           f"extra={sorted(built-wanted)[:10]}")
    cached = root / ".lake/cache/artifacts"
    archives = {path.name: path.stat().st_size for path in cached.glob("*.ltar")}
    project = set(archives) & set(published.values())
    expected = {published[name] for name in wanted}
    if project != expected:
        raise RuntimeError(f"cached project archives differ from expected: missing={len(expected-project)}, "
                           f"extra={len(project-expected)}")
    paths = (".lake/build", ".lake/cache", ".lake/packages")
    result = {"checkout": os.environ["GITHUB_SHA"], "phase": action, "target": target,
              "project_modules": len(built), "receipt_modules": len(published),
              "unique_project_archives": len(project), "project_archive_bytes": sum(archives[a] for a in project),
              "allocated_bytes": {p: int(subprocess.check_output(["du", "-s", "-B1", p]).split()[0]) for p in paths}}
    write(output / (action + ".json"), result)
    print(json.dumps(result))
    with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as summary:
        print(f"**{action}** restored {len(built):,} project modules, {len(project):,} unique project archives, "
              f"{result['project_archive_bytes']:,} compressed bytes.", file=summary)


if __name__ == "__main__":
    main()
