"""Regression tests for the plan and apply commands in clump.py."""
import contextlib
import io
import subprocess
import tempfile
import unittest
from pathlib import Path

import clump


class ClumpPlanTests(unittest.TestCase):
    def setUp(self):
        worktree = tempfile.TemporaryDirectory()
        self.addCleanup(worktree.cleanup)
        self.root = Path(worktree.name)
        subprocess.run(["git", "init", "-q", self.root], check=True)

    def module(self, name, text):
        path = self.root / "src" / Path(*name.split(".")).with_suffix(".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        subprocess.run(["git", "-C", self.root, "add", path], check=True)
        return path

    def plan(self, max_lines, exclude=()):
        mods = clump.load(self.root, keep_source=False)
        clashes = io.StringIO()
        with contextlib.redirect_stderr(clashes):
            result = clump.plan(mods, max_lines, exclude)
        return result, clashes.getvalue()

    def test_nested_clumps_keep_import_order_and_the_line_limit(self):
        self.module("L.A", "module\n\ndef a := 1\n")
        self.module("L.B", "module\nimport L.A\n\ndef b := a\n")
        self.module("L.C", "module\n\ndef c := 1\n")
        self.module("L.R", "module\nimport L.B\nimport L.C\n\ndef r := b + c\n")
        # B and C are considered by size, then the output is ordered by R's imports.
        all_members = ["L.A", "L.B", "L.C", "L.R"]
        self.assertEqual(self.plan(1000)[0], {"L.R": all_members})
        self.assertEqual(self.plan(21)[0], {"L.B": ["L.A", "L.B"], "L.R": ["L.C", "L.R"]})
        self.assertEqual(self.plan(1000, {"L.B"})[0], {"L.R": ["L.C", "L.R"]})

    def test_decl_clash_preserves_an_already_formed_child_clump(self):
        self.module("L.A", "module\n\nprivate def shared := 1\n")
        self.module("L.B", "module\nimport L.A\n\ndef b := 2\n")
        self.module("L.R", "module\nimport L.B\n\nprivate def shared := 3\n")
        plan, diagnostic = self.plan(1000)
        self.assertEqual(plan, {"L.B": ["L.A", "L.B"]})
        self.assertIn("refused 1 folds", diagnostic)

    def test_header_only_and_preexisting_clumps(self):
        header = "module\npublic import Mathlib.X\n"
        mod = clump.Module("L.A", "src/L/A.lean", header)
        self.assertEqual((mod.header, mod.body, mod.lines), (header, "", 6))
        self.assertFalse(clump.is_clump_file(mod))
        for marker in (clump.CLUMP_MARK, "-- example: " + clump.SEAM_BEGIN):
            self.module("L.A", header + "\nsection\n" + marker + "\nend\n")
            self.module("L.R", "module\nimport L.A\n\ndef r := 1\n")
            self.assertEqual(self.plan(1000)[0], {})

    def test_cycle_is_rejected(self):
        self.module("L.A", "module\nimport L.B\n")
        self.module("L.B", "module\nimport L.A\n")
        with self.assertRaisesRegex(SystemExit, "cycle"):
            self.plan(1000)

    def test_invalid_plans_leave_all_sources_in_place(self):
        paths = [self.module(n, "module\n") for n in ["L.A", "L.B", "L.C"]]
        cases = [
            ({"L.B": ["L.A"]}, "own module"),
            ({"L.B": ["L.A", "L.B"], "L.C": ["L.A", "L.C"]}, "duplicate"),
            ({"L.B": ["L.A", "L.B"], "L.C": ["L.X", "L.C"]}, "missing"),
        ]
        for plan, reason in cases:
            with self.subTest(reason=reason):
                with self.assertRaisesRegex(ValueError, reason):
                    clump.apply(self.root, plan)
                self.assertEqual([p.read_text(encoding="utf-8") for p in paths], ["module\n"] * 3)

    def test_only_selected_sources_are_read_and_rendered(self):
        leaf = "module\n\nnamespace N\ndef a := 1"
        root = "module\npublic import L.A\n\ndef b := N.a\n"
        a, r = self.module("L.A", leaf), self.module("L.R", root)
        self.module("L.Unrelated", "module\n").unlink()
        clump.apply(self.root, {"L.R": ["L.A", "L.R"]})
        merged = r.read_text(encoding="utf-8")
        self.assertIn("end N" + clump.AUTO, merged)
        self.assertEqual(clump.unclump_text(merged), {"L.A": leaf, "L.R": root})
        self.assertFalse(a.exists())


if __name__ == "__main__":
    unittest.main()
