"""Check that splitting clumps preserves existing worktree files."""
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import clump


class UnclumpTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        self.src = self.root / "src"
        self.src.mkdir()
        self.git("init", "-q")
        # A collision in the second clump must leave the first one intact as well.
        self.original = {}
        plan = {}
        for member, root in (("A", "B"), ("C", "D")):
            self.original[member] = f"module\n\ndef value{member} : Nat := 1\n"
            self.original[root] = f"module\nimport {member}\n\ndef value{root} := value{member}\n"
            plan[root] = [member, root]
        for name, content in self.original.items():
            self.file(name).write_text(content)
        self.git("add", "src")
        clump.apply(self.root, plan)
        self.git("add", "-A")

    def git(self, *args):
        subprocess.run(["git", "-C", self.root, *args], check=True)

    def file(self, name):
        return self.src / (name + ".lean")

    def snapshot(self):
        return {p.name: p.read_bytes() for p in self.src.iterdir()}

    def test_existing_edits_abort_before_restoring_any_members(self):
        self.file("C").write_text("def newTheorem : Nat := 99\n")
        before = self.snapshot()
        for state in ("untracked", "ignored", "tracked"):
            with self.subTest(state=state):
                if state == "ignored":
                    (self.root / ".gitignore").write_text("src/C.lean\n")
                if state == "tracked":
                    self.git("add", "-f", "src/C.lean")
                with self.assertRaisesRegex(ValueError, r"C\.lean"):
                    clump.unclump(self.root)
                self.assertEqual(self.snapshot(), before)

    def test_identical_member_is_kept_and_other_members_are_restored(self):
        self.file("C").write_text(self.original["C"])
        os.utime(self.file("C"), (1_000_000, 1_000_000))
        before = self.file("C").stat().st_mtime_ns
        clump.unclump(self.root)
        self.assertEqual(self.file("C").stat().st_mtime_ns, before)
        self.assertEqual(self.snapshot(), {name + ".lean": text.replace("\n", os.linesep).encode()
                                          for name, text in self.original.items()})

    def test_different_newlines_are_preserved(self):
        other_newline = "\n" if os.linesep == "\r\n" else "\r\n"
        self.file("C").write_bytes(self.original["C"].replace("\n", other_newline).encode())
        before = self.snapshot()
        with self.assertRaisesRegex(ValueError, r"C\.lean"):
            clump.unclump(self.root)
        self.assertEqual(self.snapshot(), before)

    def test_linked_clump_root_preserves_target(self):
        target = self.root / "outside.lean"
        self.file("D").rename(target)
        self.file("D").symlink_to(target)
        before = self.snapshot()
        with self.assertRaisesRegex(ValueError, "symbolic link"):
            clump.unclump(self.root)
        self.assertEqual(self.snapshot(), before)
        self.assertTrue(self.file("D").is_symlink())

    def rename_member(self, old, new):
        p = self.file("D")
        text = p.read_text().replace(f"member: {old} =====", f"member: {new} =====")
        p.write_text(text.replace(f'"m": "{old}"', f'"m": "{new}"'))

    def test_missing_root_aborts_without_writes(self):
        self.rename_member("D", "E")
        before = self.snapshot()
        with self.assertRaisesRegex(ValueError, "own module"):
            clump.unclump(self.root)
        self.assertEqual(self.snapshot(), before)

    def test_changed_clump_after_preflight_is_preserved(self):
        original = clump.restored_members
        edit = self.file("B").read_text().replace("Nat := 1", "Nat := 99")
        def edit_earlier_clump(root, text):
            if "member: D =====" in text:
                self.file("B").write_text(edit)
            return original(root, text)
        with patch.object(clump, "restored_members", side_effect=edit_earlier_clump):
            with self.assertRaisesRegex(ValueError, "clump changed"):
                clump.unclump(self.root)
        self.assertEqual(self.file("B").read_text(), edit)
        self.assertFalse(self.file("A").exists())

    def test_duplicate_destination_across_clumps_aborts_without_writes(self):
        self.rename_member("C", "A")
        before = self.snapshot()
        with self.assertRaisesRegex(ValueError, "duplicate unclump destination"):
            clump.unclump(self.root)
        self.assertEqual(self.snapshot(), before)

    def test_duplicate_member_in_one_clump_aborts_without_writes(self):
        self.rename_member("C", "D")
        before = self.snapshot()
        with self.assertRaisesRegex(ValueError, "duplicate clump member"):
            clump.unclump(self.root)
        self.assertEqual(self.snapshot(), before)


if __name__ == "__main__":
    unittest.main()
