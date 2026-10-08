"""Mutation tests for immutable Core sources, including completed proof bodies."""

import hashlib
from pathlib import Path
import tempfile
import unittest

import core_lock


class CoreLockTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.source = self.root / "Bosonize/Core/Ch01.lean"
        self.source.parent.mkdir(parents=True)
        self.source.write_text("lemma example_claim : True := by trivial\n")
        self.baseline = {"Bosonize/Core/Ch01.lean": hashlib.sha256(self.source.read_bytes()).hexdigest()}

    def test_unchanged(self):
        self.assertEqual(core_lock.check(self.root, self.baseline), [])

    def test_proof_body_changed(self):
        self.source.write_text("lemma example_claim : True := by sorry\n")
        self.assertIn("Frozen Core source changed", core_lock.check(self.root, self.baseline)[0])

    def test_file_removed(self):
        self.source.unlink()
        self.assertIn("Frozen Core file missing", core_lock.check(self.root, self.baseline)[0])

    def test_file_added(self):
        (self.source.parent / "Unreviewed.lean").write_text("axiom bad : False\n")
        self.assertIn("Unreviewed Core file", core_lock.check(self.root, self.baseline)[0])

    def test_comment_changed(self):
        self.source.write_text(self.source.read_text() + "-- source changed\n")
        self.assertTrue(core_lock.check(self.root, self.baseline))

    def test_invalid_manifest(self):
        for baseline in [[], {"file": "invalid"}, {"file": 7}]:
            with self.subTest(baseline=baseline):
                self.assertTrue(core_lock.check(self.root, baseline))


if __name__ == "__main__":
    unittest.main()
