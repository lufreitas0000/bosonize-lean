import contextlib
import io
import tempfile
import unittest
from pathlib import Path

import verify_phase_b as verifier


class Tests(unittest.TestCase):
    def test_dependency_order_and_cycle(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            (root / "BosonizeStubs").mkdir()
            a, b = root / "BosonizeStubs/A.lean", root / "BosonizeStubs/B.lean"
            a.write_text("import Bosonize\n")
            b.write_text("import BosonizeStubs.A\n")
            self.assertEqual(verifier.dependencies(root, ["BosonizeStubs/B.lean"]),
                             ["BosonizeStubs/A.lean", "BosonizeStubs/B.lean"])
            a.write_text("import BosonizeStubs.B\n")
            with self.assertRaisesRegex(ValueError, "cycle"):
                verifier.dependencies(root, ["BosonizeStubs/B.lean"])

    def test_fresh_dependency_compile_and_unproved_dependency_rejection(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            (root / "BosonizeStubs").mkdir()
            a, b = root / "BosonizeStubs/A.lean", root / "BosonizeStubs/B.lean"
            a.write_text("import Bosonize\nnamespace WebLLMProofFixture\ndef value : Nat := 1\n"
                         "lemma value_eq : value = 1 := by rfl\nend WebLLMProofFixture\n")
            b.write_text("import BosonizeStubs.A\nnamespace WebLLMProofFixture\n"
                         "lemma consumer : value = 1 := by exact value_eq\nend WebLLMProofFixture\n")
            order = verifier.dependencies(root, ["BosonizeStubs/B.lean"])
            with contextlib.redirect_stdout(io.StringIO()):
                verifier.compile_modules(root, order, verifier.phase_a.REPO)
            a.write_text(a.read_text().replace("by rfl", "by sorry"))
            with self.assertRaisesRegex(ValueError, "Unproved"):
                verifier.compile_modules(root, order, verifier.phase_a.REPO)


if __name__ == "__main__":
    unittest.main()
