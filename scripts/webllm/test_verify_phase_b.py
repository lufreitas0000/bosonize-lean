import contextlib
import io
import tempfile
import unittest
from pathlib import Path

import verify_phase_b as verifier


class Tests(unittest.TestCase):
    def test_private_axiom_output_and_multiline_lists(self):
        verifier.check_axiom_output(
            "'_private.BosonizeStubs.Fixture.0.Fixture.helper' depends on axioms: [\n"
            "  propext, Classical.choice,\n  Quot.sound]\n"
            "'Fixture.public' does not depend on any axioms\n",
            ["Fixture.helper", "Fixture.public"])
        verifier.check_axiom_output(
            "'_private.BosonizeStubs.Fixture.12.Fixture.helper' does not depend on any axioms\n",
            ["Fixture.helper"])

    def test_axiom_output_rejects_missing_or_wrong_declaration(self):
        for output in ("", "'Other.Fixture.helper' does not depend on any axioms\n",
                       "'_private.Module.zero.Fixture.helper' does not depend on any axioms\n",
                       "'_private.Module.0.Fixture.helper_extra' does not depend on any axioms\n"):
            with self.subTest(output=output), self.assertRaisesRegex(ValueError, "Missing fresh"):
                verifier.check_axiom_output(output, ["Fixture.helper"])

    def test_private_axiom_output_rejects_nonstandard_axioms(self):
        output = ("'_private.Module.0.Fixture.helper' depends on axioms: [\n"
                  "propext,\n sorryAx]\n")
        with self.assertRaisesRegex(ValueError, "Nonstandard.*sorryAx"):
            verifier.check_axiom_output(output, ["Fixture.helper"])

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
                         "private lemma helper : value = 1 := by rfl\n"
                         "lemma value_eq : value = 1 := by exact helper\nend WebLLMProofFixture\n")
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
