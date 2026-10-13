import contextlib
import io
import tempfile
import unittest
from pathlib import Path

import verify_phase_a as verifier


def proposal(code):
    return ("## Source map\nFixture only.\n## Design and scope\nVerifier test, not a chapter.\n"
            "## Lean draft\n```lean\n" + code + "\n```\n## Companion notebook\nNo proofs.\n"
            "## Review obligations\nIndependent mathematical review remains pending.\n")


CODE = "import Bosonize\nnamespace WebLLMFixture\ndef value : Nat := 1\nlemma identity : value = 1 := by sorry\nend WebLLMFixture\n"


class Tests(unittest.TestCase):
    def test_accepts_exact_stubs(self):
        _, data, count = verifier.inspect(proposal(CODE))
        self.assertEqual(data, ["WebLLMFixture.value"])
        self.assertEqual(count, 1)

    def test_rejects_data_placeholder_proof_or_axiom(self):
        for code in (CODE.replace("Nat := 1", "Nat := by sorry"), CODE.replace("by sorry", "by rfl"),
                     CODE.replace("def value", "axiom value"), CODE.replace("by sorry", "by admit")):
            with self.subTest(code=code), self.assertRaises(ValueError):
                verifier.inspect(proposal(code))

    def test_requires_source_and_review_sections(self):
        with self.assertRaises(ValueError):
            verifier.inspect(proposal(CODE).replace("## Source map", "## Omitted"))

    def test_real_elaboration_and_indirect_sorry_audit(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "draft.md"
            path.write_text(proposal(CODE))
            with contextlib.redirect_stdout(io.StringIO()):
                verifier.verify(path)
            path.write_text(proposal("import Bosonize\nnamespace WebLLMFixture\n"
                                     "lemma hole : True := by sorry\n"
                                     "def bad : True := hole\nend WebLLMFixture\n"))
            with contextlib.redirect_stdout(io.StringIO()), self.assertRaisesRegex(ValueError, "unapproved axioms"):
                verifier.verify(path)


if __name__ == "__main__":
    unittest.main()
