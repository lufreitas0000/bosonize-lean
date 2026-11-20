"""Check fresh-build ordering and rejection of indirect sorry dependencies."""
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
import audit_axioms


class AxiomAudit(unittest.TestCase):
    def test_data_audit_rejects_indirect_sorry(self):
        with tempfile.TemporaryDirectory() as folder:
            repo = Path(folder)
            source = repo / 'BosonizeStubs/Fixture.lean'
            source.parent.mkdir()
            source.write_text('namespace Fixture\ndef value : Nat := 0\ntheorem claim : True := by sorry\nend Fixture\n')
            observed = []
            def run(argv, **kwargs):
                observed.append(argv)
                if 'env' in argv:
                    return subprocess.CompletedProcess(argv, 0, "'Fixture.value' depends on axioms: [sorryAx]\n", '')
                return subprocess.CompletedProcess(argv, 0, '', '')
            with patch.object(audit_axioms.subprocess, 'run', side_effect=run):
                with self.assertRaisesRegex(ValueError, 'Nonstandard axioms'):
                    audit_axioms.audit(repo, ['BosonizeStubs/Fixture.lean'], data_only=True)
            self.assertEqual(observed[1], ['lake', 'build', 'BosonizeStubs.Fixture'])
            self.assertIn('env', observed[2])

    def test_traversal_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Expected'):
            audit_axioms.audit(Path('/tmp'), ['BosonizeStubs/../Other.lean'])

    def test_private_declarations_filtered_from_exported_audit(self):
        code = (
            'namespace Fixture\n'
            'def pubVal : Nat := 1\n'
            'private def privVal : Nat := 2\n'
            'noncomputable private def privNoncomp : Nat := 3\n'
            'noncomputable local instance pubLocalInst : Inhabited Nat := ⟨0⟩\n'
            'private local instance privLocalInst : Inhabited Nat := ⟨1⟩\n'
            'private lemma privLem : pubVal = 1 := by rfl\n'
            '@[simp] private theorem privAttrThm : pubVal = 1 := by rfl\n'
            'protected lemma protLem : pubVal = 1 := by rfl\n'
            'theorem pubThm : pubVal = 1 := by exact privLem\n'
            'end Fixture\n'
        )
        self.assertEqual(
            audit_axioms.exported_declarations(code, data_only=False),
            ['Fixture.protLem', 'Fixture.pubThm', 'Fixture.pubVal', 'Fixture.pubLocalInst'],
        )
        self.assertEqual(
            audit_axioms.exported_declarations(code, data_only=True),
            ['Fixture.pubVal', 'Fixture.pubLocalInst'],
        )

    def test_audit_skips_private_in_generated_print_axioms(self):
        with tempfile.TemporaryDirectory() as folder:
            repo = Path(folder)
            source = repo / 'BosonizeStubs/Fixture.lean'
            source.parent.mkdir()
            source.write_text(
                'namespace Fixture\n'
                'private def hidden : Nat := 0\n'
                'def shown : Nat := hidden\n'
                'private lemma helper : shown = 0 := by rfl\n'
                'theorem claim : shown = 0 := by exact helper\n'
                'end Fixture\n'
            )
            generated = []
            def run(argv, **kwargs):
                if 'env' in argv:
                    text = Path(argv[-1]).read_text()
                    generated.append(text)
                    return subprocess.CompletedProcess(
                        argv, 0,
                        "'Fixture.claim' does not depend on any axioms\n"
                        "'Fixture.shown' does not depend on any axioms\n",
                        '',
                    )
                return subprocess.CompletedProcess(argv, 0, '', '')
            with patch.object(audit_axioms.subprocess, 'run', side_effect=run):
                audit_axioms.audit(repo, ['BosonizeStubs/Fixture.lean'], data_only=False)
            self.assertEqual(len(generated), 1)
            self.assertIn('#print axioms Fixture.claim', generated[0])
            self.assertIn('#print axioms Fixture.shown', generated[0])
            self.assertNotIn('Fixture.helper', generated[0])
            self.assertNotIn('Fixture.hidden', generated[0])
