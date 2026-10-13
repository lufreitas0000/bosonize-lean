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
