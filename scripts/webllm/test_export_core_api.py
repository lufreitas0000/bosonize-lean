"""Context integrity: exact examples, complete coverage, scope order, fail closed."""
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import export_core_api as exporter


class ExportContextTests(unittest.TestCase):
    def test_preserves_section_context_and_exact_selected_body(self):
        code = ('namespace Fixture\nvariable (n : Nat)\n'
                'lemma first : n = n := by rfl\n'
                'omit n in\nlemma second : True := by trivial\nend Fixture\n')
        result = exporter.excerpt(code, {'first'})
        self.assertIn('lemma first : n = n := by rfl', result)
        self.assertNotIn('by trivial', result)
        self.assertLess(result.index('variable (n : Nat)'), result.index('lemma first'))
        self.assertIn('omit n in lemma second : True', result)

    def test_missing_example_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Missing proof examples'):
            exporter.excerpt('namespace X\nlemma ok : True := by trivial\nend X', {'absent'})

    def test_every_frozen_module_and_target_obligation_is_present(self):
        result = exporter.render()
        repo = exporter.verifier.REPO
        hashes = json.loads((repo / 'docs/spec/core_locks.json').read_text())
        for name, digest in hashes.items():
            self.assertIn('## ' + name, result)
            self.assertIn('Full source SHA-256: ' + digest, result)
        model = exporter.verifier.lean.parse_lean((repo / 'BosonizeStubs/A06ChiralFields.lean').read_text())
        for name in model.lemmas:
            self.assertIn('`' + name.split('.')[-1] + '`', result)
        self.assertTrue('def speciesBudget' in result, 'Missing speciesBudget definition')
        self.assertIn('lemma excitation_nonneg', result)
        self.assertIn('noncomputable def coordinateSpace', result)
        self.assertEqual(result, (repo / 'docs/webllm/ch15_core_api.md').read_text())

    def test_inventory_mismatch_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            repo = Path(folder)
            (repo / 'docs/spec').mkdir(parents=True)
            (repo / 'docs/spec/core_locks.json').write_text('{"Bosonize/Core/Absent.lean": "x"}')
            with self.assertRaisesRegex(ValueError, 'inventory'):
                exporter.render(repo)

    def test_frozen_hash_mismatch_rejected(self):
        original = exporter.hashlib.sha256
        class WrongHash:
            def hexdigest(self):
                return '0' * 64
        with patch.object(exporter.hashlib, 'sha256', return_value=WrongHash()):
            with self.assertRaisesRegex(ValueError, 'hash mismatch'):
                exporter.render()
        self.assertIs(exporter.hashlib.sha256, original)


if __name__ == '__main__':
    unittest.main()
