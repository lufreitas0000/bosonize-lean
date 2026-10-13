import tempfile
import unittest
from pathlib import Path
import verify_phase_c


class MarkdownReview(unittest.TestCase):
    def test_required_scope_and_limits(self):
        with tempfile.TemporaryDirectory() as folder:
            candidate = Path(folder) / 'candidate.md'
            candidate.write_text('## Proved scope\n## Evidence\n## Pedagogical changes\n')
            with self.assertRaisesRegex(ValueError, 'Remaining limitations'):
                verify_phase_c.inspect(candidate)
            candidate.write_text(candidate.read_text() + '## Remaining limitations\nHuman review required.\n')
            verify_phase_c.inspect(candidate)
