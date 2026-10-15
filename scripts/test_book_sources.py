"""Publication must not silently omit an imported section."""
import json
from pathlib import Path
import tempfile
import unittest
from check_book_sources import inventory


class BookSources(unittest.TestCase):
    def fixture(self,root):
        (root/'plan').mkdir()
        (root/'sections').mkdir()
        (root/'main.tex').write_text('\\input{sections/19.1.tex}\n')
        (root/'sections/19.1.tex').write_text('\\section{Scope}\n\\label{sec:ch19-scope}\n')
        (root/'plan/imported_sections.json').write_text(json.dumps({'sections':[dict(number='19.1',id='ch19-scope',target='notes/latex/sections/19.1.tex')]}))

    def test_actual_graph_and_missing_section(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);self.fixture(root)
            self.assertEqual(inventory(root)['included_sections'],['19.1'])
            (root/'main.tex').write_text('% \\input{sections/19.1.tex}\n')
            with self.assertRaisesRegex(ValueError,'absent'): inventory(root)

    def test_wrapper_and_duplicate_numbers_are_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);self.fixture(root)
            path=root/'sections/19.1.tex'
            path.write_text(path.read_text()+'\\documentclass{book}\n')
            with self.assertRaisesRegex(ValueError,'wrapper'): inventory(root)
