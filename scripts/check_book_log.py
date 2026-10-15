#!/usr/bin/env python3
"""Fail publication on unresolved citations/references or duplicate labels."""
import re
import sys
from pathlib import Path


def errors(text):
    patterns = [r'LaTeX Warning:.*undefined', r'LaTeX Warning:.*multiply defined',
                r'There were undefined references', r'There were multiply-defined labels',
                r'No file .*\.(?:tex|bbl)']
    return [line for line in text.splitlines() if any(re.search(p,line) for p in patterns)]


if __name__ == '__main__':
    findings=errors(Path(sys.argv[1]).read_text(errors='replace'))
    print('\n'.join(findings) if findings else 'PASS: references, citations and labels')
    raise SystemExit(bool(findings))
