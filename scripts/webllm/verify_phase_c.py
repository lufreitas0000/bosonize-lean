#!/usr/bin/env python3
"""Check Phase C Markdown structure; prose truth still requires human review."""
import argparse
from pathlib import Path

HEADINGS = ('Proved scope', 'Evidence', 'Pedagogical changes', 'Remaining limitations')


def inspect(path):
    text = Path(path).read_text(encoding='utf-8')
    for heading in HEADINGS:
        if f'## {heading}' not in text.splitlines():
            raise ValueError(f'Missing heading: ## {heading}')
    if not text.strip() or '\x00' in text:
        raise ValueError('Empty/invalid Markdown')
    print(f'PASS Markdown structure: {path}; human evidence/prose review still required')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('targets', nargs='+')
    args = parser.parse_args()
    for target in args.targets:
        inspect(target)


if __name__ == '__main__':
    main()
