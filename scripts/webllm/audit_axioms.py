#!/usr/bin/env python3
"""Freshly build selected modules and audit data, or all declarations, through imports."""
import argparse
import re
import subprocess
import tempfile
from pathlib import Path

import verify_phase_a as phase_a
import verify_phase_b as phase_b


def audit(repo, targets, data_only=False):
    names, modules = [], []
    for name in targets:
        if not re.fullmatch(r'(?:Bosonize/Core|BosonizeStubs)/[A-Za-z0-9_/]+\.lean', name):
            raise ValueError(f'Expected a Core/staging source: {name}')
        source = repo / name
        if source.is_symlink() or not source.is_file():
            raise ValueError(f'Missing/unsafe source: {name}')
        code = source.read_text()
        if data_only:
            model = phase_a.lean.parse_lean(code)
            names.extend(c.label.split(' ', 1)[1] for c in model.commands if c.kind in
                         {'def', 'abbrev', 'instance', 'structure', 'inductive', 'class'})
        else:
            names.extend(phase_b.declarations(code))
        modules.append(name.removesuffix('.lean').replace('/', '.'))
    if not names:
        raise ValueError('No named declarations to audit')
    subprocess.run(['python3', 'scripts/guards/core_lock.py'], cwd=repo, check=True)
    subprocess.run(['lake', 'build', *modules], cwd=repo, check=True)
    with tempfile.TemporaryDirectory(prefix='bosonize-axioms-') as directory:
        candidate = Path(directory) / 'Audit.lean'
        candidate.write_text('\n'.join(f'import {module}' for module in modules) + '\n' +
                             '\n'.join(f'#print axioms {name}' for name in dict.fromkeys(names)) + '\n')
        result = subprocess.run(['lake', 'env', 'lean', '-DautoImplicit=false', '-DwarningAsError=true', str(candidate)],
                                cwd=repo, text=True, capture_output=True)
        output = result.stdout + result.stderr
        print(output, end='')
        if result.returncode or 'warning:' in output:
            raise ValueError('Imported axiom audit failed')
        for name in names:
            match = re.search(r"'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", output)
            if not match and f"'{name}' does not depend on any axioms" not in output:
                raise ValueError(f'Missing axiom output: {name}')
            axioms = {x.strip() for x in match[1].split(',') if x.strip()} if match else set()
            if axioms - phase_a.ALLOWED_AXIOMS:
                raise ValueError(f'Nonstandard axioms: {name}: {sorted(axioms)}')
    print(f'PASS: {len(set(names))} freshly built ' + ('data' if data_only else 'data/theorem') + ' declarations')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data-only', action='store_true')
    parser.add_argument('targets', nargs='+')
    args = parser.parse_args()
    audit(phase_a.REPO, args.targets, args.data_only)


if __name__ == '__main__':
    main()
