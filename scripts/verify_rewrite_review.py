#!/usr/bin/env python3
"""Check report structure and source coverage only, not its editorial judgments."""
import json
import re
import sys
from pathlib import Path
p=Path(sys.argv[1]);text=p.read_text()
assert text.startswith('# Independent rewrite review\n')
assert ('Verdict: PASS' in text) != ('Verdict: REVISE' in text)
for h in ['Coverage','Required corrections','Existing issues outside this wave','Strengths and checks']:
    assert '\n## '+h+'\n' in text, 'Missing report heading: '+h
assert 100 <= len(text.split()) <= 3000
chapters={'foundations':[f'CH{n:02}' for n in range(1,6)],'currents':[f'CH{n:02}' for n in range(6,12)],'interactions':['CH19','CH20','CH21','Frontmatter']}[p.stem]
coverage=text.split('## Coverage\n',1)[1].split('## Required corrections\n',1)[0]
for chapter in chapters:
    assert re.search(r'\|\s*'+re.escape(chapter)+r'\s*\|',coverage), 'Missing chapter coverage row: '+chapter
jobs=json.loads(Path('docs/editorial/rewrite_wave1_jobs.json').read_text())['jobs']
expected={n for j in jobs if j['chapter'] in chapters for n in j['targets']}
anchors=re.findall(r'(notes/latex/[^\s`|:]+\.tex):(\d+)',coverage)
assert expected <= {n for n,_ in anchors}, 'Missing per-file source anchors: '+str(expected-{n for n,_ in anchors})
for name,line in anchors:
    assert name in expected, 'Unexpected coverage source: '+name
    assert 1 <= int(line) <= len(Path(name).read_text().splitlines()), 'Invalid source line: '+name+':'+line
required=text.split('## Required corrections\n',1)[1].split('## Existing issues outside this wave\n',1)[0]
if 'Verdict: PASS' in text: assert not re.search(r'\bP[12]\b',required), 'PASS conflicts with required corrections'
else: assert re.search(r'\bP[12]\b',required), 'REVISE needs prioritized required corrections'
print('PASS report structure, chapter/file coverage and source ranges only; findings require coordinator inspection')
