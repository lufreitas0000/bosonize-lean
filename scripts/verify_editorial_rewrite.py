#!/usr/bin/env python3
"""Preserve existing mathematical blocks and non-owned sources during prose revision.
This is a mechanical preservation gate, not mathematical certification.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

def digest(data): return hashlib.sha256(data).hexdigest()
def protected(text):
    names=r'equation\*?|align\*?|alignat\*?|gather\*?|multline\*?|displaymath|theorem|lemma|proposition|corollary|definition|proof'
    pattern=r'\\begin\{('+names+r')\}.*?\\end\{\1\}|\\\[.*?\\\]|\$\$.*?\$\$'
    return [digest(m.group().encode()) for m in re.finditer(pattern,text,re.S)]
def references(text):
    return re.findall(r'\\(?:label|cite[a-zA-Z]*|input|include)\s*(?:\[[^\]]*\]\s*)*\{[^}]*\}',text)
def check(root,group):
    root=Path(root)
    baseline=json.loads((root/'docs/editorial/rewrite_wave1_preservation.json').read_text())
    jobs=json.loads((root/'docs/editorial/rewrite_wave1_jobs.json').read_text())['jobs']
    selected=[j for j in jobs if group=='all' or j['id']==group]
    if not selected: raise ValueError('Unknown revision group: '+group)
    owned={p for j in selected for p in j['targets']}
    for name,sha in baseline['read_only'].items():
        if name not in owned and digest((root/name).read_bytes())!=sha:
            raise ValueError('Non-owned source changed: '+name)
    for name in owned:
        text=(root/name).read_text()
        if not text.strip(): raise ValueError('Empty target: '+name)
        old=baseline['targets'][name]
        if Counter(old['protected'])-Counter(protected(text)):
            raise ValueError('Existing mathematical display/theorem/definition/proof block changed or removed: '+name)
        if Counter(old['references'])-Counter(references(text)):
            raise ValueError('Existing label/citation/input/include changed or removed: '+name)
    print('PASS: existing protected blocks/references retained; non-owned book/Lean/lock sources unchanged. Prose and new claims still require inspection.')
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--group',required=True)
    args=parser.parse_args()
    check(Path.cwd(),args.group)
