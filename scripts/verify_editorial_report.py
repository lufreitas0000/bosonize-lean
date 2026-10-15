#!/usr/bin/env python3
"""Mechanical validation of a review artifact; never certifies its judgments."""
import hashlib
import json
from pathlib import Path
import re


def check(root):
    root=Path(root)
    report=(root/'docs/editorial/first_review.md').read_text()
    if len(report.split())>6500: raise ValueError('Review exceeds bounded report size')
    headings=['Executive assessment','Prioritized findings','Notation ledger','Chapter connections','Tone examples','Revision queue','Coverage and limits']
    found=re.findall(r'^## (.+)$',report,re.M)
    if found!=headings: raise ValueError('Use the seven required report headings in order')
    ids=re.findall(r'^### (ED-\d+):',report,re.M)
    if not 12<=len(ids)<=30 or len(set(ids))!=len(ids): raise ValueError('Expected 12–30 unique findings')
    inventory=json.loads((root/'docs/editorial/source_inventory.json').read_text())
    for name,sha in inventory['read_only_sources'].items():
        if hashlib.sha256((root/name).read_bytes()).hexdigest()!=sha: raise ValueError('Read-only source changed: '+name)
    findings=report.split('## Prioritized findings\n',1)[1].split('## Notation ledger\n',1)[0]
    blocks=re.split(r'^### ED-\d+:',findings,flags=re.M)[1:]
    for block in blocks:
        sources=re.findall(r'^Source: `?([^`\s:]+):(\d+)(?:-(\d+))?`?\s*$',block,re.M)
        if not sources: raise ValueError('A finding has no source anchor')
        for name,start,end in sources:
            if name not in inventory['read_only_sources']: raise ValueError('Source outside reviewed inventory: '+name)
            lines=(root/name).read_text().splitlines();start=int(start);end=int(end or start)
            if not 1<=start<=end<=len(lines): raise ValueError('Invalid source line range: '+name)
        if not re.search(r'\bP[123]\b',block): raise ValueError('Finding needs a priority')
    coverage=report.split('## Coverage and limits\n',1)[1]
    for chapter in [*range(1,12),19,20,21]:
        if not re.search(r'\|\s*CH'+f'{chapter:02}'+r'\s*\|',coverage): raise ValueError(f'Missing coverage row CH{chapter:02}')
    print('PASS: report structure, anchors and unchanged sources; editorial judgments require inspection')


if __name__=='__main__': check(Path.cwd())
