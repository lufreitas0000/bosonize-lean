#!/usr/bin/env python3
"""Check that every imported section is reachable from the actual book master."""
import argparse
import hashlib
import json
from pathlib import Path
import re


def inventory(root):
    root=root.resolve();pending=['main.tex'];seen={}
    while pending:
        name=pending.pop()
        path=(root/name).resolve()
        if not path.is_relative_to(root) or path.is_symlink(): raise ValueError('Input escapes book root')
        name=str(path.relative_to(root))
        if name in seen: continue
        data=path.read_bytes();seen[name]=hashlib.sha256(data).hexdigest()
        text=re.sub(r'(?<!\\)%[^\n]*','',data.decode())
        for target in re.findall(r'\\(?:input|include)\s*\{([^{}]+)\}',text):
            pending.append(target if target.endswith('.tex') else target+'.tex')
        for target in re.findall(r'\\InputIfFileExists\s*\{([^{}]+)\}',text):
            target=target if target.endswith('.tex') else target+'.tex'
            if (root/target).is_file(): pending.append(target)
    manifest=json.loads((root/'plan/imported_sections.json').read_text())
    numbers=[]
    for row in manifest['sections']:
        target=str(Path(row['target']).relative_to('notes/latex'))
        if target not in seen: raise ValueError('Imported section absent from book: '+target)
        if Path(target).stem != row['number']: raise ValueError('Section filename/number mismatch: '+target)
        text=(root/target).read_text()
        if len(re.findall(r'\\section\s*\{',text))!=1: raise ValueError('Expected one section in '+target)
        if '\\label{sec:'+row['id']+'}' not in text: raise ValueError('Missing original stable section label in '+target)
        if re.search(r'\\(?:documentclass|usepackage|begin\{document\})|BOSONIZE-BODY-',text):
            raise ValueError('Standalone wrapper leaked into '+target)
        numbers.append(row['number'])
    if len(set(numbers))!=len(numbers): raise ValueError('Duplicate section number')
    chapters=[]
    for row in manifest.get('chapter_replacements',[]):
        target=str(Path(row['target']).relative_to('notes/latex'))
        if target not in seen: raise ValueError('Chapter replacement absent from book: '+target)
        text=(root/target).read_text()
        if len(re.findall(r'\\chapter(?:\[[^]]*\])?\s*\{',text))!=1:
            raise ValueError('Expected one chapter in '+target)
        expected=row.get('label')
        if not expected or '\\label{'+expected+'}' not in text:
            raise ValueError('Missing stable chapter label in '+target)
        if re.search(r'\\(?:documentclass|usepackage|begin\{document\})',text):
            raise ValueError('Standalone wrapper leaked into '+target)
        predecessor=row.get('included_after')
        if predecessor:
            predecessor=str(Path(predecessor).relative_to('notes/latex'))
            main=(root/'main.tex').read_text()
            before=r'\\include\s*\{'+re.escape(Path(predecessor).with_suffix('').as_posix())+r'\}'
            current=r'\\include\s*\{'+re.escape(Path(target).with_suffix('').as_posix())+r'\}'
            left=re.search(before,main);right=re.search(current,main)
            if not left or not right or left.start()>=right.start():
                raise ValueError('Chapter is not included after its required predecessor: '+target)
        chapters.append(row['number'])
    if len(set(chapters))!=len(chapters): raise ValueError('Duplicate chapter replacement number')
    return dict(included_sections=numbers,included_chapters=chapters,book_sources_sha256=seen)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=Path('notes/latex'))
    parser.add_argument('--receipt',type=Path)
    args=parser.parse_args()
    result=inventory(args.root)
    if args.receipt:
        receipt=json.loads(args.receipt.read_text());receipt.update(result)
        args.receipt.write_text(json.dumps(receipt,indent=2)+'\n')
    print('PASS: master includes chapters '+', '.join(result['included_chapters'])+'; sections '+', '.join(result['included_sections']))
