from pathlib import Path
import json,re,sys
from collections import Counter
import verify_editorial_rewrite as guard
jobs=json.loads(Path('docs/editorial/rewrite_wave1_jobs.json').read_text())['jobs']
locks=json.loads(Path('docs/editorial/reconciliation_inline_lock.json').read_text())
base=json.loads(Path('docs/editorial/rewrite_wave1_preservation.json').read_text())
selected=[j for j in jobs if sys.argv[1]=='all' or j['id']==sys.argv[1]]
assert selected
for job in selected:
 for name in job['targets']:
  text=Path(name).read_text()
  now=re.findall(r'(?<![\\$])\$(?!\$).*?(?<!\\)\$(?!\$)|\\\(.*?\\\)',text,re.S)
  assert now==locks[name], 'Existing inline math changed/added/removed: '+name
  assert guard.protected(text)==base['targets'][name]['protected'], 'Protected math order/content changed: '+name
  assert guard.references(text)==base['targets'][name]['references'], 'Labels/citations/include graph changed: '+name
print('PASS exact current inline/display/proof math and labels/citations/include graph')
