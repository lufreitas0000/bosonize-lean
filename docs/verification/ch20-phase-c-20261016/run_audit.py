"""Run after the exact promotion baseline is committed; preserve complete logs."""
import hashlib,json,os,subprocess,sys,tempfile
from pathlib import Path
repo=Path.cwd()
sys.path.insert(0,str(repo/'scripts/webllm'))
import verify_phase_b as vb
out=repo/'docs/verification/ch20-phase-c-20261016'
out.mkdir(parents=True,exist_ok=True)
subprocess.run(['make','ci'],check=True)
source=repo/'Bosonize/Core/Ch20CDW.lean'
code=source.read_text()
clean,mask=vb.phase_a.lean.strip_lean(code)
assert not any(t.kind=='id' and t.text.split('.')[-1].strip('«»') in {'sorry','sorryAx','admit','native_decide','axiom'} for t in vb.phase_a.lean.tokenize(clean,mask))
original=subprocess.check_output(['git','show','2c65de8:BosonizeStubs/Ch20CDW.lean'],text=True)
sets=[('all-declarations',code,vb.declarations(code)),('core-aggregator','import Bosonize\n',vb.declarations(original))]
for label,prefix,names in sets:
 with tempfile.TemporaryDirectory(prefix='ch20-promoted-audit-') as temp:
  candidate=Path(temp)/'Audit.lean'
  candidate.write_text(prefix+'\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
  p=subprocess.run(['lake','env','lean','-DwarningAsError=true','-DautoImplicit=false','-DrelaxedAutoImplicit=false',str(candidate)],text=True,capture_output=True)
  output=p.stdout+p.stderr
  (out/(label+'.log')).write_text(output)
  if p.returncode or 'warning:' in output: raise RuntimeError(label+' compile failed')
  vb.check_axiom_output(output,names)
  print('PASS',label,len(names),'freshly audited declarations',flush=True)
receipt={'audited_commit':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'full_source_audit':len(sets[0][2]),'core_aggregator_audit':len(sets[1][2]),'allowed_axioms':sorted(vb.phase_a.ALLOWED_AXIOMS),'core_files':34,'ci':'passed','sandbox':os.environ.get('LLM_SANDBOXED'),'proof_token_scan':'passed'}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
