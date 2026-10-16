from pathlib import Path
import re
s=Path('.scratch/ch20_nonzero.lean').read_text()
p=Path('BosonizeStubs/Ch20CDW.lean').read_text()
start=s.index('lemma speciesEraseBridge')
stop=s.index('\nend Bosonize.Ch20',start)
x=s[start:stop]
# Retain the dependency closure, reuse existing canonical helper proofs.
remove=['target_one_admissible','inner_fsumX','inner_if_zeroX','inner_ifX','sum_single_pairX','erase_mn_not_mid_budget_local']
parts=re.split(r'(?m)^(?=(?:private )?(?:noncomputable )?(?:lemma|def) )',x)
kept=[]
for part in parts:
    m=re.match(r'(?:private )?(?:noncomputable )?(?:lemma|def) (\w+)',part)
    if m and m.group(1) in remove: continue
    if part.strip(): kept.append(part)
x=''.join(kept)
x=re.sub(r'(?m)^(?:private )?lemma ', 'have ',x)
x=re.sub(r'(?m)^private noncomputable def ', 'let ',x)
x=re.sub(r'(?m)^private def ', 'let ',x)
x=x.replace('Ch20ResidualScratch.residualDoubleExpansion','discardedResidualDoubleExpansion')
x=x.replace('erase_mn_not_mid_budget_local','targetZeroErased_not_mid_budget')
x=x.replace('simp only [Prod.mk.injEq, h01, false_and, false_or]','simp only [Prod.mk.injEq]')
x=x.replace('  have h01 : (0 : Fin 2) ≠ 1 := by decide\n','')
# A local let must be unfolded explicitly at the places where simp used a def.
x=x.replace('simp [residualOccupation', 'simp [residualOccupation')
pre='''  classical
  let mn := targetZeroMn
  let m0 := targetZeroM0
  let m1 : Ch01.Band 4 := ⟨1, by norm_num [Ch01.inBandPredicate]⟩
  let residualOccupation := targetZeroOccupation
  have ground_memX := ground_memCDWX (σ := Fin 2)
  have speciesBridge := targetZeroSpeciesBridge
  have leftSpecies_residualOccupation := targetZeroLeftSpeciesOccupation
  have leftSpecies_residual_excitation := targetZeroLeftSpeciesExcitation
'''
end='''  intro hz
  have hraw := congrArg Subtype.val hz
  change Ch14.projection 2 (cdwTarget Ch16.standardBranches witnessZero) 1
      ((cdwResidualOp 2 (fun _ => Ch06Ext.periodicTwist 4)
        Ch16.standardBranches 1 witnessZero 0)
       (A05.groundKet 2 witnessZero)) = 0 at hraw
  have hi := congrArg (fun y => inner ℂ (A02.ket (residualOccupation m1)) y) hraw
  simp at hi
  exact residual_m1_coefficient_nonzero hi
'''
body=pre+''.join('  '+l+'\n' if l else '\n' for l in x.splitlines())+end
Path('.scratch/nonzero_body.txt').write_text(body)
# Separate integration candidate until the baseline correction is reviewed.
idx=p.index('lemma concrete_discarded_channel_nonzero :')
a=p.index(':= by sorry',idx)
p=p[:a]+':= by\n'+body+p[a+len(':= by sorry'):]
Path('.scratch/ch20_integrated.lean').write_text(p)
