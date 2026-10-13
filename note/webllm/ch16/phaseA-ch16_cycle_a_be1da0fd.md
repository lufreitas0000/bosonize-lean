# CH16 Phase A: user-reviewed finish

Running finish records the user's approval of the downloaded content. No independent reviewer is claimed.

Packet: ch16_cycle_a_be1da0fd-20261013T193345Z-76069531

Base: 5cbe38a43338f0ae62bedf258a701674d203f05b

Response SHA-256: 66f93ac5c9678e25716b8b2eaec760cead8eb0838adb16508bc3641d5dade83d

Candidate commit: 7d78e90213c0ff7b5e341bd9b1e3d1d5f0a50f2f

Model label: codex-local

## Source evidence
- BosonizeStubs/A07FiniteNormalOrdering.lean: 8440173c7b70684c3547cb4e311b15358f07ab27de2adc7d51fe3013be38932f
- BosonizeStubs/Ch16FieldHamiltonian.lean: 5b573e80c0a4588828a6d2e00c884bd73f6f369a8ce4267ad401873e3d3bc66b

## verify-1.log
```text
[core_lock] Verified 25 complete Core source file(s).
/tmp/bosonize-phase-a-vt_v7cvu/Candidate.lean:80:6: warning: declaration uses `sorry`
/tmp/bosonize-phase-a-vt_v7cvu/Candidate.lean:85:6: warning: declaration uses `sorry`
/tmp/bosonize-phase-a-vt_v7cvu/Candidate.lean:90:6: warning: declaration uses `sorry`
/tmp/bosonize-phase-a-vt_v7cvu/Candidate.lean:97:6: warning: declaration uses `sorry`
/tmp/bosonize-phase-a-vt_v7cvu/Candidate.lean:107:6: warning: declaration uses `sorry`
/tmp/bosonize-phase-a-vt_v7cvu/Candidate.lean:115:6: warning: declaration uses `sorry`
/tmp/bosonize-phase-a-vt_v7cvu/Candidate.lean:205:6: warning: declaration uses `sorry`
/tmp/bosonize-phase-a-vt_v7cvu/Candidate.lean:211:6: warning: declaration uses `sorry`
/tmp/bosonize-phase-a-vt_v7cvu/Candidate.lean:225:8: warning: declaration uses `sorry`
/tmp/bosonize-phase-a-vt_v7cvu/Candidate.lean:234:8: warning: declaration uses `sorry`
/tmp/bosonize-phase-a-vt_v7cvu/Candidate.lean:245:6: warning: declaration uses `sorry`
/tmp/bosonize-phase-a-vt_v7cvu/Candidate.lean:254:6: warning: declaration uses `sorry`
/tmp/bosonize-phase-a-vt_v7cvu/Candidate.lean:262:6: warning: declaration uses `sorry`
/tmp/bosonize-phase-a-vt_v7cvu/Candidate.lean:267:6: warning: declaration uses `sorry`
/tmp/bosonize-phase-a-vt_v7cvu/Candidate.lean:274:8: warning: declaration uses `sorry`
/tmp/bosonize-phase-a-vt_v7cvu/Candidate.lean:285:8: warning: declaration uses `sorry`
/tmp/bosonize-phase-a-vt_v7cvu/Candidate.lean:294:8: warning: declaration uses `sorry`
/tmp/bosonize-phase-a-vt_v7cvu/Candidate.lean:305:8: warning: declaration uses `sorry`
/tmp/bosonize-phase-a-vt_v7cvu/Candidate.lean:309:8: warning: declaration uses `sorry`
'Bosonize.A07.Letter' does not depend on any axioms
'Bosonize.A07.QuadraticSymbol' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.orientation' does not depend on any axioms
'Bosonize.A07.natMode' does not depend on any axioms
'Bosonize.A07.phaseSign' does not depend on any axioms
'Bosonize.A07.signedMode' does not depend on any axioms
'Bosonize.A07.current' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.rawPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.normalPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.rawEvaluation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.normalEvaluation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.squareSymbol' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.gradientCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.chiralCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.phiCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.thetaCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.dualSquareSymbol' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.marginWithExcursion' depends on axioms: [propext]
'Bosonize.Ch16.chiralSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.localFieldEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.fieldHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.epsilon' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.referenceWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.sugawara' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.weightedEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.weightedError' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.errorOperator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.excitedKet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.standardBranches' depends on axioms: [propext]
Phase A artifact ELABORATED: 29 audited data declarations; 19 unproved theorem stubs.
Not proved, not independently reviewed, not staged, and not locked. Local mathematical review is next.

```

## axioms.log
```text
make[1]: Entering directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch16-A-cf3303b1'
[core_lock] Verified 25 complete Core source file(s).
ℹ [3403/3411] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [3410/3411] Replayed BosonizeStubs.A07FiniteNormalOrdering
warning: BosonizeStubs/A07FiniteNormalOrdering.lean:79:6: declaration uses `sorry`
warning: BosonizeStubs/A07FiniteNormalOrdering.lean:84:6: declaration uses `sorry`
warning: BosonizeStubs/A07FiniteNormalOrdering.lean:89:6: declaration uses `sorry`
warning: BosonizeStubs/A07FiniteNormalOrdering.lean:96:6: declaration uses `sorry`
warning: BosonizeStubs/A07FiniteNormalOrdering.lean:106:6: declaration uses `sorry`
warning: BosonizeStubs/A07FiniteNormalOrdering.lean:114:6: declaration uses `sorry`
⚠ [3411/3411] Replayed BosonizeStubs.Ch16FieldHamiltonian
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:84:6: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:90:6: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:104:8: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:113:8: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:124:6: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:133:6: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:141:6: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:146:6: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:153:8: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:164:8: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:173:8: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:184:8: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:188:8: declaration uses `sorry`
Build completed successfully (3411 jobs).
'Bosonize.A07.Letter' does not depend on any axioms
'Bosonize.A07.QuadraticSymbol' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.orientation' does not depend on any axioms
'Bosonize.A07.natMode' does not depend on any axioms
'Bosonize.A07.phaseSign' does not depend on any axioms
'Bosonize.A07.signedMode' does not depend on any axioms
'Bosonize.A07.current' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.rawPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.normalPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.rawEvaluation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.normalEvaluation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.squareSymbol' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.gradientCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.chiralCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.phiCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.thetaCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.dualSquareSymbol' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.marginWithExcursion' depends on axioms: [propext]
'Bosonize.Ch16.chiralSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.localFieldEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.fieldHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.epsilon' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.referenceWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.sugawara' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.weightedEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.weightedError' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.errorOperator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.excitedKet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.standardBranches' depends on axioms: [propext]
PASS: 29 freshly built data declarations
make[1]: Leaving directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch16-A-cf3303b1'

```

## build.log
```text
make[1]: Entering directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch16-A-cf3303b1'
lake build BosonizeStubs
✔ [3384/3413] Built Bosonize.Core.Ch01LatticeBand (1.6s)
✔ [3385/3413] Built Bosonize.Core.Ch02UmbralCalculus (2.6s)
✔ [3386/3413] Built Bosonize.Core.A01FourierCharacters (2.9s)
✔ [3387/3413] Built Bosonize.Core.A02CARHilbert (3.7s)
✔ [3388/3413] Built Bosonize.Core.Ch03Fourier (5.5s)
✔ [3389/3413] Built Bosonize.Core.Ch04CARFock (5.3s)
✔ [3390/3413] Built Bosonize.Core.A03EnergyBudgets (10s)
✔ [3391/3413] Built Bosonize.Core.Ch05Fermions (6.6s)
✔ [3392/3413] Built Bosonize.Core.A04DensityKinematics (10s)
✔ [3393/3413] Built Bosonize.Core.Ch06LocalNet (11s)
✔ [3394/3413] Built Bosonize.Core.Ch08Boson (14s)
✔ [3395/3413] Built Bosonize.Core.Ch07VacuumBudget (14s)
✔ [3396/3413] Built Bosonize.Core.A05FiniteExponentials (3.1s)
✔ [3397/3413] Built Bosonize.Core.A04PartitionCombinatorics (3.6s)
✔ [3398/3413] Built Bosonize.Core.Ch06Ext (6.7s)
✔ [3399/3413] Built Bosonize.Core.Ch09DensityModes (5.3s)
✔ [3400/3413] Built Bosonize.Core.A04CurrentMargins (3.6s)
✔ [3401/3413] Built Bosonize.Core.Ch10Heisenberg (4.4s)
✔ [3402/3413] Built Bosonize.Core.Ch11HaldaneCompleteness (11s)
✔ [3403/3413] Built Bosonize.Core.Ch12Sugawara (6.1s)
✔ [3404/3413] Built Bosonize.Core.A05MultiSpecies (9.2s)
ℹ [3405/3413] Built Bosonize.Core.Ch13KleinFactors (5.7s)
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3406/3413] Built Bosonize.Core.Ch14Mandelstam (9.7s)
✔ [3407/3413] Built Bosonize.Core.A06ChiralFields (10s)
✔ [3408/3413] Built Bosonize.Core.Ch15DualFields (3.9s)
✔ [3409/3413] Built Bosonize (2.1s)
⚠ [3410/3413] Built BosonizeStubs.A07FiniteNormalOrdering (2.8s)
warning: BosonizeStubs/A07FiniteNormalOrdering.lean:79:6: declaration uses `sorry`
warning: BosonizeStubs/A07FiniteNormalOrdering.lean:84:6: declaration uses `sorry`
warning: BosonizeStubs/A07FiniteNormalOrdering.lean:89:6: declaration uses `sorry`
warning: BosonizeStubs/A07FiniteNormalOrdering.lean:96:6: declaration uses `sorry`
warning: BosonizeStubs/A07FiniteNormalOrdering.lean:106:6: declaration uses `sorry`
warning: BosonizeStubs/A07FiniteNormalOrdering.lean:114:6: declaration uses `sorry`
⚠ [3411/3413] Built BosonizeStubs.Ch16FieldHamiltonian (3.1s)
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:84:6: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:90:6: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:104:8: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:113:8: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:124:6: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:133:6: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:141:6: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:146:6: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:153:8: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:164:8: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:173:8: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:184:8: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:188:8: declaration uses `sorry`
✔ [3412/3413] Built BosonizeStubs (2.7s)
Build completed successfully (3413 jobs).
make[1]: Leaving directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch16-A-cf3303b1'

```

## Final ci.log
```text
make[1]: Entering directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch16-A-cf3303b1'
./scripts/ci.sh
== Testing the statement-freeze guard ==
.....................................................................
----------------------------------------------------------------------
Ran 69 tests in 1.721s

OK
== Checking frozen chapter definitions and statements ==
[stub_lock] Verification PASSED: 835 statement(s) and 719 frozen command(s) verified.
== Checking complete frozen Core sources ==
[core_lock] Verified 25 complete Core source file(s).
== Building Bosonize (Core) ==
ℹ [3403/3410] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Build completed successfully (3410 jobs).
== Building BosonizeStubs (Staging) ==
ℹ [3403/3413] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [3410/3413] Replayed BosonizeStubs.A07FiniteNormalOrdering
warning: BosonizeStubs/A07FiniteNormalOrdering.lean:79:6: declaration uses `sorry`
warning: BosonizeStubs/A07FiniteNormalOrdering.lean:84:6: declaration uses `sorry`
warning: BosonizeStubs/A07FiniteNormalOrdering.lean:89:6: declaration uses `sorry`
warning: BosonizeStubs/A07FiniteNormalOrdering.lean:96:6: declaration uses `sorry`
warning: BosonizeStubs/A07FiniteNormalOrdering.lean:106:6: declaration uses `sorry`
warning: BosonizeStubs/A07FiniteNormalOrdering.lean:114:6: declaration uses `sorry`
⚠ [3411/3413] Replayed BosonizeStubs.Ch16FieldHamiltonian
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:84:6: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:90:6: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:104:8: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:113:8: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:124:6: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:133:6: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:141:6: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:146:6: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:153:8: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:164:8: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:173:8: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:184:8: declaration uses `sorry`
warning: BosonizeStubs/Ch16FieldHamiltonian.lean:188:8: declaration uses `sorry`
Build completed successfully (3413 jobs).
== Testing the Web-LLM artifact/proof verifiers and axiom audit ==
.........[core_lock] Verified 25 complete Core source file(s).
[core_lock] Verified 25 complete Core source file(s).
......
----------------------------------------------------------------------
Ran 15 tests in 17.682s

OK
'Fixture.value' depends on axioms: [sorryAx]
PASS Markdown structure: /tmp/tmp790u4i1h/candidate.md; human evidence/prose review still required
CI OK
make[1]: Leaving directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch16-A-cf3303b1'

```
