# CH16 Phase B: user-reviewed finish

Running finish records the user's approval of the downloaded content. No independent reviewer is claimed.

Packet: ch16_cycle_b_f9a97a9d-20261013T234537Z-0096e2cf

Base: ece42448103dc647b3c4e8b7b0c06f545b719410

Response SHA-256: bfb0601205441429227b8b9af99a7ca2597995d275ea3046dd525c14d6317219

Candidate commit: a6c3b1f6ca9a8731d76c04d9f7462947e116a721

Model label: codex-local

## Source evidence
- BosonizeStubs/A07FiniteNormalOrdering.lean: 0add9f369175f79e96bda84c3ce4580aa4a32f22de7e9836d203246aa5d3be20

## verify-1.log
```text
[stub_lock] Verification PASSED: 835 statement(s) and 719 frozen command(s) verified.
[core_lock] Verified 25 complete Core source file(s).
ℹ [3404/3410] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Build completed successfully (3410 jobs).
'Bosonize.A07.normal_evaluation_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.normal_evaluation_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.normal_pair_contraction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.contraction_on_joint_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.chiral_gradient_representation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.dual_square_chiral_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
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
PASS: BosonizeStubs/A07FiniteNormalOrdering.lean, 23 freshly audited declarations

```

## Final ci.log
```text
make[1]: Entering directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch16-B-60af0b66'
./scripts/ci.sh
== Testing the statement-freeze guard ==
.....................................................................
----------------------------------------------------------------------
Ran 69 tests in 1.896s

OK
== Checking frozen chapter definitions and statements ==
[stub_lock] Verification PASSED: 835 statement(s) and 719 frozen command(s) verified.
== Checking complete frozen Core sources ==
[core_lock] Verified 25 complete Core source file(s).
== Building Bosonize (Core) ==
✔ [3384/3410] Built Bosonize.Core.Ch01LatticeBand (1.7s)
✔ [3385/3410] Built Bosonize.Core.Ch02UmbralCalculus (2.6s)
✔ [3386/3410] Built Bosonize.Core.A01FourierCharacters (3.0s)
✔ [3387/3410] Built Bosonize.Core.A02CARHilbert (4.0s)
✔ [3388/3410] Built Bosonize.Core.Ch03Fourier (5.8s)
✔ [3389/3410] Built Bosonize.Core.Ch04CARFock (5.4s)
✔ [3390/3410] Built Bosonize.Core.A03EnergyBudgets (11s)
✔ [3391/3410] Built Bosonize.Core.Ch05Fermions (7.8s)
✔ [3392/3410] Built Bosonize.Core.A04DensityKinematics (15s)
✔ [3393/3410] Built Bosonize.Core.Ch06LocalNet (15s)
✔ [3394/3410] Built Bosonize.Core.Ch08Boson (20s)
✔ [3395/3410] Built Bosonize.Core.Ch07VacuumBudget (20s)
✔ [3396/3410] Built Bosonize.Core.A05FiniteExponentials (3.9s)
✔ [3397/3410] Built Bosonize.Core.Ch06Ext (8.1s)
✔ [3398/3410] Built Bosonize.Core.A04PartitionCombinatorics (4.1s)
✔ [3399/3410] Built Bosonize.Core.Ch09DensityModes (6.2s)
✔ [3400/3410] Built Bosonize.Core.A04CurrentMargins (4.2s)
✔ [3401/3410] Built Bosonize.Core.Ch10Heisenberg (5.2s)
✔ [3402/3410] Built Bosonize.Core.Ch11HaldaneCompleteness (13s)
✔ [3403/3410] Built Bosonize.Core.Ch12Sugawara (6.9s)
✔ [3404/3410] Built Bosonize.Core.A05MultiSpecies (10s)
ℹ [3405/3410] Built Bosonize.Core.Ch13KleinFactors (6.5s)
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3406/3410] Built Bosonize.Core.Ch14Mandelstam (11s)
✔ [3407/3410] Built Bosonize.Core.A06ChiralFields (12s)
✔ [3408/3410] Built Bosonize.Core.Ch15DualFields (5.0s)
✔ [3409/3410] Built Bosonize (2.4s)
Build completed successfully (3410 jobs).
== Building BosonizeStubs (Staging) ==
ℹ [3403/3413] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3410/3413] Built BosonizeStubs.A07FiniteNormalOrdering (3.9s)
⚠ [3411/3413] Built BosonizeStubs.Ch16FieldHamiltonian (3.8s)
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
✔ [3412/3413] Built BosonizeStubs (3.4s)
Build completed successfully (3413 jobs).
== Testing the Web-LLM artifact/proof verifiers and axiom audit ==
.........[core_lock] Verified 25 complete Core source file(s).
[core_lock] Verified 25 complete Core source file(s).
......
----------------------------------------------------------------------
Ran 15 tests in 20.178s

OK
'Fixture.value' depends on axioms: [sorryAx]
PASS Markdown structure: /tmp/tmpk2yxwhtk/candidate.md; human evidence/prose review still required
CI OK
make[1]: Leaving directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch16-B-60af0b66'

```
