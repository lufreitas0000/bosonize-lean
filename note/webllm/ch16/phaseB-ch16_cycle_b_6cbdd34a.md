# CH16 Phase B: user-reviewed finish

Running finish records the user's approval of the downloaded content. No independent reviewer is claimed.

Packet: ch16_cycle_b_6cbdd34a-20261013T235148Z-0ec0598e

Base: 1cc39c66205be2878873d5c849c15032efef0642

Response SHA-256: c74e6656716419fd8f261e167b0368df77a07575aa6e4e3c14ec24ca4183c9ee

Candidate commit: 6adef634122f53f74d58e7c806427186f8af5a55

Model label: codex-local

## Source evidence
- BosonizeStubs/Ch16FieldHamiltonian.lean: 42d8e962071d62d74b444951e37e9e5998e59e92183383260f5024193585fe71

## verify-1.log
```text
[stub_lock] Verification PASSED: 835 statement(s) and 719 frozen command(s) verified.
[core_lock] Verified 25 complete Core source file(s).
ℹ [3403/3410] Replayed Bosonize.Core.Ch13KleinFactors
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
'Bosonize.Ch16.field_chiral_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.chiral_spatial_collapse_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.field_weighted_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.field_weighted_after_excursion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.error_weighted_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.ground_error_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.excited_ket_mem_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.excited_ket_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.single_mode_error_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.first_mode_error_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.error_nonzero_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.concrete_dispersion_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.concrete_excited_error_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
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
PASS: BosonizeStubs/Ch16FieldHamiltonian.lean, 25 freshly audited declarations

```

## Final ci.log
```text
make[1]: Entering directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch16-B-660d040c'
./scripts/ci.sh
== Testing the statement-freeze guard ==
.....................................................................
----------------------------------------------------------------------
Ran 69 tests in 1.811s

OK
== Checking frozen chapter definitions and statements ==
[stub_lock] Verification PASSED: 835 statement(s) and 719 frozen command(s) verified.
== Checking complete frozen Core sources ==
[core_lock] Verified 25 complete Core source file(s).
== Building Bosonize (Core) ==
✔ [3384/3410] Built Bosonize.Core.Ch01LatticeBand (1.7s)
✔ [3385/3410] Built Bosonize.Core.Ch02UmbralCalculus (3.1s)
✔ [3386/3410] Built Bosonize.Core.A01FourierCharacters (3.4s)
✔ [3387/3410] Built Bosonize.Core.A02CARHilbert (4.3s)
✔ [3388/3410] Built Bosonize.Core.Ch03Fourier (5.8s)
✔ [3389/3410] Built Bosonize.Core.Ch04CARFock (5.8s)
✔ [3390/3410] Built Bosonize.Core.A03EnergyBudgets (10s)
✔ [3391/3410] Built Bosonize.Core.Ch05Fermions (6.7s)
✔ [3392/3410] Built Bosonize.Core.A04DensityKinematics (11s)
✔ [3393/3410] Built Bosonize.Core.Ch06LocalNet (11s)
✔ [3394/3410] Built Bosonize.Core.Ch08Boson (15s)
✔ [3395/3410] Built Bosonize.Core.Ch07VacuumBudget (14s)
✔ [3396/3410] Built Bosonize.Core.A05FiniteExponentials (3.4s)
✔ [3397/3410] Built Bosonize.Core.A04PartitionCombinatorics (3.8s)
✔ [3398/3410] Built Bosonize.Core.Ch06Ext (6.0s)
✔ [3399/3410] Built Bosonize.Core.Ch09DensityModes (5.7s)
✔ [3400/3410] Built Bosonize.Core.A04CurrentMargins (4.1s)
✔ [3401/3410] Built Bosonize.Core.Ch10Heisenberg (5.7s)
✔ [3402/3410] Built Bosonize.Core.Ch11HaldaneCompleteness (13s)
✔ [3403/3410] Built Bosonize.Core.Ch12Sugawara (5.0s)
✔ [3404/3410] Built Bosonize.Core.A05MultiSpecies (9.8s)
ℹ [3405/3410] Built Bosonize.Core.Ch13KleinFactors (6.6s)
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3406/3410] Built Bosonize.Core.Ch14Mandelstam (11s)
✔ [3407/3410] Built Bosonize.Core.A06ChiralFields (12s)
✔ [3408/3410] Built Bosonize.Core.Ch15DualFields (4.6s)
✔ [3409/3410] Built Bosonize (3.3s)
Build completed successfully (3410 jobs).
== Building BosonizeStubs (Staging) ==
ℹ [3403/3413] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3410/3413] Built BosonizeStubs.A07FiniteNormalOrdering (3.6s)
✔ [3411/3413] Built BosonizeStubs.Ch16FieldHamiltonian (9.6s)
✔ [3412/3413] Built BosonizeStubs (3.2s)
Build completed successfully (3413 jobs).
== Testing the Web-LLM artifact/proof verifiers and axiom audit ==
.........[core_lock] Verified 25 complete Core source file(s).
[core_lock] Verified 25 complete Core source file(s).
......
----------------------------------------------------------------------
Ran 15 tests in 21.074s

OK
'Fixture.value' depends on axioms: [sorryAx]
PASS Markdown structure: /tmp/tmpapwnsbog/candidate.md; human evidence/prose review still required
CI OK
make[1]: Leaving directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch16-B-660d040c'

```
