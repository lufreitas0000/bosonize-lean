# CH15 Phase B: user-reviewed finish

Running finish records the user's approval of the downloaded content. No independent reviewer is claimed.

Packet: ch15_cycle_b_ea374fc9-20261013T184306Z-a29ee8ce

Base: 23958251d2d20c4fb5148f8b9ffcba7ca8a82b2b

Response SHA-256: 2676d3c2b02d75c30a87648efa6f29dbbb5ca11d1b21373b26548a5b5dcfa4a9

Candidate commit: 6cba91cd580abc52d44c714663df5509ad6f354e

Model label: codex-local

## Source evidence
- BosonizeStubs/Ch15DualFields.lean: e6863de5211ac488eaf35b3b1afec0168192d5dce585c04c9350fc15a006edf5

## verify-1.log
```text
[stub_lock] Verification PASSED: 816 statement(s) and 657 frozen command(s) verified.
[core_lock] Verified 23 complete Core source file(s).
ℹ [3403/3408] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Build completed successfully (3408 jobs).
'Bosonize.A06.lattice_character_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.lattice_character_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.integer_lift_periodic' depends on axioms: [propext, Quot.sound]
'Bosonize.A06.forward_diff_add' depends on axioms: [propext, Quot.sound]
'Bosonize.A06.forward_diff_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.forward_diff_sum_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.chiral_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.chiral_forward_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.joint_signed_current_commutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.chiral_cross_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.chiral_same_commutator_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.dirichlet_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.dirichlet_spatial_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.skew_kernel_diff_sum_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.admissible_ground_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.concrete_two_branch_parameters' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.Orientation' does not depend on any axioms
'Bosonize.A06.orientationSign' does not depend on any axioms
'Bosonize.A06.Branches' does not depend on any axioms
'Bosonize.A06.speciesOf' does not depend on any axioms
'Bosonize.A06.marginAt' depends on axioms: [propext]
'Bosonize.A06.branchMargins' depends on axioms: [propext]
'Bosonize.A06.latticeCharacter' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.skewKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.dirichletKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.opForwardDiff' depends on axioms: [propext, Quot.sound]
'Bosonize.A06.integerLift' depends on axioms: [propext, Quot.sound]
'Bosonize.A06.chiralField' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.chiralDifferenceExpansion' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS: BosonizeStubs/A06ChiralFields.lean, 29 freshly audited declarations
'Bosonize.Ch15.phi_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.theta_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.phi_self_commutator_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.theta_self_commutator_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.mixed_commutator_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.mixed_forward_diff_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.zero_mode_obstruction_on_ground' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.phiField' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.thetaField' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS: BosonizeStubs/Ch15DualFields.lean, 9 freshly audited declarations

```

## Final ci.log
```text
make[1]: Entering directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch15-B-8d827fc4'
./scripts/ci.sh
== Testing the statement-freeze guard ==
.....................................................................
----------------------------------------------------------------------
Ran 69 tests in 2.088s

OK
== Checking frozen chapter definitions and statements ==
[stub_lock] Verification PASSED: 816 statement(s) and 657 frozen command(s) verified.
== Checking complete frozen Core sources ==
[core_lock] Verified 23 complete Core source file(s).
== Building Bosonize (Core) ==
✔ [3384/3408] Built Bosonize.Core.Ch01LatticeBand (1.6s)
✔ [3385/3408] Built Bosonize.Core.Ch02UmbralCalculus (2.9s)
✔ [3386/3408] Built Bosonize.Core.A01FourierCharacters (3.2s)
✔ [3387/3408] Built Bosonize.Core.A02CARHilbert (3.0s)
✔ [3388/3408] Built Bosonize.Core.Ch03Fourier (7.1s)
✔ [3389/3408] Built Bosonize.Core.Ch04CARFock (7.0s)
✔ [3390/3408] Built Bosonize.Core.A03EnergyBudgets (12s)
✔ [3391/3408] Built Bosonize.Core.Ch05Fermions (6.8s)
✔ [3392/3408] Built Bosonize.Core.A04DensityKinematics (11s)
✔ [3393/3408] Built Bosonize.Core.Ch06LocalNet (13s)
✔ [3394/3408] Built Bosonize.Core.Ch08Boson (17s)
✔ [3395/3408] Built Bosonize.Core.Ch07VacuumBudget (18s)
✔ [3396/3408] Built Bosonize.Core.A05FiniteExponentials (3.8s)
✔ [3397/3408] Built Bosonize.Core.Ch06Ext (8.3s)
✔ [3398/3408] Built Bosonize.Core.A04PartitionCombinatorics (3.6s)
✔ [3399/3408] Built Bosonize.Core.Ch09DensityModes (5.4s)
✔ [3400/3408] Built Bosonize.Core.A04CurrentMargins (3.4s)
✔ [3401/3408] Built Bosonize.Core.Ch10Heisenberg (5.7s)
✔ [3402/3408] Built Bosonize.Core.Ch11HaldaneCompleteness (14s)
✔ [3403/3408] Built Bosonize.Core.Ch12Sugawara (7.1s)
✔ [3404/3408] Built Bosonize.Core.A05MultiSpecies (10s)
ℹ [3405/3408] Built Bosonize.Core.Ch13KleinFactors (6.0s)
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3406/3408] Built Bosonize.Core.Ch14Mandelstam (13s)
✔ [3407/3408] Built Bosonize (2.5s)
Build completed successfully (3408 jobs).
== Building BosonizeStubs (Staging) ==
ℹ [3403/3411] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3408/3411] Built BosonizeStubs.A06ChiralFields (11s)
✔ [3409/3411] Built BosonizeStubs.Ch15DualFields (3.7s)
✔ [3410/3411] Built BosonizeStubs (2.3s)
Build completed successfully (3411 jobs).
== Testing the Web-LLM artifact/proof verifiers and axiom audit ==
........[core_lock] Verified 23 complete Core source file(s).
[core_lock] Verified 23 complete Core source file(s).
......
----------------------------------------------------------------------
Ran 14 tests in 15.073s

OK
'Fixture.value' depends on axioms: [sorryAx]
PASS Markdown structure: /tmp/tmple8yt6nl/candidate.md; human evidence/prose review still required
CI OK
make[1]: Leaving directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch15-B-8d827fc4'

```
