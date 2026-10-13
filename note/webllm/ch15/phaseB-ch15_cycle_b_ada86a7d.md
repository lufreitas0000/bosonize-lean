# CH15 Phase B: user-reviewed finish

Running finish records the user's approval of the downloaded content. No independent reviewer is claimed.

Packet: ch15_cycle_b_ada86a7d-20261013T150950Z-73e31510

Base: cbee7697a3d0866c18bb89f466967e4ff089205e

Response SHA-256: adfc8a187eb5019e9c2b553562388ac23f4ef3c8d224b40d5af718bf94981393

Candidate commit: b2030868a8b64a305bda64e9bfb410b0d4ae38b7

Model label: codex-local

## Source evidence
- BosonizeStubs/A06ChiralFields.lean: daffa052dbd46a919a001b086804af1cb8b2182c5322a20d4f8581c4a131d603

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

```

## Final ci.log
```text
make[1]: Entering directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch15-B-1fe960d8'
./scripts/ci.sh
== Testing the statement-freeze guard ==
.....................................................................
----------------------------------------------------------------------
Ran 69 tests in 1.946s

OK
== Checking frozen chapter definitions and statements ==
[stub_lock] Verification PASSED: 816 statement(s) and 657 frozen command(s) verified.
== Checking complete frozen Core sources ==
[core_lock] Verified 23 complete Core source file(s).
== Building Bosonize (Core) ==
✔ [3384/3408] Built Bosonize.Core.Ch01LatticeBand (1.9s)
✔ [3385/3408] Built Bosonize.Core.Ch02UmbralCalculus (2.6s)
✔ [3386/3408] Built Bosonize.Core.A01FourierCharacters (3.3s)
✔ [3387/3408] Built Bosonize.Core.A02CARHilbert (4.4s)
✔ [3388/3408] Built Bosonize.Core.Ch04CARFock (5.8s)
✔ [3389/3408] Built Bosonize.Core.Ch03Fourier (6.1s)
✔ [3390/3408] Built Bosonize.Core.A03EnergyBudgets (11s)
✔ [3391/3408] Built Bosonize.Core.Ch05Fermions (7.2s)
✔ [3392/3408] Built Bosonize.Core.A04DensityKinematics (12s)
✔ [3393/3408] Built Bosonize.Core.Ch06LocalNet (13s)
✔ [3394/3408] Built Bosonize.Core.Ch08Boson (17s)
✔ [3395/3408] Built Bosonize.Core.Ch07VacuumBudget (17s)
✔ [3396/3408] Built Bosonize.Core.A05FiniteExponentials (3.9s)
✔ [3397/3408] Built Bosonize.Core.Ch06Ext (7.8s)
✔ [3398/3408] Built Bosonize.Core.A04PartitionCombinatorics (3.0s)
✔ [3399/3408] Built Bosonize.Core.Ch09DensityModes (6.1s)
✔ [3400/3408] Built Bosonize.Core.A04CurrentMargins (4.6s)
✔ [3401/3408] Built Bosonize.Core.Ch10Heisenberg (5.4s)
✔ [3402/3408] Built Bosonize.Core.Ch11HaldaneCompleteness (13s)
✔ [3403/3408] Built Bosonize.Core.Ch12Sugawara (7.7s)
✔ [3404/3408] Built Bosonize.Core.A05MultiSpecies (11s)
ℹ [3405/3408] Built Bosonize.Core.Ch13KleinFactors (7.2s)
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3406/3408] Built Bosonize.Core.Ch14Mandelstam (11s)
✔ [3407/3408] Built Bosonize (2.4s)
Build completed successfully (3408 jobs).
== Building BosonizeStubs (Staging) ==
ℹ [3402/3404] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3408/3411] Built BosonizeStubs.A06ChiralFields (12s)
⚠ [3409/3411] Built BosonizeStubs.Ch15DualFields (4.2s)
warning: BosonizeStubs/Ch15DualFields.lean:19:6: declaration uses `sorry`
warning: BosonizeStubs/Ch15DualFields.lean:25:6: declaration uses `sorry`
warning: BosonizeStubs/Ch15DualFields.lean:31:6: declaration uses `sorry`
warning: BosonizeStubs/Ch15DualFields.lean:41:6: declaration uses `sorry`
warning: BosonizeStubs/Ch15DualFields.lean:51:6: declaration uses `sorry`
warning: BosonizeStubs/Ch15DualFields.lean:62:6: declaration uses `sorry`
warning: BosonizeStubs/Ch15DualFields.lean:73:8: declaration uses `sorry`
✔ [3410/3411] Built BosonizeStubs (3.3s)
Build completed successfully (3411 jobs).
== Testing the Web-LLM artifact/proof verifiers and axiom audit ==
........[core_lock] Verified 23 complete Core source file(s).
[core_lock] Verified 23 complete Core source file(s).
......
----------------------------------------------------------------------
Ran 14 tests in 20.485s

OK
'Fixture.value' depends on axioms: [sorryAx]
PASS Markdown structure: /tmp/tmpyldh90k_/candidate.md; human evidence/prose review still required
CI OK
make[1]: Leaving directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch15-B-1fe960d8'

```
