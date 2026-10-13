# CH15 Phase C: user-reviewed finish

Running finish records the user's approval of the downloaded content. No independent reviewer is claimed.

Packet: ch15_cycle_c_463e5816-20261013T190333Z-1daf480b

Base: d9259475ce4032b6ce73a44c5d319ebbb40c3a07

Response SHA-256: e400731f96b11f9b855ca1240a0b901ec041a9d8ef1fe7aa23b57dff2115564f

Candidate commit: 23183e7a6f085f2420347d3899f690fae630a54a

Model label: codex-local

## Source evidence
- Bosonize/Core/A06ChiralFields.lean: 77c579ff06238d2801e9861fdf65c5c1efc66fc31d0161efd18a6a386d2fa768
- Bosonize/Core/Ch15DualFields.lean: 30880501f9f71594b9e1cc0af6784428cbc0d48c6e70c8930c5d2c27caa9ff85

## Reviewed import/path migration
```json
[
  {
    "from": "BosonizeStubs/A06ChiralFields.lean",
    "to": "Bosonize/Core/A06ChiralFields.lean",
    "source_sha256": "77c579ff06238d2801e9861fdf65c5c1efc66fc31d0161efd18a6a386d2fa768",
    "old_imports": [
      "import Bosonize"
    ],
    "new_imports": [
      "import Bosonize.Core.Ch01LatticeBand",
      "import Bosonize.Core.Ch02UmbralCalculus",
      "import Bosonize.Core.A01FourierCharacters",
      "import Bosonize.Core.Ch03Fourier",
      "import Bosonize.Core.A02CARHilbert",
      "import Bosonize.Core.Ch04CARFock",
      "import Bosonize.Core.Ch05Fermions",
      "import Bosonize.Core.Ch06LocalNet",
      "import Bosonize.Core.Ch06Ext",
      "import Bosonize.Core.A03EnergyBudgets",
      "import Bosonize.Core.Ch07VacuumBudget",
      "import Bosonize.Core.Ch08Boson",
      "import Bosonize.Core.A05MultiSpecies",
      "import Bosonize.Core.Ch13KleinFactors",
      "import Bosonize.Core.A05FiniteExponentials",
      "import Bosonize.Core.Ch14Mandelstam",
      "import Bosonize.Core.A04DensityKinematics",
      "import Bosonize.Core.Ch09DensityModes",
      "import Bosonize.Core.A04CurrentMargins",
      "import Bosonize.Core.Ch10Heisenberg",
      "import Bosonize.Core.A04PartitionCombinatorics",
      "import Bosonize.Core.Ch11HaldaneCompleteness",
      "import Bosonize.Core.Ch12Sugawara"
    ]
  },
  {
    "from": "BosonizeStubs/Ch15DualFields.lean",
    "to": "Bosonize/Core/Ch15DualFields.lean",
    "source_sha256": "30880501f9f71594b9e1cc0af6784428cbc0d48c6e70c8930c5d2c27caa9ff85",
    "old_imports": [
      "import BosonizeStubs.A06ChiralFields"
    ],
    "new_imports": [
      "import Bosonize.Core.A06ChiralFields"
    ]
  }
]
```

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

## verify-2.log
```text
PASS Markdown structure: docs/webllm/drafts/ch15_cycle_c_463e5816.md; human evidence/prose review still required

```

## Final aggregator.log
```text
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
'Bosonize.Ch15.phi_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.theta_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.phi_self_commutator_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.theta_self_commutator_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.mixed_commutator_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.mixed_forward_diff_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.zero_mode_obstruction_on_ground' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.phiField' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.thetaField' depends on axioms: [propext, Classical.choice, Quot.sound]

```

## Final axioms.log
```text
make[1]: Entering directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch15-C-e6330f7e'
[core_lock] Verified 25 complete Core source file(s).
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
'Bosonize.Ch15.phi_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.theta_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.phi_self_commutator_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.theta_self_commutator_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.mixed_commutator_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.mixed_forward_diff_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.zero_mode_obstruction_on_ground' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.phiField' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.thetaField' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS: 38 freshly built data/theorem declarations
make[1]: Leaving directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch15-C-e6330f7e'

```

## Final ci.log
```text
make[1]: Entering directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch15-C-e6330f7e'
./scripts/ci.sh
== Testing the statement-freeze guard ==
.....................................................................
----------------------------------------------------------------------
Ran 69 tests in 1.530s

OK
== Checking frozen chapter definitions and statements ==
[stub_lock] Verification PASSED: 816 statement(s) and 679 frozen command(s) verified.
== Checking complete frozen Core sources ==
[core_lock] Verified 25 complete Core source file(s).
== Building Bosonize (Core) ==
✔ [3384/3410] Built Bosonize.Core.Ch01LatticeBand (1.5s)
✔ [3385/3410] Built Bosonize.Core.Ch02UmbralCalculus (2.6s)
✔ [3386/3410] Built Bosonize.Core.A01FourierCharacters (2.8s)
✔ [3387/3410] Built Bosonize.Core.A02CARHilbert (3.6s)
✔ [3388/3410] Built Bosonize.Core.Ch03Fourier (5.1s)
✔ [3389/3410] Built Bosonize.Core.Ch04CARFock (5.2s)
✔ [3390/3410] Built Bosonize.Core.A03EnergyBudgets (10s)
✔ [3391/3410] Built Bosonize.Core.Ch05Fermions (6.5s)
✔ [3392/3410] Built Bosonize.Core.A04DensityKinematics (11s)
✔ [3393/3410] Built Bosonize.Core.Ch06LocalNet (12s)
✔ [3394/3410] Built Bosonize.Core.Ch08Boson (15s)
✔ [3395/3410] Built Bosonize.Core.Ch07VacuumBudget (15s)
✔ [3396/3410] Built Bosonize.Core.A05FiniteExponentials (3.5s)
✔ [3397/3410] Built Bosonize.Core.A04PartitionCombinatorics (3.9s)
✔ [3398/3410] Built Bosonize.Core.Ch06Ext (6.9s)
✔ [3399/3410] Built Bosonize.Core.Ch09DensityModes (5.7s)
✔ [3400/3410] Built Bosonize.Core.A04CurrentMargins (3.9s)
✔ [3401/3410] Built Bosonize.Core.Ch10Heisenberg (4.9s)
✔ [3402/3410] Built Bosonize.Core.Ch11HaldaneCompleteness (10s)
✔ [3403/3410] Built Bosonize.Core.Ch12Sugawara (6.3s)
✔ [3404/3410] Built Bosonize.Core.A05MultiSpecies (9.1s)
ℹ [3405/3410] Built Bosonize.Core.Ch13KleinFactors (5.5s)
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3406/3410] Built Bosonize.Core.Ch14Mandelstam (10s)
✔ [3407/3410] Built Bosonize.Core.A06ChiralFields (10s)
✔ [3408/3410] Built Bosonize.Core.Ch15DualFields (3.9s)
✔ [3409/3410] Built Bosonize (2.5s)
Build completed successfully (3410 jobs).
== Building BosonizeStubs (Staging) ==
ℹ [3403/3411] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3410/3411] Built BosonizeStubs (2.6s)
Build completed successfully (3411 jobs).
== Testing the Web-LLM artifact/proof verifiers and axiom audit ==
.........[core_lock] Verified 25 complete Core source file(s).
[core_lock] Verified 25 complete Core source file(s).
......
----------------------------------------------------------------------
Ran 15 tests in 16.562s

OK
'Fixture.value' depends on axioms: [sorryAx]
PASS Markdown structure: /tmp/tmpaj7m9gfu/candidate.md; human evidence/prose review still required
CI OK
make[1]: Leaving directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch15-C-e6330f7e'

```
