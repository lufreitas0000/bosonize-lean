# CH18 Phase C: user-reviewed finish

Running finish records the user's approval of the downloaded content. No independent reviewer is claimed.

Packet: ch18_cycle_c_864a75c9-20261015T055202Z-3c0e731a

Base: 94dc0a8e6aea6d81239ebc86327c79cb32d71fac

Response SHA-256: 61f019439744ded492ca2a56c7953570ae4fca8db06e82db31255877eb7102ca

Candidate commit: 9c92ef72818b6897edde5a9be847f010256f76d5

Model label: chatgpt-chat-high

## Source evidence
- Bosonize/Core/Ch18Bogoliubov.lean: b55da072fac73055173cd65e584751caabdd02f2473648725b09e11c6fbc314b

## Reviewed import/path migration
```json
[
  {
    "from": "BosonizeStubs/Ch18Bogoliubov.lean",
    "to": "Bosonize/Core/Ch18Bogoliubov.lean",
    "source_sha256": "b55da072fac73055173cd65e584751caabdd02f2473648725b09e11c6fbc314b",
    "old_imports": [
      "import Bosonize.Core.A07InteractionsAndBogoliubov",
      "import Bosonize.Core.Ch16FieldHamiltonian",
      "import Bosonize.Core.Ch17LuttingerModels"
    ],
    "new_imports": [
      "import Bosonize.Core.A07InteractionsAndBogoliubov",
      "import Bosonize.Core.Ch16FieldHamiltonian",
      "import Bosonize.Core.Ch17LuttingerModels"
    ]
  }
]
```

## verify-1.log
```text
[stub_lock] Verification PASSED: 906 statement(s) and 977 frozen command(s) verified.
[core_lock] Verified 30 complete Core source file(s).
ℹ [3403/3415] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
ℹ [3411/3415] Replayed Bosonize.Core.A07InteractionsAndBogoliubov
info: Bosonize/Core/A07InteractionsAndBogoliubov.lean:375:2: Try this:
  [apply] abel_nf
Build completed successfully (3415 jobs).
'Bosonize.Ch18.HyperbolicPair.mul_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.HyperbolicPair.c_sub_s_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.HyperbolicPair.c_add_s_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.HyperbolicPair.inverse_combination' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.hyperbolic_params_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.tanh_relation_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerG_mul_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerGInv_eq_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerG_mul_u_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerGInv_mul_u_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerG_eq_sqrt_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerG_pos_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerGInv_pos_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.hyperbolic_coeff_eq_luttinger' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.v2_eq_zero_iff_s_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.u_lt_v1_of_v2_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.vacuum_shift_prefactor_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concrete_velocity_match' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteParams_s_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_creator_inverse_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_creator_inverse_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_annihilator_inverse_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_annihilator_inverse_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_cross_annihilator_creator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_cross_creator_creator_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_cross_annihilator_annihilator_on_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Bosonize.Ch18.luttinger_oscillator_dressed_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttinger_hamiltonian_dressed_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.dressed_annihilator_ground_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.dressed_annihilator_ground_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.dressed_annihilator_ground_right_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.dressed_annihilator_ground_left_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.no_common_bare_dressed_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concrete_bogoliubov_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.HyperbolicPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.HyperbolicPair.ofParams' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerG' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerGInv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.LuttingerParams' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.LuttingerParams.toHyperbolicPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.vacuumShiftScalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteV1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteVF' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteG4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteG2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteCarrierH' does not depend on any axioms
'Bosonize.Ch18.concreteCutoff' does not depend on any axioms
'Bosonize.Ch18.concreteBudget' does not depend on any axioms
'Bosonize.Ch18.concreteMode' does not depend on any axioms
'Bosonize.Ch18.concreteNs' does not depend on any axioms
'Bosonize.Ch18.concreteBranches' depends on axioms: [propext]
'Bosonize.Ch18.concreteParams' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concretePair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.dressedOscillatorOp' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS: BosonizeStubs/Ch18Bogoliubov.lean, 55 freshly audited declarations

```

## verify-2.log
```text
PASS Markdown structure: docs/webllm/drafts/ch18_cycle_c_864a75c9.md; human evidence/prose review still required

```

## Final aggregator.log
```text
'Bosonize.Ch18.HyperbolicPair.mul_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.HyperbolicPair.c_sub_s_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.HyperbolicPair.c_add_s_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.HyperbolicPair.inverse_combination' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.hyperbolic_params_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.tanh_relation_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerG_mul_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerGInv_eq_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerG_mul_u_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerGInv_mul_u_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerG_eq_sqrt_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerG_pos_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerGInv_pos_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.hyperbolic_coeff_eq_luttinger' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.v2_eq_zero_iff_s_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.u_lt_v1_of_v2_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.vacuum_shift_prefactor_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concrete_velocity_match' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteParams_s_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_creator_inverse_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_creator_inverse_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_annihilator_inverse_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_annihilator_inverse_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_cross_annihilator_creator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_cross_creator_creator_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_cross_annihilator_annihilator_on_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Bosonize.Ch18.luttinger_oscillator_dressed_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttinger_hamiltonian_dressed_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.dressed_annihilator_ground_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.dressed_annihilator_ground_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.dressed_annihilator_ground_right_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.dressed_annihilator_ground_left_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.no_common_bare_dressed_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concrete_bogoliubov_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.HyperbolicPair' does not depend on any axioms
'Bosonize.Ch18.HyperbolicPair.ofParams' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerG' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerGInv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.LuttingerParams' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.LuttingerParams.toHyperbolicPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.vacuumShiftScalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteV1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteVF' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteG4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteG2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteCarrierH' does not depend on any axioms
'Bosonize.Ch18.concreteCutoff' does not depend on any axioms
'Bosonize.Ch18.concreteBudget' does not depend on any axioms
'Bosonize.Ch18.concreteMode' does not depend on any axioms
'Bosonize.Ch18.concreteNs' does not depend on any axioms
'Bosonize.Ch18.concreteBranches' depends on axioms: [propext]
'Bosonize.Ch18.concreteParams' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concretePair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.dressedOscillatorOp' depends on axioms: [propext, Classical.choice, Quot.sound]

```

## Final axioms.log
```text
make[1]: Entering directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch18-C-ca8b8689'
[core_lock] Verified 31 complete Core source file(s).
ℹ [3403/3414] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
ℹ [3411/3414] Replayed Bosonize.Core.A07InteractionsAndBogoliubov
info: Bosonize/Core/A07InteractionsAndBogoliubov.lean:375:2: Try this:
  [apply] abel_nf
Build completed successfully (3414 jobs).
'Bosonize.Ch18.HyperbolicPair.mul_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.HyperbolicPair.c_sub_s_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.HyperbolicPair.c_add_s_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.HyperbolicPair.inverse_combination' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.hyperbolic_params_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.tanh_relation_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerG_mul_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerGInv_eq_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerG_mul_u_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerGInv_mul_u_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerG_eq_sqrt_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerG_pos_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerGInv_pos_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.hyperbolic_coeff_eq_luttinger' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.v2_eq_zero_iff_s_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.u_lt_v1_of_v2_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.vacuum_shift_prefactor_of_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concrete_velocity_match' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteParams_s_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_creator_inverse_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_creator_inverse_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_annihilator_inverse_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_annihilator_inverse_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_cross_annihilator_creator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_cross_creator_creator_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.bogoliubov_cross_annihilator_annihilator_on_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Bosonize.Ch18.luttinger_oscillator_dressed_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttinger_hamiltonian_dressed_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.dressed_annihilator_ground_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.dressed_annihilator_ground_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.dressed_annihilator_ground_right_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.dressed_annihilator_ground_left_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.no_common_bare_dressed_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concrete_bogoliubov_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.HyperbolicPair' does not depend on any axioms
'Bosonize.Ch18.HyperbolicPair.ofParams' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerG' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.luttingerGInv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.LuttingerParams' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.LuttingerParams.toHyperbolicPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.vacuumShiftScalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteV1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteVF' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteG4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteG2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concreteCarrierH' does not depend on any axioms
'Bosonize.Ch18.concreteCutoff' does not depend on any axioms
'Bosonize.Ch18.concreteBudget' does not depend on any axioms
'Bosonize.Ch18.concreteMode' does not depend on any axioms
'Bosonize.Ch18.concreteNs' does not depend on any axioms
'Bosonize.Ch18.concreteBranches' depends on axioms: [propext]
'Bosonize.Ch18.concreteParams' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.concretePair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch18.dressedOscillatorOp' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS: 55 freshly built data/theorem declarations
make[1]: Leaving directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch18-C-ca8b8689'

```

## Final ci.log
```text
make[1]: Entering directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch18-C-ca8b8689'
./scripts/ci.sh
== Testing the statement-freeze guard ==
.....................................................................
----------------------------------------------------------------------
Ran 69 tests in 1.475s

OK
== Checking frozen chapter definitions and statements ==
[stub_lock] Verification PASSED: 906 statement(s) and 977 frozen command(s) verified.
== Checking complete frozen Core sources ==
[core_lock] Verified 31 complete Core source file(s).
== Building Bosonize (Core) ==
✔ [3384/3416] Built Bosonize.Core.Ch01LatticeBand (1.5s)
✔ [3385/3416] Built Bosonize.Core.Ch02UmbralCalculus (2.3s)
✔ [3386/3416] Built Bosonize.Core.A01FourierCharacters (2.6s)
✔ [3387/3416] Built Bosonize.Core.A02CARHilbert (3.3s)
✔ [3388/3416] Built Bosonize.Core.Ch03Fourier (4.5s)
✔ [3389/3416] Built Bosonize.Core.Ch04CARFock (4.5s)
✔ [3390/3416] Built Bosonize.Core.A03EnergyBudgets (8.8s)
✔ [3391/3416] Built Bosonize.Core.Ch05Fermions (5.9s)
✔ [3392/3416] Built Bosonize.Core.A04DensityKinematics (9.9s)
✔ [3393/3416] Built Bosonize.Core.Ch06LocalNet (10s)
✔ [3394/3416] Built Bosonize.Core.Ch08Boson (13s)
✔ [3395/3416] Built Bosonize.Core.Ch07VacuumBudget (13s)
✔ [3396/3416] Built Bosonize.Core.A05FiniteExponentials (3.0s)
✔ [3397/3416] Built Bosonize.Core.Ch06Ext (5.0s)
✔ [3398/3416] Built Bosonize.Core.A04PartitionCombinatorics (3.2s)
✔ [3399/3416] Built Bosonize.Core.Ch09DensityModes (5.4s)
✔ [3400/3416] Built Bosonize.Core.A04CurrentMargins (3.5s)
✔ [3401/3416] Built Bosonize.Core.Ch10Heisenberg (4.6s)
✔ [3402/3416] Built Bosonize.Core.Ch11HaldaneCompleteness (11s)
✔ [3403/3416] Built Bosonize.Core.Ch12Sugawara (5.8s)
✔ [3404/3416] Built Bosonize.Core.A05MultiSpecies (9.0s)
ℹ [3405/3416] Built Bosonize.Core.Ch13KleinFactors (5.4s)
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3406/3416] Built Bosonize.Core.Ch14Mandelstam (10s)
✔ [3407/3416] Built Bosonize.Core.A06ChiralFields (10s)
✔ [3408/3416] Built Bosonize.Core.Ch15DualFields (3.9s)
✔ [3409/3416] Built Bosonize.Core.A07FiniteNormalOrdering (3.8s)
✔ [3410/3416] Built Bosonize.Core.Ch16FieldHamiltonian (8.1s)
ℹ [3411/3416] Built Bosonize.Core.A07InteractionsAndBogoliubov (40s)
info: Bosonize/Core/A07InteractionsAndBogoliubov.lean:375:2: Try this:
  [apply] abel_nf
✔ [3412/3416] Built Bosonize.Core.A10DiscreteSchriefferWolff (7.6s)
✔ [3413/3416] Built Bosonize.Core.Ch17LuttingerModels (15s)
✔ [3414/3416] Built Bosonize.Core.Ch18Bogoliubov (8.8s)
✔ [3415/3416] Built Bosonize (2.8s)
Build completed successfully (3416 jobs).
== Building BosonizeStubs (Staging) ==
ℹ [3403/3417] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
ℹ [3411/3417] Replayed Bosonize.Core.A07InteractionsAndBogoliubov
info: Bosonize/Core/A07InteractionsAndBogoliubov.lean:375:2: Try this:
  [apply] abel_nf
✔ [3416/3417] Built BosonizeStubs (2.8s)
Build completed successfully (3417 jobs).
== Testing the Web-LLM artifact/proof verifiers and axiom audit ==
.........[core_lock] Verified 31 complete Core source file(s).
[core_lock] Verified 31 complete Core source file(s).
......
----------------------------------------------------------------------
Ran 15 tests in 14.650s

OK
'Fixture.value' depends on axioms: [sorryAx]
PASS Markdown structure: /tmp/tmpgfv5fpwq/candidate.md; human evidence/prose review still required
CI OK
make[1]: Leaving directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch18-C-ca8b8689'

```
