# CH18 Phase B: user-reviewed finish

Running finish records the user's approval of the downloaded content. No independent reviewer is claimed.

Packet: ch18_cycle_b_0648ad0f-20261015T054228Z-af073e60

Base: b8b0ff0b970786d9317b7c8150a6999626005636

Response SHA-256: 211d6ad04bf29a78fce51fd296eb4777db37a9e805376b9733cdbbd41a6ff150

Candidate commit: 45f2703c318619ff9b9ca4f1589cddbcfc532a9a

Model label: chatgpt-chat-high

## Source evidence
- BosonizeStubs/Ch18Bogoliubov.lean: b55da072fac73055173cd65e584751caabdd02f2473648725b09e11c6fbc314b

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

## Final ci.log
```text
make[1]: Entering directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch18-B-b1add690'
./scripts/ci.sh
== Testing the statement-freeze guard ==
.....................................................................
----------------------------------------------------------------------
Ran 69 tests in 1.465s

OK
== Checking frozen chapter definitions and statements ==
[stub_lock] Verification PASSED: 906 statement(s) and 977 frozen command(s) verified.
== Checking complete frozen Core sources ==
[core_lock] Verified 30 complete Core source file(s).
== Building Bosonize (Core) ==
✔ [3384/3415] Built Bosonize.Core.Ch01LatticeBand (1.4s)
✔ [3385/3415] Built Bosonize.Core.Ch02UmbralCalculus (2.4s)
✔ [3386/3415] Built Bosonize.Core.A01FourierCharacters (2.6s)
✔ [3387/3415] Built Bosonize.Core.A02CARHilbert (3.3s)
✔ [3388/3415] Built Bosonize.Core.Ch03Fourier (4.4s)
✔ [3389/3415] Built Bosonize.Core.Ch04CARFock (4.5s)
✔ [3390/3415] Built Bosonize.Core.A03EnergyBudgets (8.6s)
✔ [3391/3415] Built Bosonize.Core.Ch05Fermions (5.4s)
✔ [3392/3415] Built Bosonize.Core.A04DensityKinematics (9.6s)
✔ [3393/3415] Built Bosonize.Core.Ch06LocalNet (10s)
✔ [3394/3415] Built Bosonize.Core.Ch08Boson (14s)
✔ [3395/3415] Built Bosonize.Core.Ch07VacuumBudget (13s)
✔ [3396/3415] Built Bosonize.Core.A05FiniteExponentials (3.0s)
✔ [3397/3415] Built Bosonize.Core.A04PartitionCombinatorics (3.2s)
✔ [3398/3415] Built Bosonize.Core.Ch06Ext (6.4s)
✔ [3399/3415] Built Bosonize.Core.Ch09DensityModes (4.9s)
✔ [3400/3415] Built Bosonize.Core.A04CurrentMargins (3.2s)
✔ [3401/3415] Built Bosonize.Core.Ch10Heisenberg (4.5s)
✔ [3402/3415] Built Bosonize.Core.Ch11HaldaneCompleteness (10s)
✔ [3403/3415] Built Bosonize.Core.Ch12Sugawara (6.1s)
✔ [3404/3415] Built Bosonize.Core.A05MultiSpecies (9.0s)
ℹ [3405/3415] Built Bosonize.Core.Ch13KleinFactors (4.9s)
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3406/3415] Built Bosonize.Core.Ch14Mandelstam (9.3s)
✔ [3407/3415] Built Bosonize.Core.A06ChiralFields (9.7s)
✔ [3408/3415] Built Bosonize.Core.Ch15DualFields (3.7s)
✔ [3409/3415] Built Bosonize.Core.A07FiniteNormalOrdering (3.4s)
✔ [3410/3415] Built Bosonize.Core.Ch16FieldHamiltonian (7.9s)
ℹ [3411/3415] Built Bosonize.Core.A07InteractionsAndBogoliubov (38s)
info: Bosonize/Core/A07InteractionsAndBogoliubov.lean:375:2: Try this:
  [apply] abel_nf
✔ [3412/3415] Built Bosonize.Core.A10DiscreteSchriefferWolff (7.7s)
✔ [3413/3415] Built Bosonize.Core.Ch17LuttingerModels (15s)
✔ [3414/3415] Built Bosonize (2.4s)
Build completed successfully (3415 jobs).
== Building BosonizeStubs (Staging) ==
ℹ [3404/3417] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
ℹ [3411/3417] Replayed Bosonize.Core.A07InteractionsAndBogoliubov
info: Bosonize/Core/A07InteractionsAndBogoliubov.lean:375:2: Try this:
  [apply] abel_nf
✔ [3415/3417] Built BosonizeStubs.Ch18Bogoliubov (8.3s)
✔ [3416/3417] Built BosonizeStubs (2.5s)
Build completed successfully (3417 jobs).
== Testing the Web-LLM artifact/proof verifiers and axiom audit ==
.........[core_lock] Verified 30 complete Core source file(s).
[core_lock] Verified 30 complete Core source file(s).
......
----------------------------------------------------------------------
Ran 15 tests in 14.943s

OK
'Fixture.value' depends on axioms: [sorryAx]
PASS Markdown structure: /tmp/tmpk9enw1_z/candidate.md; human evidence/prose review still required
CI OK
make[1]: Leaving directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch18-B-b1add690'

```
