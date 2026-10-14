# CH17 Phase B: user-reviewed finish

Running finish records the user's approval of the downloaded content. No independent reviewer is claimed.

Packet: ch17_cycle_b_0ed0c297-20261014T204148Z-9fa634a3

Base: 914f09b7cb3cd326a146705243d29cba561fd8bb

Response SHA-256: 45d448bda532726c2d4a9efe5dc2292db691baa4478c837b6cff2c69cff00e55

Candidate commit: b92e0b9fe6c0260086e8218dd2a8dd0998579aed

Model label: codex-local

## Source evidence
- BosonizeStubs/Ch17LuttingerModels.lean: d535a4cdd406507170e1b202b59dde26e9f33ca33d5f34492b6414a369e65f2e

## verify-1.log
```text
[stub_lock] Verification PASSED: 872 statement(s) and 867 frozen command(s) verified.
[core_lock] Verified 27 complete Core source file(s).
ℹ [3403/3412] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Build completed successfully (3412 jobs).
Try this:
  [apply] abel_nf
'Bosonize.A07Interactions.hyperbolic_params_exist' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.sea_normal_bilinear_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.sea_normal_rho_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.sea_normal_rho_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.quartic_sea_wick_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.quartic_sea_wick_zero_repeated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.species_raw_intra_eq_current_sub_correction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Bosonize.A07Interactions.raw_intra_eq_current_sub_correction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Bosonize.A07Interactions.sea_wick_correction_ground_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.sea_wick_correction_full_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.raw_inter_eq_hopping' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.hopping_mode_kills_ground' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.pairing_mode_ground_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.hopping_mode_self_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.pairing_mode_self_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.bogoliubov_creator_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.bogoliubov_expansion_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.bogoliubov_ccr_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.seaIndicator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.creatorToSeaLetter' does not depend on any axioms
'Bosonize.A07Interactions.annihilatorToSeaLetter' does not depend on any axioms
'Bosonize.A07Interactions.seaInversions' does not depend on any axioms
'Bosonize.A07Interactions.bilinearWord' does not depend on any axioms
'Bosonize.A07Interactions.quarticWord' does not depend on any axioms
'Bosonize.A07Interactions.seaWickWeight' does not depend on any axioms
'Bosonize.A07Interactions.oppositeOrientation' does not depend on any axioms
'Bosonize.A07Interactions.HyperbolicParams' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.seaQuasiAnnihilator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.seaQuasiCreator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.evalSeaLetter' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.seaWickWord' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.numberOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.seaSubtractedNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.seaNormalBilinear' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.seaNormalRho' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.quarticSeaWick' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.quarticContraction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.seaWickTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.seaWickCorrection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.computationalMomentum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.speciesRawIntra' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.rawIntraBranch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.speciesCurrentIntra' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.currentIntraBranch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.rawInterBranch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.hoppingInterBranch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.pairingInterBranch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.hoppingMode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.pairingMode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.bogoliubovCreator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.bogoliubovAnnihilator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.dressedModeNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS: BosonizeStubs/A07InteractionsAndBogoliubov.lean, 52 freshly audited declarations
'Bosonize.A10.sw_generator_commutator_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.sw_generator_skew_hermitian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.sw_2x2_truncation_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.sw_3x3_no_iff_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.sw_2x2_exact_eigenpair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.sw_compressed_bch_second_order' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.shell_proj_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.shell_proj_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.shell_proj_self_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.energy_shell_discards_double_mode_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.sw_off_zero_implies_effective_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.swGeneratorMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.diagEnergyMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.nonResonant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.swCounterH0_2x2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.swCounterV_2x2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.swCounterS1_2x2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.swCounterP_2x2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.swCounterH0_3x3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.swCounterP_3x3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.swCounterQ_3x3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.swCounterV_3x3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.swCounterS1_3x3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.swCounterEigenvector_2x2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.exactShellSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.lowShellProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.highShellProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.doubleModeOneKet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.diagPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.offDiagPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.swSecondOrderCorrection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.swEffectiveSecondOrder' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A10.bchSecondOrderPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS: BosonizeStubs/A10DiscreteSchriefferWolff.lean, 33 freshly audited declarations
'Bosonize.Ch17.zero_mode_scalar_canonical_mu' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch17.luttinger_chosen_eq_bosonized' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch17.zero_mode_op_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch17.free_fermion_eq_sugawara_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch17.luttinger_hamiltonian_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch17.luttinger_hamiltonian_canonical_mu_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch17.luttinger_raw_intra_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch17.concrete_luttinger_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch17.v1Velocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch17.v2Velocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch17.canonicalMu' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch17.sugawaraMargin' depends on axioms: [propext]
'Bosonize.Ch17.zeroModeEnergyScalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch17.symmetricZeroModeScalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch17.chemicalPotentialOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch17.freeSugawaraKinetic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch17.freeFermionKinetic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch17.zeroModeEnergyOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch17.luttingerOscillatorOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch17.luttingerBosonizedHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch17.luttingerChosenModel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch17.luttingerFermionChosenModel' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS: BosonizeStubs/Ch17LuttingerModels.lean, 22 freshly audited declarations

```

## Final ci.log
```text
make[1]: Entering directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch17-B-e4f5efdd'
./scripts/ci.sh
== Testing the statement-freeze guard ==
.....................................................................
----------------------------------------------------------------------
Ran 69 tests in 1.947s

OK
== Checking frozen chapter definitions and statements ==
[stub_lock] Verification PASSED: 872 statement(s) and 867 frozen command(s) verified.
== Checking complete frozen Core sources ==
[core_lock] Verified 27 complete Core source file(s).
== Building Bosonize (Core) ==
✔ [3384/3412] Built Bosonize.Core.Ch01LatticeBand (1.5s)
✔ [3385/3412] Built Bosonize.Core.Ch02UmbralCalculus (2.4s)
✔ [3386/3412] Built Bosonize.Core.A01FourierCharacters (2.8s)
✔ [3387/3412] Built Bosonize.Core.A02CARHilbert (3.6s)
✔ [3388/3412] Built Bosonize.Core.Ch03Fourier (5.2s)
✔ [3389/3412] Built Bosonize.Core.Ch04CARFock (5.0s)
✔ [3390/3412] Built Bosonize.Core.A03EnergyBudgets (9.7s)
✔ [3391/3412] Built Bosonize.Core.Ch05Fermions (5.0s)
✔ [3392/3412] Built Bosonize.Core.A04DensityKinematics (10s)
✔ [3393/3412] Built Bosonize.Core.Ch06LocalNet (11s)
✔ [3394/3412] Built Bosonize.Core.Ch08Boson (14s)
✔ [3395/3412] Built Bosonize.Core.Ch07VacuumBudget (14s)
✔ [3396/3412] Built Bosonize.Core.A05FiniteExponentials (3.4s)
✔ [3397/3412] Built Bosonize.Core.A04PartitionCombinatorics (3.4s)
✔ [3398/3412] Built Bosonize.Core.Ch06Ext (6.9s)
✔ [3399/3412] Built Bosonize.Core.Ch09DensityModes (6.0s)
✔ [3400/3412] Built Bosonize.Core.A04CurrentMargins (3.6s)
✔ [3401/3412] Built Bosonize.Core.Ch10Heisenberg (4.7s)
✔ [3402/3412] Built Bosonize.Core.Ch11HaldaneCompleteness (12s)
✔ [3403/3412] Built Bosonize.Core.Ch12Sugawara (6.1s)
✔ [3404/3412] Built Bosonize.Core.A05MultiSpecies (8.0s)
ℹ [3405/3412] Built Bosonize.Core.Ch13KleinFactors (6.1s)
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3406/3412] Built Bosonize.Core.Ch14Mandelstam (10s)
✔ [3407/3412] Built Bosonize.Core.A06ChiralFields (11s)
✔ [3408/3412] Built Bosonize.Core.Ch15DualFields (4.3s)
✔ [3409/3412] Built Bosonize.Core.A07FiniteNormalOrdering (3.8s)
✔ [3410/3412] Built Bosonize.Core.Ch16FieldHamiltonian (8.8s)
✔ [3411/3412] Built Bosonize (2.8s)
Build completed successfully (3412 jobs).
== Building BosonizeStubs (Staging) ==
ℹ [3403/3416] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
ℹ [3412/3416] Built BosonizeStubs.A07InteractionsAndBogoliubov (44s)
info: BosonizeStubs/A07InteractionsAndBogoliubov.lean:349:2: Try this:
  [apply] abel_nf
✔ [3413/3416] Built BosonizeStubs.A10DiscreteSchriefferWolff (8.8s)
✔ [3414/3416] Built BosonizeStubs.Ch17LuttingerModels (18s)
✔ [3415/3416] Built BosonizeStubs (2.6s)
Build completed successfully (3416 jobs).
== Testing the Web-LLM artifact/proof verifiers and axiom audit ==
.........[core_lock] Verified 27 complete Core source file(s).
[core_lock] Verified 27 complete Core source file(s).
......
----------------------------------------------------------------------
Ran 15 tests in 18.535s

OK
'Fixture.value' depends on axioms: [sorryAx]
PASS Markdown structure: /tmp/tmpeiw7chqc/candidate.md; human evidence/prose review still required
CI OK
make[1]: Leaving directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch17-B-e4f5efdd'

```
