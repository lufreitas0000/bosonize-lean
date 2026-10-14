# CH17 Phase C: user-reviewed finish

Running finish records the user's approval of the downloaded content. No independent reviewer is claimed.

Packet: ch17_cycle_c_fefac95c-20261014T205013Z-15f4a46b

Base: be2584bacf6831a83180217b75116adfd44c1626

Response SHA-256: fe12e976184536f5709da151a6aaa569bd226e43e51a895ddc59bd446dc9df02

Candidate commit: f09bedaaf396163c13ad7316ac0dea7fda29699c

Model label: codex-local

## Source evidence
- Bosonize/Core/A07InteractionsAndBogoliubov.lean: 1e96db0038b2ae7f012e16d1f6d5a98b43b33661d31f4220cdf3399530fca59f
- Bosonize/Core/A10DiscreteSchriefferWolff.lean: 7ea9ac1c592eed76fc9349ff63592363c2f9efdb0876dc0c93ddf24e9f74b33f
- Bosonize/Core/Ch17LuttingerModels.lean: 9355fcc40f2ec1e5d9ac5ef07065ee8d03a957d8329ef9d5d528e7f1f2e3223c

## Reviewed import/path migration
```json
[
  {
    "from": "BosonizeStubs/A07InteractionsAndBogoliubov.lean",
    "to": "Bosonize/Core/A07InteractionsAndBogoliubov.lean",
    "source_sha256": "1e96db0038b2ae7f012e16d1f6d5a98b43b33661d31f4220cdf3399530fca59f",
    "old_imports": [
      "import Bosonize"
    ],
    "new_imports": [
      "import Bosonize.Core.A07FiniteNormalOrdering",
      "import Bosonize.Core.Ch16FieldHamiltonian",
      "import Bosonize.Core.A06ChiralFields",
      "import Bosonize.Core.Ch15DualFields",
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
    "from": "BosonizeStubs/A10DiscreteSchriefferWolff.lean",
    "to": "Bosonize/Core/A10DiscreteSchriefferWolff.lean",
    "source_sha256": "7ea9ac1c592eed76fc9349ff63592363c2f9efdb0876dc0c93ddf24e9f74b33f",
    "old_imports": [
      "import Bosonize",
      "import BosonizeStubs.A07InteractionsAndBogoliubov"
    ],
    "new_imports": [
      "import Bosonize.Core.A07FiniteNormalOrdering",
      "import Bosonize.Core.Ch16FieldHamiltonian",
      "import Bosonize.Core.A06ChiralFields",
      "import Bosonize.Core.Ch15DualFields",
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
      "import Bosonize.Core.Ch12Sugawara",
      "import Bosonize.Core.A07InteractionsAndBogoliubov"
    ]
  },
  {
    "from": "BosonizeStubs/Ch17LuttingerModels.lean",
    "to": "Bosonize/Core/Ch17LuttingerModels.lean",
    "source_sha256": "9355fcc40f2ec1e5d9ac5ef07065ee8d03a957d8329ef9d5d528e7f1f2e3223c",
    "old_imports": [
      "import Bosonize",
      "import BosonizeStubs.A07InteractionsAndBogoliubov",
      "import BosonizeStubs.A10DiscreteSchriefferWolff"
    ],
    "new_imports": [
      "import Bosonize.Core.A07FiniteNormalOrdering",
      "import Bosonize.Core.Ch16FieldHamiltonian",
      "import Bosonize.Core.A06ChiralFields",
      "import Bosonize.Core.Ch15DualFields",
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
      "import Bosonize.Core.Ch12Sugawara",
      "import Bosonize.Core.A07InteractionsAndBogoliubov",
      "import Bosonize.Core.A10DiscreteSchriefferWolff"
    ]
  }
]
```

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

## verify-2.log
```text
PASS Markdown structure: docs/webllm/drafts/ch17_cycle_c_fefac95c.md; human evidence/prose review still required

```

## Final aggregator.log
```text
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

```

## Final axioms.log
```text
make[1]: Entering directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch17-C-93bbd2ce'
[core_lock] Verified 30 complete Core source file(s).
ℹ [3403/3413] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
ℹ [3411/3413] Replayed Bosonize.Core.A07InteractionsAndBogoliubov
info: Bosonize/Core/A07InteractionsAndBogoliubov.lean:375:2: Try this:
  [apply] abel_nf
Build completed successfully (3413 jobs).
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
PASS: 107 freshly built data/theorem declarations
make[1]: Leaving directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch17-C-93bbd2ce'

```

## Final ci.log
```text
make[1]: Entering directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch17-C-93bbd2ce'
./scripts/ci.sh
== Testing the statement-freeze guard ==
.....................................................................
----------------------------------------------------------------------
Ran 69 tests in 1.476s

OK
== Checking frozen chapter definitions and statements ==
[stub_lock] Verification PASSED: 872 statement(s) and 945 frozen command(s) verified.
== Checking complete frozen Core sources ==
[core_lock] Verified 30 complete Core source file(s).
== Building Bosonize (Core) ==
✔ [3384/3415] Built Bosonize.Core.Ch01LatticeBand (1.6s)
✔ [3385/3415] Built Bosonize.Core.Ch02UmbralCalculus (2.9s)
✔ [3386/3415] Built Bosonize.Core.A01FourierCharacters (3.3s)
✔ [3387/3415] Built Bosonize.Core.A02CARHilbert (4.2s)
✔ [3388/3415] Built Bosonize.Core.Ch03Fourier (7.0s)
✔ [3389/3415] Built Bosonize.Core.Ch04CARFock (6.9s)
✔ [3390/3415] Built Bosonize.Core.A03EnergyBudgets (13s)
✔ [3391/3415] Built Bosonize.Core.Ch05Fermions (8.0s)
✔ [3392/3415] Built Bosonize.Core.A04DensityKinematics (14s)
✔ [3393/3415] Built Bosonize.Core.Ch06LocalNet (16s)
✔ [3394/3415] Built Bosonize.Core.Ch08Boson (20s)
✔ [3395/3415] Built Bosonize.Core.Ch07VacuumBudget (21s)
✔ [3396/3415] Built Bosonize.Core.A05FiniteExponentials (4.8s)
✔ [3397/3415] Built Bosonize.Core.Ch06Ext (9.5s)
✔ [3398/3415] Built Bosonize.Core.A04PartitionCombinatorics (4.5s)
✔ [3399/3415] Built Bosonize.Core.Ch09DensityModes (5.0s)
✔ [3400/3415] Built Bosonize.Core.A04CurrentMargins (3.8s)
✔ [3401/3415] Built Bosonize.Core.Ch10Heisenberg (5.1s)
✔ [3402/3415] Built Bosonize.Core.Ch11HaldaneCompleteness (12s)
✔ [3403/3415] Built Bosonize.Core.Ch12Sugawara (8.4s)
✔ [3404/3415] Built Bosonize.Core.A05MultiSpecies (12s)
ℹ [3405/3415] Built Bosonize.Core.Ch13KleinFactors (6.9s)
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3406/3415] Built Bosonize.Core.Ch14Mandelstam (12s)
✔ [3407/3415] Built Bosonize.Core.A06ChiralFields (12s)
✔ [3408/3415] Built Bosonize.Core.Ch15DualFields (4.2s)
✔ [3409/3415] Built Bosonize.Core.A07FiniteNormalOrdering (3.6s)
✔ [3410/3415] Built Bosonize.Core.Ch16FieldHamiltonian (9.7s)
ℹ [3411/3415] Built Bosonize.Core.A07InteractionsAndBogoliubov (51s)
info: Bosonize/Core/A07InteractionsAndBogoliubov.lean:375:2: Try this:
  [apply] abel_nf
✔ [3412/3415] Built Bosonize.Core.A10DiscreteSchriefferWolff (10s)
✔ [3413/3415] Built Bosonize.Core.Ch17LuttingerModels (20s)
✔ [3414/3415] Built Bosonize (2.4s)
Build completed successfully (3415 jobs).
== Building BosonizeStubs (Staging) ==
ℹ [3403/3416] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
ℹ [3411/3416] Replayed Bosonize.Core.A07InteractionsAndBogoliubov
info: Bosonize/Core/A07InteractionsAndBogoliubov.lean:375:2: Try this:
  [apply] abel_nf
✔ [3415/3416] Built BosonizeStubs (2.3s)
Build completed successfully (3416 jobs).
== Testing the Web-LLM artifact/proof verifiers and axiom audit ==
.........[core_lock] Verified 30 complete Core source file(s).
[core_lock] Verified 30 complete Core source file(s).
......
----------------------------------------------------------------------
Ran 15 tests in 15.633s

OK
'Fixture.value' depends on axioms: [sorryAx]
PASS Markdown structure: /tmp/tmpiz5uvyb_/candidate.md; human evidence/prose review still required
CI OK
make[1]: Leaving directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch17-C-93bbd2ce'

```
