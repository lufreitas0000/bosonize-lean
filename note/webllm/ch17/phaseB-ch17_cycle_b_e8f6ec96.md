# CH17 Phase B: user-reviewed finish

Running finish records the user's approval of the downloaded content. No independent reviewer is claimed.

Packet: ch17_cycle_b_e8f6ec96-20261014T201059Z-84b6bef3

Base: da92182a17362acfb95d7cfe9c8465360c056aa1

Response SHA-256: fdd47c320e23e1a7df097b75754ba2519776b605d7f66af4506d114375adaa5d

Candidate commit: adced5e3afbdfee3f852e6ed8e36f65067835ad7

Model label: codex-local

## Source evidence
- BosonizeStubs/A07InteractionsAndBogoliubov.lean: 6fb81eaa54ad1b4604a379f69a4462d799a8d31df62df1cb0870602723f19d03

## verify-1.log
```text
[stub_lock] Verification PASSED: 872 statement(s) and 867 frozen command(s) verified.
[core_lock] Verified 27 complete Core source file(s).
ℹ [3404/3412] Replayed Bosonize.Core.Ch13KleinFactors
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

```

## Final ci.log
```text
make[1]: Entering directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch17-B-e9acd44d'
./scripts/ci.sh
== Testing the statement-freeze guard ==
.....................................................................
----------------------------------------------------------------------
Ran 69 tests in 1.730s

OK
== Checking frozen chapter definitions and statements ==
[stub_lock] Verification PASSED: 872 statement(s) and 867 frozen command(s) verified.
== Checking complete frozen Core sources ==
[core_lock] Verified 27 complete Core source file(s).
== Building Bosonize (Core) ==
✔ [3384/3412] Built Bosonize.Core.Ch01LatticeBand (1.5s)
✔ [3385/3412] Built Bosonize.Core.Ch02UmbralCalculus (2.7s)
✔ [3386/3412] Built Bosonize.Core.A01FourierCharacters (2.0s)
✔ [3387/3412] Built Bosonize.Core.A02CARHilbert (3.7s)
✔ [3388/3412] Built Bosonize.Core.Ch03Fourier (5.1s)
✔ [3389/3412] Built Bosonize.Core.Ch04CARFock (5.1s)
✔ [3390/3412] Built Bosonize.Core.A03EnergyBudgets (10s)
✔ [3391/3412] Built Bosonize.Core.Ch05Fermions (6.7s)
✔ [3392/3412] Built Bosonize.Core.A04DensityKinematics (11s)
✔ [3393/3412] Built Bosonize.Core.Ch06LocalNet (12s)
✔ [3394/3412] Built Bosonize.Core.Ch08Boson (16s)
✔ [3395/3412] Built Bosonize.Core.Ch07VacuumBudget (16s)
✔ [3396/3412] Built Bosonize.Core.A05FiniteExponentials (3.3s)
✔ [3397/3412] Built Bosonize.Core.Ch06Ext (7.1s)
✔ [3398/3412] Built Bosonize.Core.A04PartitionCombinatorics (3.3s)
✔ [3399/3412] Built Bosonize.Core.Ch09DensityModes (5.6s)
✔ [3400/3412] Built Bosonize.Core.A04CurrentMargins (3.6s)
✔ [3401/3412] Built Bosonize.Core.Ch10Heisenberg (5.0s)
✔ [3402/3412] Built Bosonize.Core.Ch11HaldaneCompleteness (12s)
✔ [3403/3412] Built Bosonize.Core.Ch12Sugawara (6.3s)
✔ [3404/3412] Built Bosonize.Core.A05MultiSpecies (10s)
ℹ [3405/3412] Built Bosonize.Core.Ch13KleinFactors (6.2s)
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3406/3412] Built Bosonize.Core.Ch14Mandelstam (10s)
✔ [3407/3412] Built Bosonize.Core.A06ChiralFields (10s)
✔ [3408/3412] Built Bosonize.Core.Ch15DualFields (3.7s)
✔ [3409/3412] Built Bosonize.Core.A07FiniteNormalOrdering (3.7s)
✔ [3410/3412] Built Bosonize.Core.Ch16FieldHamiltonian (8.7s)
✔ [3411/3412] Built Bosonize (2.9s)
Build completed successfully (3412 jobs).
== Building BosonizeStubs (Staging) ==
ℹ [3403/3416] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
ℹ [3412/3416] Built BosonizeStubs.A07InteractionsAndBogoliubov (50s)
info: BosonizeStubs/A07InteractionsAndBogoliubov.lean:349:2: Try this:
  [apply] abel_nf
⚠ [3413/3416] Built BosonizeStubs.A10DiscreteSchriefferWolff (2.0s)
warning: BosonizeStubs/A10DiscreteSchriefferWolff.lean:63:8: declaration uses `sorry`
warning: BosonizeStubs/A10DiscreteSchriefferWolff.lean:70:8: declaration uses `sorry`
warning: BosonizeStubs/A10DiscreteSchriefferWolff.lean:76:8: declaration uses `sorry`
warning: BosonizeStubs/A10DiscreteSchriefferWolff.lean:83:8: declaration uses `sorry`
warning: BosonizeStubs/A10DiscreteSchriefferWolff.lean:93:8: declaration uses `sorry`
warning: BosonizeStubs/A10DiscreteSchriefferWolff.lean:146:8: declaration uses `sorry`
warning: BosonizeStubs/A10DiscreteSchriefferWolff.lean:156:6: declaration uses `sorry`
warning: BosonizeStubs/A10DiscreteSchriefferWolff.lean:160:6: declaration uses `sorry`
warning: BosonizeStubs/A10DiscreteSchriefferWolff.lean:164:6: declaration uses `sorry`
warning: BosonizeStubs/A10DiscreteSchriefferWolff.lean:168:6: declaration uses `sorry`
warning: BosonizeStubs/A10DiscreteSchriefferWolff.lean:177:8: declaration uses `sorry`
⚠ [3414/3416] Built BosonizeStubs.Ch17LuttingerModels (3.0s)
warning: BosonizeStubs/Ch17LuttingerModels.lean:44:6: declaration uses `sorry`
warning: BosonizeStubs/Ch17LuttingerModels.lean:116:8: declaration uses `sorry`
warning: BosonizeStubs/Ch17LuttingerModels.lean:121:6: declaration uses `sorry`
warning: BosonizeStubs/Ch17LuttingerModels.lean:127:8: declaration uses `sorry`
warning: BosonizeStubs/Ch17LuttingerModels.lean:135:8: declaration uses `sorry`
warning: BosonizeStubs/Ch17LuttingerModels.lean:144:8: declaration uses `sorry`
warning: BosonizeStubs/Ch17LuttingerModels.lean:153:8: declaration uses `sorry`
warning: BosonizeStubs/Ch17LuttingerModels.lean:168:8: declaration uses `sorry`
✔ [3415/3416] Built BosonizeStubs (2.8s)
Build completed successfully (3416 jobs).
== Testing the Web-LLM artifact/proof verifiers and axiom audit ==
.........[core_lock] Verified 27 complete Core source file(s).
[core_lock] Verified 27 complete Core source file(s).
......
----------------------------------------------------------------------
Ran 15 tests in 18.525s

OK
'Fixture.value' depends on axioms: [sorryAx]
PASS Markdown structure: /tmp/tmp711adr2h/candidate.md; human evidence/prose review still required
CI OK
make[1]: Leaving directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch17-B-e9acd44d'

```
