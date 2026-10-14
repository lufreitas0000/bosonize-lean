# CH17 Phase B continuation checkpoint — 2026-10-14

Recorded: 2026-10-14T11:14:00.921332-03:00. Partial development checkpoint, not batch acceptance or Phase B completion. Phase C is authorized after complete Phase B verification and remains unstarted. Stop after CH17.

## Baseline and scope

Primary main/active packet baseline: `f464a50f3d07e81153150ca570a4aea3ad90155a`.
Packet: `ch17_cycle_b_a8767708-20261014T011412Z-5d98e758`.
Candidate worktree: `/home/lucas/Projects/.packets/worktrees/ch17-phase-b` on `codex/ch17-phase-b`.
Prior checkpoint: `f9500ee` and `phaseB-checkpoint-a07.md`.
All existing interfaces, data, namespaces, imports and lock records remain unchanged. Core guard verifies 27 complete Core files; strict statement guard verifies 872 statements and 867 frozen commands. A guard caught a broad replacement of A10.highShellProj's frozen letI with let; that accidental edit was reverted before checkpoint, restoring the exact frozen definition. All actual proof changes are inside the existing bodies.

Primary has unrelated user note deletions and a notes/draft-lean-code directory. These are untouched, excluded from this branch and not stashed or committed. Recheck/preserve their current state before runner integration; do not overwrite them.

## Compiler and axiom evidence

Fresh combined candidate with the actual three source modules compiled using installed Lean 4.35.0-rc4, autoImplicit=false and relaxedAutoImplicit=false: exit 0, exactly TWO original placeholder warnings, ZERO other warnings/errors. #print axioms audited all 107 declarations (70 data + 37 theorem contracts). Data has only permitted standard axioms. Thirty theorem proofs use only permitted standard axioms; five implemented wrappers/aggregates inherit sorryAx from two remaining original stubs. This was a partial checkpoint compiler audit, not whole Phase B warning-as-error success or CI. A10 alone separately passed a fresh warning-as-error audit for all 33 declarations (22 data +11 theorems).

| Module | Contracts | Original stubs | Standard-axiom theorem proofs | sorryAx-dependent contracts | Source SHA-256 |
| :--- | ---: | ---: | ---: | ---: | :--- |
| A07InteractionsAndBogoliubov | 18 | 1 | 15 | 3 | `d38c96716a65de6156d56ea1bfc87b11170ecbac5c601cd24574ed8c0c2d6a44` |
| A10DiscreteSchriefferWolff | 11 | 0 | 11 | 0 | `b77a079f426943fa6fb5609316dfdb645371c88c48be82875ad480094990594c` |
| Ch17LuttingerModels | 8 | 1 | 4 | 4 | `600afba3fa26a451e2d4ce98ee3e9ecb1d76b4f695a0b93a5bbc50b8076ba48c` |

Thirty-five of thirty-seven proof bodies are implemented. This is not thirty-five completed theorem proofs: thirty are complete and five await dependencies.

A07 progress: sea_normal_rho_zero, sea_wick_correction_ground_zero, sea_wick_correction_full_band and species_raw_intra_eq_current_sub_correction implemented in this continuation. The aggregate retains exact finite edge commutators, pairs opposite transfers, and counts finite sea-hole/particle distances. Its body inherits sorryAx only from the unfinished general quartic identity. raw_inter_eq_hopping is now standard-axiom complete after its sea-current dependencies were proved.

A10: all eleven proof bodies and nonzero shell witness are complete. Generator equation and skew-Hermitian matrix signs are exact; eigenpair and truncation witnesses use actual finite matrices; degree-two BCH compression is an exact polynomial identity. Shell projections sum to the actual budget projector. Repeated mode-one ket has true nonzero action and low/high projection distinction, using restricted input CCR and lowering rather than unproved exact grading. Frozen hypotheses that are redundant for the polynomial identity remain unchanged and are explicitly referenced in its body.

CH17: seven bodies implemented. Scalar chemical-potential equality, chosen-model decomposition, zero-mode budget action and concrete witness are standard-axiom complete. Three budget/raw/canonical wrappers inherit the sharp free-fermion/Sugawara stub. The concrete witness was repaired by using a generic species/cutoff helper inside its existing proof body, specializing Fin2/h8 only at the end; lowering both branches isolates mode one and kills mode two. No source options or top-level helpers were added.

## Two exact remaining obligations

1. A07 quartic_sea_wick_identity: latest complete-looking scratch candidate closes fifteen sea cases and has one unsolved annihilator-order case. It is NOT integrated. The exact goal, CAR finishing step and resource diagnosis are preserved in `local-phaseB-quartic-checkpoint-2026-10-14.md` in the flat packet folder. Latest source there is `local-phaseB-quartic.lean` and compiler output `local-phaseB-quartic-12.log`. The last run used CLI maxHeartbeats=800000; default validation remains required. Generic eq_comm was replaced by specialized band predicate symmetry after exposing a resource blowup. No top-level resource option/interface mutation is allowed silently.
2. CH17 free_fermion_eq_sugawara_on_budget: preserve K≤M and K+|N|<h. Existing Core only supplies2K+|N|≤h, so cannot directly close this sharper contract. New supported route: full finite positive-current sum equals computational momentum minus N(N+1)/2 globally. Exact integer CAR checks passed every occupation at h1..5 (sanity only). Prove full-transfer sea-Wick sum=0 via universal physical-creator antisymmetry; combine the verified aggregate with Qfull=2P−N, then cutoff-reduce modes>M≥K by budget lowering. Prototype/last scalar and index-conditional diagnostics: `local-phaseB-antisym.lean` and `local-phaseB-antisym-3.log`; exact analysis `local-phaseB-sharp-sugawara-checkpoint.md`. Not a proved helper or accepted interface amendment.

## Resume and finish sequence

Recheck live allowance, checkout/packet identities and strict locks. Continue from this branch, not original placeholders. Finish the last quartic case, compile under the installed default resource configuration with warningAsError, and freshly audit all A07 dependencies. Serialize the complete A07 source with unchanged packet_id/base_sha and accept it through make lean-finish-phaseB 17. Preserve unrelated primary changes during integration. Prepare a fresh next B packet and submit the already proved A10 source, repeat for CH17 once its sharp bridge is proved. Only after every reachable staging dependency has zero placeholders/warnings and standard axioms proceed through authorized Phase C: promotion, scoped lock migration, independent pedagogical-sync review, CI and scoped commits/pushes. No Phase C work has happened yet; do not claim runner acceptance from this checkpoint.

## Usage guard

Live five-hour reading:91% used/9% remaining; weekly61% used/39% remaining. Formalizer guard requires stopping new proof work below10% five-hour or5% weekly remaining. All agents stopped immediately and saved completed work/current goals. Reported next five-hour reset: October14,2026 15:42:53 America/Fortaleza. No reset credit spent, no autonomous wakeup scheduled. The authorization to finish B then C persists on resumption.

## Fresh combined compiler and axiom output

```text
/home/lucas/Projects/.packets/worktrees/ch17-phase-b/scratch/resume-checkpoint-audit.lean:343:6: warning: declaration uses `sorry`
/home/lucas/Projects/.packets/worktrees/ch17-phase-b/scratch/resume-checkpoint-audit.lean:1700:8: warning: declaration uses `sorry`
'Bosonize.A07Interactions.hyperbolic_params_exist' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.sea_normal_bilinear_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.sea_normal_rho_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.sea_normal_rho_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.quartic_sea_wick_identity' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.quartic_sea_wick_zero_repeated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.species_raw_intra_eq_current_sub_correction' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'Bosonize.A07Interactions.raw_intra_eq_current_sub_correction' depends on axioms: [propext,
 sorryAx,
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
'Bosonize.Ch17.free_fermion_eq_sugawara_on_budget' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch17.luttinger_hamiltonian_on_budget' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch17.luttinger_hamiltonian_canonical_mu_on_budget' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'Bosonize.Ch17.luttinger_raw_intra_on_budget' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
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
