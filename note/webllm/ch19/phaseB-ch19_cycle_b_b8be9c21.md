# CH19 Phase B: user-reviewed finish

Running finish records the user's approval of the downloaded content. No independent reviewer is claimed.

Packet: ch19_cycle_b_b8be9c21-20261015T072535Z-8355a5de

Base: 32dd4a3db3760a6f9961cd34ae76ba5fef8b1ec2

Response SHA-256: eb6c9b6e4dcc46b5a49abb60b8efabfe8ff6b37768d82cbf2b80cc780269b6d0

Candidate commit: 5e8273506ce0a35be57709c22ec55af8e1519fc3

Model label: chatgpt-chat-high

## Source evidence
- BosonizeStubs/Ch19Correlations.lean: cc2eee0d9a5c53cf9a9e7b9a48998fd8de90d4b17f8359003b957bb7214e1687

## verify-1.log
```text
[stub_lock] Verification PASSED: 968 statement(s) and 1020 frozen command(s) verified.
[core_lock] Verified 31 complete Core source file(s).
ℹ [3403/3416] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
ℹ [3411/3416] Replayed Bosonize.Core.A07InteractionsAndBogoliubov
info: Bosonize/Core/A07InteractionsAndBogoliubov.lean:375:2: Try this:
  [apply] abel_nf
Build completed successfully (3416 jobs).
'Bosonize.A08.oscPairing_monomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.oscPairing_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.oscPairing_self_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.oscPairing_self_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.oscCreation_pairing_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.osc_ccr' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.osc_annihilators_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.osc_creators_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.oscAnnihilation_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.omega0_eq_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.omega0_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.omega0_gramSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.omega0_ccr_descends' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.omega0_ccr_descends_aa' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.omega0_ccr_descends_cc' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.bogoliubovMap_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.bogoliubovMap_inverse_rev' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.bogoliubovMap_inverse_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.bogoliubovMap_word_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.omegaP_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.omegaP_gramSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.omegaP_ccr_descends' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.omegaP_ccr_descends_aa' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.omegaP_ccr_descends_cc' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.omegaP_comp_bogoliubovMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.omegaP_mul_dressed_annihilator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.omegaP_dressed_creator_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.omegaP_commutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.vectorState_ground_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.vectorState_adjoint_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.compressed_gram' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.compressed_common_kernel_trivial' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.compressed_no_vacuum_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.compressed_kernel_of_s_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.note_compressed_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.OscMode' does not depend on any axioms
'Bosonize.A08.oscWeight' does not depend on any axioms
'Bosonize.A08.OscPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.oscMonomialNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.oscPairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.oscCreation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.oscAnnihilation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.OscGen' does not depend on any axioms
'Bosonize.A08.OscAlgebra' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.creatorGen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.annihilatorGen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.oscRep' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.omega0' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.bogoliubovMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.omegaP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.OscWord' does not depend on any axioms
'Bosonize.A08.wordDagger' does not depend on any axioms
'Bosonize.A08.wordElement' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.gramSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.vectorState' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.compressedQR' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.compressedQL' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A08.noteCompressedPair' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS: BosonizeStubs/A08OscillatorStates.lean, 58 freshly audited declarations
'Bosonize.Ch19.omegaP_creator_annihilator_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.omegaP_annihilator_creator_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.omegaP_creator_creator_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.omegaP_annihilator_annihilator_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.omegaP_cross_creator_creator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.omegaP_cross_annihilator_annihilator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.omegaP_cross_creator_annihilator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.ordered_density_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.ordered_density_kernel_lattice' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.density_commutator_expectation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.symmetrized_density_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.s_sq_eq_luttinger' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.c_sq_eq_luttinger' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.density_kernel_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.density_kernel_diagonal_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.ordered_density_free' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.ground_lowering_raising' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.ground_raising_lowering' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.ground_raising_raising' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.ground_lowering_lowering' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.excited_ket_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.ground_dressed_number' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.ground_dressed_reverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.ground_not_dressed_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.fock_ground_density_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.fock_ground_matches_free_state' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.concrete_correlation_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.densityKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.oscDensityR' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.orderedDensityCorrelation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.freePair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch19.fockDensityR' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS: BosonizeStubs/Ch19Correlations.lean, 32 freshly audited declarations

```

## Final ci.log
```text
make[1]: Entering directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch19-B-5b975db5'
./scripts/ci.sh
== Testing the statement-freeze guard ==
.....................................................................
----------------------------------------------------------------------
Ran 69 tests in 1.412s

OK
== Checking frozen chapter definitions and statements ==
[stub_lock] Verification PASSED: 968 statement(s) and 1020 frozen command(s) verified.
== Checking complete frozen Core sources ==
[core_lock] Verified 31 complete Core source file(s).
== Building Bosonize (Core) ==
✔ [3384/3416] Built Bosonize.Core.Ch01LatticeBand (1.5s)
✔ [3385/3416] Built Bosonize.Core.Ch02UmbralCalculus (2.2s)
✔ [3386/3416] Built Bosonize.Core.A01FourierCharacters (2.5s)
✔ [3387/3416] Built Bosonize.Core.A02CARHilbert (3.2s)
✔ [3388/3416] Built Bosonize.Core.Ch04CARFock (4.4s)
✔ [3389/3416] Built Bosonize.Core.Ch03Fourier (4.5s)
✔ [3390/3416] Built Bosonize.Core.A03EnergyBudgets (8.5s)
✔ [3391/3416] Built Bosonize.Core.Ch05Fermions (5.6s)
✔ [3392/3416] Built Bosonize.Core.A04DensityKinematics (9.3s)
✔ [3393/3416] Built Bosonize.Core.Ch06LocalNet (10s)
✔ [3394/3416] Built Bosonize.Core.Ch08Boson (13s)
✔ [3395/3416] Built Bosonize.Core.Ch07VacuumBudget (12s)
✔ [3396/3416] Built Bosonize.Core.A05FiniteExponentials (2.9s)
✔ [3397/3416] Built Bosonize.Core.A04PartitionCombinatorics (3.3s)
✔ [3398/3416] Built Bosonize.Core.Ch06Ext (6.2s)
✔ [3399/3416] Built Bosonize.Core.Ch09DensityModes (4.6s)
✔ [3400/3416] Built Bosonize.Core.A04CurrentMargins (3.4s)
✔ [3401/3416] Built Bosonize.Core.Ch10Heisenberg (4.3s)
✔ [3402/3416] Built Bosonize.Core.Ch11HaldaneCompleteness (10s)
✔ [3403/3416] Built Bosonize.Core.Ch12Sugawara (5.5s)
✔ [3404/3416] Built Bosonize.Core.A05MultiSpecies (8.6s)
ℹ [3405/3416] Built Bosonize.Core.Ch13KleinFactors (4.0s)
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3406/3416] Built Bosonize.Core.Ch14Mandelstam (9.2s)
✔ [3407/3416] Built Bosonize.Core.A06ChiralFields (10s)
✔ [3408/3416] Built Bosonize.Core.Ch15DualFields (3.6s)
✔ [3409/3416] Built Bosonize.Core.A07FiniteNormalOrdering (3.2s)
✔ [3410/3416] Built Bosonize.Core.Ch16FieldHamiltonian (7.7s)
ℹ [3411/3416] Built Bosonize.Core.A07InteractionsAndBogoliubov (38s)
info: Bosonize/Core/A07InteractionsAndBogoliubov.lean:375:2: Try this:
  [apply] abel_nf
✔ [3412/3416] Built Bosonize.Core.A10DiscreteSchriefferWolff (7.6s)
✔ [3413/3416] Built Bosonize.Core.Ch17LuttingerModels (15s)
✔ [3414/3416] Built Bosonize.Core.Ch18Bogoliubov (8.0s)
✔ [3415/3416] Built Bosonize (2.5s)
Build completed successfully (3416 jobs).
== Building BosonizeStubs (Staging) ==
ℹ [3404/3419] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
ℹ [3411/3419] Replayed Bosonize.Core.A07InteractionsAndBogoliubov
info: Bosonize/Core/A07InteractionsAndBogoliubov.lean:375:2: Try this:
  [apply] abel_nf
✔ [3416/3419] Built BosonizeStubs.A08OscillatorStates (6.9s)
✔ [3417/3419] Built BosonizeStubs.Ch19Correlations (7.7s)
✔ [3418/3419] Built BosonizeStubs (2.4s)
Build completed successfully (3419 jobs).
== Testing the Web-LLM artifact/proof verifiers and axiom audit ==
.........[core_lock] Verified 31 complete Core source file(s).
[core_lock] Verified 31 complete Core source file(s).
......
----------------------------------------------------------------------
Ran 15 tests in 15.383s

OK
'Fixture.value' depends on axioms: [sorryAx]
PASS Markdown structure: /tmp/tmphou9ui5j/candidate.md; human evidence/prose review still required
CI OK
make[1]: Leaving directory '/home/lucas/Projects/.packets/cycle-worktrees/bosonize-lean/ch19-B-5b975db5'

```
