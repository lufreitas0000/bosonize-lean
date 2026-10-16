# Bosonize/Core/A08OscillatorStates.lean

- Carrier review tasks:
  - verify polynomial pairing well-foundedness and non-degeneracy (`oscPairing_self_eq_zero`);
  - check that `oscWeight` values are strictly positive ($m = i.val + 1 \ge 1$) so no infinite-dimensional slice is created;
  - confirm adjointness `oscCreation_pairing_adjoint` and commutator $[A, C] = m I$ algebraically on polynomials.
- State and automorphism review tasks:
  - trace $\omega_0$ definition as vacuum state evaluation $\langle 1, \pi(a) 1 \rangle$;
  - verify that $\beta_{c,s}$ satisfies $(c^2 - s^2 = 1) \iff \beta_{c,s} \circ \beta_{c,-s} = \text{id}$ on non-empty mode sets (`bogoliubovMap_inverse_iff`);
  - verify the pullback direction $\omega_P = \omega_0 \circ \beta_{c,-s}$ so that dressed lowering operators annihilate the vacuum, and $\omega_P \circ \beta_{c,s} = \omega_0$ (`omegaP_comp_bogoliubovMap`);
  - confirm full quotient descent on all relation pairs: $[A, C] - m I$, $[A, A]$, and $[C, C]$ for both bare $\omega_0$ and dressed $\omega_P$;
  - confirm that the non-multiplicativity witness $\omega_P(A C) - \omega_P(C A) = m$ holds without assuming states are homomorphisms.
- Contraction review tasks:
  - calculate both same-branch contractions: $m s^2$ for $CA$ and $m c^2$ for $AC$;
  - check that $c^2$ remains non-zero even when $s = 0$ (free vacuum fluctuations);
  - check that cross-branch contractions have the exact $-\delta_{ij} m c s$ sign, sensitive to $\beta$ direction.
- Correlation kernel review tasks:
  - verify that $D(x,y) = L^{-2} \sum m (s^2 \zeta^{-md} + c^2 \zeta^{md})$ preserves the ordered observable and does not collapse into a cosine;
  - verify that the commutator expectation $D(x,y) - D(y,x)$ matches the $(1, -1)$ Schwinger kernel;
  - check diagonal positivity $0 < (D(x,x)).re$ under the required condition $\zeta \neq 0$ for $h > 0$ and $M \ge 1$.
- Compressed vacuum review tasks:
  - confirm $Q_R^\dagger Q_R + Q_L^\dagger Q_L = \operatorname{diag}(2s^2, c^2, c^2)$ matrix identity;
  - confirm that $s \neq 0$ implies strict positivity and trivial common kernel $\{0\}$;
  - confirm that $s = 0$ admits non-trivial kernel $(1, 0, 0)^T$, showing necessity of $s \neq 0$ for obstruction.
- Witness review tasks:
  - verify arithmetic of all conjuncts in `concrete_correlation_witness` via `norm_num`;
  - check that Fock ground state expectation $\langle \Omega, \tilde{C}_R \tilde{A}_R \Omega \rangle = 9/8 \neq 0$ witnesses that the bare Fock vacuum is not the interacting dressed vacuum.

Phase A historical checkpoint: the interfaces were integrated after user review; proofs were still pending at this checkpoint.


Phase A finish evidence: `note/webllm/ch19/phaseA-ch19_cycle_a_e7c404b4.md`.


Phase B finish evidence: `note/webllm/ch19/phaseB-ch19_cycle_b_ac6d6ccf.md`.

## Phase C source and declaration audit (2026-10-16)

### Exact reviewed source snapshot

| Module | SHA-256 | Declarations | Theorem contracts | Constructive role |
| --- | --- | ---: | ---: | --- |
| `BosonizeStubs/A08OscillatorStates.lean` | `ed3ef9f87c9be26460004fd52efbdd7f0a2490b544c990cc89e6178f0a97ee35` | 58 | 35 | Polynomial oscillator pairing and representation, positive normalized word functionals, Bogoliubov pullback, finite vector-state facts, and the explicit compressed-vacuum obstruction. |
| `BosonizeStubs/Ch19Correlations.lean` | `cc2eee0d9a5c53cf9a9e7b9a48998fd8de90d4b17f8359003b957bb7214e1687` | 32 | 27 | Ordered oscillator contractions and density kernels, symmetrization and diagonal bounds, finite-Fock ground contractions, the zero-squeeze scalar comparison, and concrete witnesses. |

The source snapshot is the same as the accepted Phase B record. A08's 23 data declarations are `OscMode`, `oscWeight`, `OscPoly`, `oscMonomialNorm`, `oscPairing`, `oscCreation`, `oscAnnihilation`, `OscGen`, `OscAlgebra`, `creatorGen`, `annihilatorGen`, `oscRep`, `omega0`, `bogoliubovMap`, `omegaP`, `OscWord`, `wordDagger`, `wordElement`, `gramSum`, `vectorState`, `compressedQR`, `compressedQL`, and `noteCompressedPair`. Ch19's five data declarations are `densityKernel`, `oscDensityR`, `orderedDensityCorrelation`, `freePair`, and `fockDensityR`.

### Theorem-to-role map

Every theorem contract in the two accepted modules is covered below; line numbers refer to the exact source snapshot above.

| Source declarations | Role in the construction |
| --- | --- |
| A08 `oscPairing_monomial`, `oscPairing_conj`, `oscPairing_self_nonneg`, `oscPairing_self_eq_zero`, `oscCreation_pairing_adjoint`, `osc_ccr`, `osc_annihilators_commute`, `osc_creators_commute`, `oscAnnihilation_one` (lines 59–265) | Positive nondegenerate weighted polynomial pairing; generator adjointness; oscillator commutation and vacuum action. |
| A08 `omega0_eq_pairing`, `omega0_one`, `omega0_gramSum`, `omega0_ccr_descends`, `omega0_ccr_descends_aa`, `omega0_ccr_descends_cc` (266–430) | Bare vacuum evaluation, normalization, word-Gram positivity and annihilation/creator relation descent. |
| A08 `bogoliubovMap_inverse`, `bogoliubovMap_inverse_rev`, `bogoliubovMap_inverse_iff`, `bogoliubovMap_word_adjoint` (431–579) | Inverse transformations and the pairing identity used to establish positivity after pullback. |
| A08 `omegaP_one`, `omegaP_gramSum`, `omegaP_ccr_descends`, `omegaP_ccr_descends_aa`, `omegaP_ccr_descends_cc`, `omegaP_comp_bogoliubovMap`, `omegaP_mul_dressed_annihilator`, `omegaP_dressed_creator_mul`, `omegaP_commutator` (580–997) | Normalized positive dressed functional, relation descent, pullback identity, dressed vacuum equations and nonmultiplicativity witness. |
| A08 `vectorState_ground_one`, `vectorState_adjoint_mul_self` (1001–1014) | Normalization and positivity for the finite Fock vector functional. |
| A08 `compressed_gram`, `compressed_common_kernel_trivial`, `compressed_no_vacuum_density`, `compressed_kernel_of_s_zero`, `note_compressed_witness` (1024–1100) | Gram identity and exact common-kernel/density obstruction for the specified three-dimensional compression; the zero-squeeze kernel records necessity of the nonzero-squeeze hypothesis. |
| Ch19 `omegaP_creator_annihilator_right`, `omegaP_annihilator_creator_right`, `omegaP_creator_creator_right`, `omegaP_annihilator_annihilator_right`, `omegaP_cross_creator_creator`, `omegaP_cross_annihilator_annihilator`, `omegaP_cross_creator_annihilator` (24–384) | Both same-branch ordered contractions, same-branch zeros and cross-branch contractions with their signs. |
| Ch19 `ordered_density_kernel`, `ordered_density_kernel_lattice`, `density_commutator_expectation`, `symmetrized_density_kernel`, `s_sq_eq_luttinger`, `c_sq_eq_luttinger`, `density_kernel_diagonal`, `density_kernel_diagonal_pos`, `ordered_density_free` (385–679) | Exact finite oscillator kernels, primitive-root translation, commutator, symmetrization, parameter conversion, diagonal positivity and the free case. |
| Ch19 `ground_lowering_raising`, `ground_raising_lowering`, `ground_raising_raising`, `ground_lowering_lowering`, `excited_ket_norm_sq`, `ground_dressed_number`, `ground_dressed_reverse`, `ground_not_dressed_vacuum` (686–891) | Finite-Fock contractions and excitation norm under explicit mode, budget, admissibility and branch-margin hypotheses; nonzero interacting dressed-number witness. |
| Ch19 `fock_ground_density_kernel`, `fock_ground_matches_free_state`, `concrete_correlation_witness` (892–1017) | Finite ground density kernel, scalar equality with the oscillator free state at zero squeeze only, and checked numerical witnesses. |

### Fresh Phase C checks

- `python3 scripts/guards/stub_lock.py --check --strict`: passed, 968 statement locks and 1020 frozen commands checked.
- Before promotion, `python3 scripts/guards/core_lock.py` passed with 31 existing Core sources; after adding the two reviewed modules, the fresh check passed with 33 complete Core sources.
- Fresh local run on 2026-10-16, `lake build Bosonize BosonizeStubs`: passed, 3420 jobs. The historical Phase B receipt records its separate build as 3419 jobs. The only output beyond build progress in the fresh run was informational tactic-suggestion text from two already frozen Core files; Lean emitted no warning diagnostic for the CH19/A08 sources.
- The accepted Phase B fresh audit in `note/webllm/ch19/phaseB-ch19_cycle_b_b8be9c21.md` lists all 62 theorem contracts. Each depends only on `propext`, `Classical.choice`, and `Quot.sound`; no project-specific axiom appears. The source files contain no remaining `sorry` or `admit` placeholders.

### Scope carried into pedagogy

The oscillator word algebra and finite CAR Fock space remain distinct. Only the scalar density-kernel equality at zero squeeze is proved between them, under the source theorem's hypotheses. The appendix's charge extension, formal Weyl-type vertices, coefficientwise Gaussian series, general Wick tables and finite interacting-state comparisons are not in these two modules. General-orientation contraction tables remain tracked by CH19-N2 for CH20b; no analytic limit, power law or evaluation at formal parameter `t=1` is claimed.

### Independent review and promotion migration

- Independent pedagogical review: PASS (2026-10-16). The reviewer checked the note and appendix against both current Lean sources, verified preservation of the existing exposition, and found no remaining mathematical or scope corrections. The build-count clarification above was accepted.
- Independent import/path migration review: PASS (2026-10-16). The reviewer confirmed that this module already depends on promoted `Bosonize.Core.Ch18Bogoliubov`, needs no import change, and has no omitted dependency.
- Promoted path: `Bosonize/Core/A08OscillatorStates.lean`; source SHA-256 remains `ed3ef9f87c9be26460004fd52efbdd7f0a2490b544c990cc89e6178f0a97ee35`.
- The v2 lock entry moved from the staging path to the Core path with all 35 declaration hashes and all 30 command hashes unchanged. The complete source hash was added as one of two new entries in `docs/spec/core_locks.json`; the previous 31 Core hashes are unchanged.
- Companion moved from `docs/companion/BosonizeStubs/A08OscillatorStates.md` to `docs/companion/Bosonize/Core/A08OscillatorStates.md`.
- The pedagogical update appends a scoped constructive explanation while retaining the pre-existing appendix text and deferred formal-vertex material.
