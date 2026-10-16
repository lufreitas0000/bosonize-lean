# Bosonize/Core/Ch19Correlations.lean

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


Phase B finish evidence: `note/webllm/ch19/phaseB-ch19_cycle_b_b8be9c21.md`.

## Phase C declaration and migration audit (2026-10-16)

### Exact source and data declarations

- Reviewed Phase B source: `BosonizeStubs/Ch19Correlations.lean`, SHA-256 `cc2eee0d9a5c53cf9a9e7b9a48998fd8de90d4b17f8359003b957bb7214e1687`.
- Promoted source: `Bosonize/Core/Ch19Correlations.lean`, SHA-256 `845e95b619fca515b25c2a103071ba1fa0fdfa46ddd12081440ddfbdae902339`.
- The five data declarations are `densityKernel` (ordered finite mode kernel), `oscDensityR` (oscillator-algebra density), `orderedDensityCorrelation` (evaluation in `omegaP`), `freePair` (zero-squeeze parameters), and `fockDensityR` (finite CAR Fock density operator).

### Theorem-to-role map

All 27 theorem contracts are included below.

| Theorem declarations | Proved role |
| --- | --- |
| `omegaP_creator_annihilator_right`, `omegaP_annihilator_creator_right`, `omegaP_creator_creator_right`, `omegaP_annihilator_annihilator_right` | Two ordered same-branch contractions and the corresponding same-branch zeros. |
| `omegaP_cross_creator_creator`, `omegaP_cross_annihilator_annihilator`, `omegaP_cross_creator_annihilator` | Cross-branch contractions and the sign-sensitive squeeze terms. |
| `ordered_density_kernel`, `ordered_density_kernel_lattice`, `density_commutator_expectation` | Ordered finite kernel, primitive-root lattice form, and its commutator antisymmetry, with nonzero phase assumptions. |
| `symmetrized_density_kernel`, `s_sq_eq_luttinger`, `c_sq_eq_luttinger` | Separate symmetrized kernel and the parameter identities. |
| `density_kernel_diagonal`, `density_kernel_diagonal_pos`, `ordered_density_free` | Exact finite diagonal, strict positivity when `h > 0` and `M ≥ 1`, and the zero-squeeze kernel. |
| `ground_lowering_raising`, `ground_raising_lowering`, `ground_raising_raising`, `ground_lowering_lowering` | Finite Fock ground contractions, under explicit positivity, admissibility, mode-cutoff and zero-margin hypotheses. |
| `excited_ket_norm_sq`, `ground_dressed_number`, `ground_dressed_reverse`, `ground_not_dressed_vacuum` | Excitation norm and both dressed-number orders under branch margins; nonzero expectation witnesses that the bare ground is not a dressed vacuum. |
| `fock_ground_density_kernel`, `fock_ground_matches_free_state`, `concrete_correlation_witness` | Finite ground kernel, scalar equality to the free oscillator kernel at zero squeeze only, and explicit exact witnesses. |

The declaration map is complementary to the A08 notebook's complete 62-contract axiom audit. The comparison theorem asserts equality of one scalar kernel under its stated hypotheses; it does not identify the oscillator functional with a finite Fock state.

### Fresh checks and independent review

- Fresh local `lake build Bosonize BosonizeStubs` on 2026-10-16 passed (3420 jobs). The output contains two tactic-suggestion informational messages from existing frozen dependencies; the CH19/A08 sources emitted no warning diagnostic.
- Fresh strict stub lock passed with 968 statement locks and 1020 frozen commands. The Core lock passed with 33 complete source hashes after adding A08 and CH19.
- Independent pedagogical review: PASS (2026-10-16). The reviewer confirmed the carrier and claim boundaries against the sources and accepted the fresh/historical build-count clarification.
- Independent import/path migration review: PASS (2026-10-16). The reviewer verified the A08 Core import replacement, aggregator ordering, unchanged declaration hashes, recomputed dependent contexts and no missing dependency.

### Exact migration delta

- Source path: `BosonizeStubs/Ch19Correlations.lean` → `Bosonize/Core/Ch19Correlations.lean`.
- Imports: the sole source change replaces `import BosonizeStubs.A08OscillatorStates` with `import Bosonize.Core.A08OscillatorStates`; theorem and data declaration text is unchanged.
- Aggregators: `Bosonize.lean` imports A08 before CH19; `BosonizeStubs.lean` removes the two direct staging imports and continues to import `Bosonize`.
- v2 lock: path key moved; all 27 theorem hashes retained; only the affected import-command hash and declaration context hashes were updated.
- Core lock: this source hash was added; all previous Core source hashes are unchanged.
- Companion moved from `docs/companion/BosonizeStubs/Ch19Correlations.md` to this Core path.
