# Bosonize/Core/Ch18Bogoliubov.lean: Phase B complete; Phase C preparation

Status: 34 proved contracts and 21 complete data declarations in this module (55 freshly audited declarations total).
All accepted proofs have fresh standard-axiom evidence (`propext`, `Classical.choice`, `Quot.sound`).
Phase B finish evidence: [note/webllm/ch18/phaseB-ch18_cycle_b_0648ad0f.md](../../../../note/webllm/ch18/phaseB-ch18_cycle_b_0648ad0f.md).
Accepted staging source SHA-256: `b55da072fac73055173cd65e584751caabdd02f2473648725b09e11c6fbc314b`.
Planned promoted source: `Bosonize/Core/Ch18Bogoliubov.lean`.
Pedagogical mapping: [corresponding reference note](../../../../notes/md/ch18_bogoliubov.md) and [interactions appendix](../../../../notes/appendices/a07_interactions_and_bogoliubov.md).

## Exact proved declaration mapping

Every row below denotes a complete theorem proof in `Bosonize.Ch18`. Exact signatures, carrier instances, and hypotheses are preserved in the staging source `Bosonize/Core/Ch18Bogoliubov.lean`.

| Declaration | Realization and dependency scope |
| --- | --- |
| `HyperbolicPair.mul_eq_one` | $(c - s)(c + s) = 1$ derived from `c^2 - s^2 = 1`. |
| `HyperbolicPair.c_sub_s_ne_zero` | Non-degeneracy $c - s \ne 0$ from product identity. |
| `HyperbolicPair.c_add_s_ne_zero` | Non-degeneracy $c + s \ne 0$ from product identity. |
| `HyperbolicPair.inverse_combination` | Carrier-generic module identity $c(cX + sY) - s(cY + sX) = X$ on any complex vector space. |
| `hyperbolic_params_nonempty` | Parameter package existence with $u > 0, c > 0$ for any stable $|v_2| < v_1$. |
| `tanh_relation_of_params` | Algebraic cross-multiplied relation $v_2(c^2 + s^2) = v_1(2cs)$, corresponding to $\tanh 2\xi = v_2 / v_1$. |
| `luttingerG_mul_inv` | Exact algebraic reciprocal product $g \cdot g^{-1} = 1$. |
| `luttingerGInv_eq_inv` | Reciprocal equality $g^{-1} = (g)^{-1}$. |
| `luttingerG_mul_u_of_params` | Relation $g \cdot u = v_1 - v_2$ with renormalized velocity. |
| `luttingerGInv_mul_u_of_params` | Relation $g^{-1} \cdot u = v_1 + v_2$ with renormalized velocity. |
| `luttingerG_eq_sqrt_of_params` | Closed-form formula $g = \sqrt{(v_1 - v_2)/(v_1 + v_2)}$ without sign ambiguity. |
| `luttingerG_pos_of_params` | Strict positivity $g > 0$ from $c - s \ne 0$. |
| `luttingerGInv_pos_of_params` | Strict positivity $g^{-1} > 0$ from $c + s \ne 0$. |
| `hyperbolic_coeff_eq_luttinger` | Hyperbolic coefficient relation $c^2 + s^2 = (g + g^{-1})/2$. |
| `v2_eq_zero_iff_s_eq_zero` | Characterization of non-interacting limit: $v_2 = 0 \iff s = 0$. |
| `u_lt_v1_of_v2_ne_zero` | Physical velocity reduction $u < v_1$ for $v_1 > 0$ and $v_2 \ne 0$. |
| `vacuum_shift_prefactor_of_params` | Normal-ordering shift prefactor identity $2us^2 = v_1 - u$. |
| `concrete_velocity_match` | Evaluates $v_1 = v_F + g_4/2\pi$ and $v_2 = g_2/2\pi$ on witness $(1, 32\pi, 30\pi)$. |
| `concreteParams_s_ne_zero` | Strict non-zero mixing check $s = 3/4 \ne 0$ on concrete witness. |
| `bogoliubov_creator_inverse_right` | Global operator identity expressing $\rho_{m,R}$ in terms of dressed operators. |
| `bogoliubov_creator_inverse_left` | Global operator identity expressing $\rho_{m,L}$ in terms of dressed operators. |
| `bogoliubov_annihilator_inverse_right` | Global operator identity expressing $\rho_{-m,R}$ in terms of dressed operators. |
| `bogoliubov_annihilator_inverse_left` | Global operator identity expressing $\rho_{-m,L}$ in terms of dressed operators. |
| `bogoliubov_cross_annihilator_creator` | Global commutator $[\tilde{A}_\eta, \tilde{C}_{\bar\eta}] = 0$ on ambient Fock space. |
| `bogoliubov_cross_creator_creator_on_budget` | Cross-branch creator commutator $[\tilde{C}_R, \tilde{C}_L] v = 0$ on `jointBudget` under `branchMargins`. |
| `bogoliubov_cross_annihilator_annihilator_on_budget` | Cross-branch annihilator commutator $[\tilde{A}_R, \tilde{A}_L] v = 0$ on `jointBudget` under `branchMargins`. |
| `luttinger_oscillator_dressed_on_budget` | Mode sum over $m \in \{1,\dots,M\}$ equating oscillator op to dressed sum minus scalar shift on budget. |
| `luttinger_hamiltonian_dressed_on_budget` | Interacting Luttinger Hamiltonian equals dressed sum plus zero modes minus shift on `jointBudget`. |
| `dressed_annihilator_ground_right` | Constructive ground ket action $\tilde{A}_R |0\rangle = s \cdot \text{excitedKet}_L(m)$. |
| `dressed_annihilator_ground_left` | Constructive ground ket action $\tilde{A}_L |0\rangle = s \cdot \text{excitedKet}_R(m)$. |
| `dressed_annihilator_ground_right_ne_zero` | Non-zero ground excitation for $s \ne 0$ under `marginAt`. |
| `dressed_annihilator_ground_left_ne_zero` | Non-zero ground excitation for $s \ne 0$ under `marginAt`. |
| `no_common_bare_dressed_vacuum` | Minimal finite obstruction: no non-zero budget state is annihilated by both bare and dressed modes for $s \ne 0$. |
| `concrete_bogoliubov_witness` | 12-conjunction witness evaluating all properties at $(17,15,8,5/4,3/4)$. |

The operator theorems are stated on `Bosonize.A05.FockSpace σ h` for an arbitrary finite, linearly ordered species type $\sigma$ (`{σ : Type*} [Fintype σ] [LinearOrder σ]`) equipped with a pair of distinct branches `branches : Bosonize.A06.Branches σ` (Right and Left); only the concrete witness specializes $\sigma$ to `Fin 2` with `concreteBranches = standardBranches`.
The four inverse transforms and the cross-branch annihilator-creator commutator are **global operator identities** on `A05.Operators σ h`, relying only on $c^2 - s^2 = 1$ and `A05.rho_cross_commute` (resolving CH18-N14). The Hilbert space adjoint relation is proved in `A07Interactions.bogoliubov_creator_adjoint` (resolving CH18-N13).
In contrast, same-branch CCR, cross-branch creator-creator / annihilator-annihilator commutators, and the Hamiltonian diagonalization theorems are **budget-restricted action identities** requiring $v \in \text{jointBudget}$ under `branchMargins`.
The closed-form vacuum shift scalar $\Delta E_{\mathrm{vac}} = \frac{2\pi}{2h}(v_1 - u)\frac{M(M+1)}{2}$ is derived from `vacuumShiftScalar` and $2us^2 = v_1 - u$, with $2us^2 \ge 0$ and $\Delta E_{\mathrm{vac}} > 0 \iff v_2 \ne 0$ (resolving CH18-N3).
The physical interpretation $g < 1 \iff v_2 > 0$ for repulsive interactions is recorded as a derived remark (resolving CH18-N2b).
The non-vacuous witness $(17, 15, 8, 5/4, 3/4)$ with $h = 8, M = 2, K = 2, Ns = 0$ certifies non-triviality and non-zero ground ket action.

## Verification, review and Phase C boundary

Phase B completed with all 34 theorems proved and 21 data declarations (55 total declarations audited) under `warning-as-error` in `Bosonize/Core/Ch18Bogoliubov.lean`.
All 55 declarations depend exclusively on standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound` (or no axioms).
The Phase B CI run passed 69 statement-guard tests, 15 artifact/proof tests, Core build (3415 jobs), staging build (3417 jobs), 906 statements and 977 frozen commands verified in `stub_lock`, and 30 complete Core files in `core_lock`.
Independent review trail:
- Phase A: Reviewer 1 FAIL (B1, B2); Reviewer 2 CHANGES_REQUIRED (adds A1); Revision round 2 (`gpt-5.4`, re-emitted by `gpt-5.4-mini`); Reviewer 1 round 2 PASS. Mirrored under `docs/webllm/reviews/ch18_phase_a/`.
- Phase B: User finish recorded in `note/webllm/ch18/phaseB-ch18_cycle_b_0648ad0f.md`.
- Phase C: Pedagogical candidate prepared following `pedagogical-sync` skill. Promotion and lock migration remain runner-managed operations.

## Historical Phase A provenance

The original review notebook tasks are preserved verbatim below for provenance.

- Scalar review notebook tasks:
  - check that `luttingerG`, `luttingerGInv`, `g u = v1 - v2`, `g⁻¹ u = v1 + v2`, and `2us^2 = v1 - u` use only `HyperbolicParams` fields and never a hidden sign choice;
  - verify that `v2 = 0 ↔ s = 0` and `u < v1` really require the stated positivity hypotheses.
- Operator review notebook tasks:
  - expand the inverse transform with exact branch labels and signs;
  - derive the finite-sum dressed oscillator identity from the frozen per-mode theorem `A07Interactions.bogoliubov_expansion_on_budget` rather than from ad hoc commutation hypotheses;
  - combine that sum with `Ch17.luttinger_hamiltonian_on_budget` for the full Chapter 17 statement.
- Witness notebook tasks:
  - evaluate the explicit witness `(17,15,8,5/4,3/4)`;
  - confirm `Ch17.v1Velocity 1 (32π) = 17` and `Ch17.v2Velocity (30π) = 15`;
  - check `vacuumShiftScalar 8 2 8 (3/4) = 27π/8` and hence nonzero;
  - inspect that the dressed lowering action on the finite ground ket is nonzero because it lands on an explicit `Ch16.excitedKet` witness, not because a global dressed vacuum is assumed.
- SW review notebook tasks:
  - cite Core results `A10.energy_shell_discards_double_mode_one` and `A10.sw_off_zero_implies_effective_exact` when discussing shell projection;
  - keep the shell-vs-mode-decimation distinction conceptual and separate from the Bogoliubov diagonalization proof obligations above.

- Phase B review tasks added at Phase B start (review warning CH18-N15):
  - `tanh_relation_of_params`: with `cosh 2ξ = c² + s²` and `sinh 2ξ = 2cs`, check that `v2 (c² + s²) = v1 (2cs)` is the cross-multiplied form of `tanh 2ξ = v2 / v1` and needs no division by `v1`; witness `(c, s) = (5/4, 3/4)` gives `c² + s² = 17/8`, `2cs = 15/8`, and `15 · 17/8 = 17 · 15/8`.
  - `luttingerG_eq_sqrt_of_params`: `g = (c − s)²`; check that `v1 + v2 > 0` follows from the stability field `|v2| < v1` so the square root argument is well defined; witness `g = (1/2)² = 1/4 = √((17 − 15)/(17 + 15)) = √(1/16)`.
  - `luttingerGInv_eq_inv`: `(c + s)² (c − s)² = (c² − s²)² = 1`, so `luttingerGInv = g⁻¹` for every `HyperbolicPair` (no positivity needed); witness `4 = (1/4)⁻¹`.
  - `hyperbolic_coeff_eq_luttinger`: `c² + s² = (g + g⁻¹)/2` from `(c − s)² + (c + s)² = 2(c² + s²)`; witness `17/8 = (1/4 + 4)/2`.
  - `HyperbolicPair.inverse_combination`: `c(cX + sY) − s(cY + sX) = (c² − s²)X = X` on any complex module; compare the `X`/`Y` placement with the branch pairing in `A07Interactions.bogoliubovAnnihilator` / `bogoliubovCreator` before using it to invert the transform.
  - `bogoliubov_cross_annihilator_annihilator_on_budget`: expand `[Ã_R, Ã_L]` into four density commutators; check that the cross-species terms vanish by `A05.rho_cross_commute`, that the two same-branch terms cancel on the budget (opposite chiralities), and record which part of `A06.branchMargins` supplies the margin for indices `±m`.

Phase A integrated after user review. Theorems remain unproved.


Phase A finish evidence: `note/webllm/ch18/phaseA-ch18_cycle_a_6c99dd27.md`.


Phase B finish evidence: `note/webllm/ch18/phaseB-ch18_cycle_b_0648ad0f.md`.


Phase C finish evidence: `note/webllm/ch18/phaseC-ch18_cycle_c_864a75c9.md`.
