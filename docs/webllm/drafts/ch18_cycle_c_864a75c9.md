# CH18 Phase C synchronization and review candidate

## Proved scope

The accepted Phase B source `BosonizeStubs/Ch18Bogoliubov.lean` contains 34 complete theorem proofs and 21 data declarations (55 freshly audited declarations total) in namespace `Bosonize.Ch18`. All 34 contracts are proved with standard axioms only (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, `sorryAx`, `admit`, or `native_decide` occurs. The operator theorems are stated on the finite multispecies CAR Hilbert space `Bosonize.A05.FockSpace σ h` for an arbitrary finite, linearly ordered species type $\sigma$ (`{σ : Type*} [Fintype σ] [LinearOrder σ]`) equipped with a pair of distinct branches `branches : Bosonize.A06.Branches σ` (Right and Left) on the band $-h < k \le h$ ($L = 2h$). Only the concrete witness specializes to $\sigma = \mathrm{Fin}\; 2$ with `Ch16.standardBranches`.

### Data declarations (21 declarations)

| Declaration | Type / Structure | Role |
| --- | --- | --- |
| `HyperbolicPair` | `structure` | Bundles real scalars $c, s \in \mathbb{R}$ with proof field `hyperbolic_id : c^2 - s^2 = 1`. |
| `HyperbolicPair.ofParams` | `def` | Projects hyperbolic scalars from `A07Interactions.HyperbolicParams v1 v2`. |
| `luttingerG` | `def` | Dimensionless Luttinger parameter $g := (c - s)^2$. |
| `luttingerGInv` | `def` | Inverse Luttinger parameter $g^{-1} := (c + s)^2$. |
| `LuttingerParams` | `abbrev` | Abbreviation for `Bosonize.A07Interactions.HyperbolicParams v1 v2`. |
| `LuttingerParams.toHyperbolicPair` | `def` | Coercion from `LuttingerParams` to `HyperbolicPair`. |
| `vacuumShiftScalar` | `noncomputable def` | Finite normal-ordering shift scalar $\Delta E_{\mathrm{vac}} = \frac{2\pi}{2h} \sum_{m=1}^M 2us^2m$. |
| `concreteV1` | `def` | Forward velocity parameter $v_1 = 17$ for explicit witness. |
| `concreteV2` | `def` | Coupling velocity parameter $v_2 = 15$ for explicit witness. |
| `concreteVF` | `noncomputable def` | Fermi velocity $v_F = 1$ for explicit witness. |
| `concreteG4` | `noncomputable def` | Intra-branch coupling $g_4 = 32\pi$ for explicit witness. |
| `concreteG2` | `noncomputable def` | Inter-branch coupling $g_2 = 30\pi$ for explicit witness. |
| `concreteCarrierH` | `def` | Half-band size $h = 8$ for explicit witness. |
| `concreteCutoff` | `def` | Mode cutoff $M = 2$ for explicit witness. |
| `concreteBudget` | `def` | Total energy budget $K = 2$ for explicit witness. |
| `concreteMode` | `def` | Retained mode index $m = 2$ for explicit witness. |
| `concreteNs` | `def` | Sector charge assignment $N_R = N_L = 0$ for explicit witness. |
| `concreteBranches` | `def` | Standard distinct branches `standardBranches` on `Fin 2`. |
| `concreteParams` | `noncomputable def` | Proved `HyperbolicParams 17 15` record with $u=8, c=5/4, s=3/4$. |
| `concretePair` | `noncomputable def` | Proved `HyperbolicPair` record from `concreteParams`. |
| `dressedOscillatorOp` | `noncomputable def` | Dressed oscillator sum operator $\frac{2\pi}{2h} \sum_{m=1}^M \text{dressedModeNumber}$. |

### Proved theorem contracts (34 theorems)

| Declaration | Mathematical Content | Scope / Hypotheses |
| --- | --- | --- |
| `HyperbolicPair.mul_eq_one` | $(c - s)(c + s) = 1$ | Scalar algebraic identity from $c^2 - s^2 = 1$. |
| `HyperbolicPair.c_sub_s_ne_zero` | $c - s \ne 0$ | Non-degeneracy lemma. |
| `HyperbolicPair.c_add_s_ne_zero` | $c + s \ne 0$ | Non-degeneracy lemma. |
| `HyperbolicPair.inverse_combination` | $c(cX + sY) - s(cY + sX) = X$ | Carrier-generic module identity on any complex vector space. |
| `hyperbolic_params_nonempty` | $|v_2| < v_1 \implies \text{Nonempty}(HyperbolicParams)$ | Parameter existence with verified $c > 0$. |
| `tanh_relation_of_params` | $v_2(c^2 + s^2) = v_1(2cs)$ | Cross-multiplied form of $\tanh 2\xi = v_2 / v_1$. |
| `luttingerG_mul_inv` | $g \cdot g^{-1} = 1$ | Exact algebraic product identity. |
| `luttingerGInv_eq_inv` | $g^{-1} = (g)^{-1}$ | Reciprocal equality. |
| `luttingerG_mul_u_of_params` | $g \cdot u = v_1 - v_2$ | Parameter relation with renormalized velocity. |
| `luttingerGInv_mul_u_of_params` | $g^{-1} \cdot u = v_1 + v_2$ | Parameter relation with renormalized velocity. |
| `luttingerG_eq_sqrt_of_params` | $g = \sqrt{(v_1 - v_2)/(v_1 + v_2)}$ | Closed-form Luttinger parameter expression. |
| `luttingerG_pos_of_params` | $g > 0$ | Strict positivity from $c - s \ne 0$. |
| `luttingerGInv_pos_of_params` | $g^{-1} > 0$ | Strict positivity from $c + s \ne 0$. |
| `hyperbolic_coeff_eq_luttinger` | $c^2 + s^2 = (g + g^{-1})/2$ | Hyperbolic coefficient relation. |
| `v2_eq_zero_iff_s_eq_zero` | $v_2 = 0 \iff s = 0$ | Characterization of non-interacting limit. |
| `u_lt_v1_of_v2_ne_zero` | $v_1 > 0 \wedge v_2 \ne 0 \implies u < v_1$ | Physical velocity reduction by mixing. |
| `vacuum_shift_prefactor_of_params` | $2us^2 = v_1 - u$ | Scalar normal-ordering shift prefactor. |
| `concrete_velocity_match` | $v_1 = v_F + g_4/2\pi \wedge v_2 = g_2/2\pi$ | Witness velocities match physical formulas. |
| `concreteParams_s_ne_zero` | $s \ne 0$ for witness | Explicit non-trivial mixing check ($s = 3/4$). |
| `bogoliubov_creator_inverse_right` | $\rho_{m,R} = c \tilde{C}_R - s \tilde{A}_L$ | Global operator inversion on ambient Fock space. |
| `bogoliubov_creator_inverse_left` | $\rho_{m,L} = c \tilde{C}_L - s \tilde{A}_R$ | Global operator inversion on ambient Fock space. |
| `bogoliubov_annihilator_inverse_right` | $\rho_{-m,R} = c \tilde{A}_R - s \tilde{C}_L$ | Global operator inversion on ambient Fock space. |
| `bogoliubov_annihilator_inverse_left` | $\rho_{-m,L} = c \tilde{A}_L - s \tilde{C}_R$ | Global operator inversion on ambient Fock space. |
| `bogoliubov_cross_annihilator_creator` | $[\tilde{A}_\eta, \tilde{C}_{\bar\eta}] = 0$ | Global operator commutator on ambient Fock space. |
| `bogoliubov_cross_creator_creator_on_budget` | $[\tilde{C}_R, \tilde{C}_L] v = 0$ | Cross-branch commutator on `jointBudget` under `branchMargins`. |
| `bogoliubov_cross_annihilator_annihilator_on_budget` | $[\tilde{A}_R, \tilde{A}_L] v = 0$ | Cross-branch commutator on `jointBudget` under `branchMargins`. |
| `luttinger_oscillator_dressed_on_budget` | Oscillator op equals dressed sum minus shift | Mode sum on `jointBudget` under `branchMargins`. |
| `luttinger_hamiltonian_dressed_on_budget` | Full Hamiltonian equals dressed sum plus zero modes minus shift | Interacting model on `jointBudget` under `branchMargins` and `sugawaraMargin`. |
| `dressed_annihilator_ground_right` | $\tilde{A}_R |0\rangle = s \cdot \text{excitedKet}_L(m)$ | Constructive action on sector ground ket $|0\rangle$. |
| `dressed_annihilator_ground_left` | $\tilde{A}_L |0\rangle = s \cdot \text{excitedKet}_R(m)$ | Constructive action on sector ground ket $|0\rangle$. |
| `dressed_annihilator_ground_right_ne_zero` | $\tilde{A}_R |0\rangle \ne 0$ for $s \ne 0$ | Non-zero excitation under `marginAt`. |
| `dressed_annihilator_ground_left_ne_zero` | $\tilde{A}_L |0\rangle \ne 0$ for $s \ne 0$ | Non-zero excitation under `marginAt`. |
| `no_common_bare_dressed_vacuum` | No non-zero budget state annihilated by both bare and dressed modes | Minimal finite obstruction theorem under `branchMargins`. |
| `concrete_bogoliubov_witness` | 12-conjunction witness at $(17,15,8,5/4,3/4)$ | Full non-vacuous realization witness. |

## Evidence

Fresh compiler and axiom audits are recorded in `note/webllm/ch18/phaseB-ch18_cycle_b_0648ad0f.md`. The Phase B verification transaction audited all 55 declarations in `BosonizeStubs/Ch18Bogoliubov.lean` with `warning-as-error` enabled:
1. Target source: `BosonizeStubs/Ch18Bogoliubov.lean` (SHA-256: `b55da072fac73055173cd65e584751caabdd02f2473648725b09e11c6fbc314b`).
2. Axiom dependencies: all 55 audited declarations depend strictly on standard Lean axioms `propext`, `Classical.choice`, `Quot.sound`, or no axioms (`concreteCarrierH`, `concreteCutoff`, `concreteBudget`, `concreteMode`, `concreteNs`). Nonstandard axioms, `sorryAx`, and native decision procedures are absent.
3. CI suite: passes 69 statement-freeze tests, 15 artifact/proof tests, Core build (3415 jobs), staging build (3417 jobs), 906 statements and 977 frozen commands verified in `stub_lock`, and 30 Core files in `core_lock`.
4. Review trail:
   - Phase A: Reviewer 1 FAIL (B1, B2); Reviewer 2 CHANGES_REQUIRED (adds A1); Revision round 2 (`gpt-5.4`, re-emitted by `gpt-5.4-mini`); Reviewer 1 round 2 PASS. Mirrored under `docs/webllm/reviews/ch18_phase_a/`.
   - Phase B: User finish recorded in `note/webllm/ch18/phaseB-ch18_cycle_b_0648ad0f.md`.
   - Phase C: Pedagogical candidate prepared following `pedagogical-sync` skill.

## Pedagogical changes

This candidate updates the chapter lecture note `notes/md/ch18_bogoliubov.md`, the shared interactions appendix `notes/appendices/a07_interactions_and_bogoliubov.md`, and the companion notebook `docs/companion/BosonizeStubs/Ch18Bogoliubov.md`:
1. *Preservation of reference theory:* All original definitions, formulas, citations, and Chapter 17 portions in Appendix A07 are preserved verbatim. Earlier proof-strategy sections are retained and identified as earlier proposals.
2. *Constructive realization:* Added Section 18.5 in `notes/md/ch18_bogoliubov.md` and synchronized the constructive realization in Appendix A07, explaining carriers, budgets, exact theorem statements, global versus budget-only operator identities, constructive ground-ket actions, and the explicit witness $(17,15,8,5/4,3/4)$.
3. *Companion synchronization:* Updated `docs/companion/BosonizeStubs/Ch18Bogoliubov.md` with the Phase B completion status, a complete declaration mapping table for all 34 theorems, verification and review provenance, while preserving the existing Phase A review tasks verbatim.
4. *Resolution of tracked review warnings:*
   - **CH18-N2b**: Resolved in Remark 18.5a in prose: physical interpretation that $g < 1 \iff v_2 > 0$ for repulsive interactions, with non-interacting fermions at $g = 1 \iff v_2 = 0$.
   - **CH18-N3**: Resolved in Remark 18.6a in prose: derived closed-form vacuum shift $\Delta E_{\mathrm{vac}} = \frac{2\pi}{2h}(v_1 - u)\frac{M(M+1)}{2}$ from `vacuumShiftScalar` and the proved prefactor relation $2us^2 = v_1 - u$, with $2us^2 \ge 0$ and $\Delta E_{\mathrm{vac}} > 0 \iff v_2 \ne 0$.
   - **CH18-N13**: Cited `Bosonize.A07Interactions.bogoliubov_creator_adjoint` for ledger item c07 (Hilbert space adjoint $\tilde{\rho}_{m,\eta}^\dagger = \tilde{\rho}_{-m,\eta}$).
   - **CH18-N14**: Explicitly classified global operator theorems (`HyperbolicPair.inverse_combination`, four inverse transforms, `bogoliubov_cross_annihilator_creator`, `bogoliubov_creator_adjoint`) versus budget-restricted theorems (`bogoliubov_cross_creator_creator_on_budget`, `bogoliubov_cross_annihilator_annihilator_on_budget`, `luttinger_oscillator_dressed_on_budget`, `luttinger_hamiltonian_dressed_on_budget`, `bogoliubov_ccr_on_budget`, `bogoliubov_expansion_on_budget`, `no_common_bare_dressed_vacuum`).

## Remaining limitations

1. The verified Hamiltonian identity is an operator action equality on the finite subspace `jointBudget h Ns K` under `branchMargins` ($2M + K + |N_\nu| \le h$), not a spectral theorem or unitary equivalence of operators.
2. The chosen pairing model diagonalized here is distinct from the raw finite inter-branch interaction (which reduces to hopping); identifying pairing with a physical backscattering channel requires an external orientation/momentum dictionary.
3. No global CCR algebra automorphism or unitary implementer $U = e^{iS}$ is constructed on finite Fock space (ruled out by finite-dimensional no-go theorems).
4. No interacting dressed vacuum vector $|\tilde{0}\rangle$ exists on finite Fock space; the bare and dressed vacua are mutually obstructed on the current-action regime (`no_common_bare_dressed_vacuum`).
5. Schrieffer-Wolff energy-shell decimation is a discrete projection on total energy shells, distinct from continuum Wilsonian RG flow or single-mode decimation.
