### Chapter 18: The Bogoliubov Transformation

To identify the true physical excitations of the Luttinger liquid, we must decouple the Right and Left moving density waves algebraically. This requires finding a new set of bosonic operators that diagonalize the pairing Hamiltonian matrix while preserving the underlying Kac-Moody algebra. The mathematical formalization strictly follows [Appendix A07](../appendices/a07_interactions_and_bogoliubov.md), [Appendix A08](../appendices/a08_states_and_correlations.md), and [Appendix A10](../appendices/a10_discrete_rg_and_schrieffer_wolff.md).

#### 18.1 The Hyperbolic Transformation

**Definition 18.1 (Algebraic Hyperbolic Parameters).**
We define the transformation purely algebraically. A hyperbolic pair consists of real scalars $c, s \in \mathbb{R}$ satisfying the exact identity:
$$
c^2 - s^2 = 1 \tag{18.1}
$$

*Lean 4 Proof Strategy:* Define a structure `HyperbolicPair` containing `c s : ℝ` and a proof field `hyperbolic_id : c^2 - s^2 = 1`. This structure bundles the scalars and their invariant, which can then be passed to the transformation functions. Typical algebraic consequences like $(c-s)(c+s)=1$ and $c \pm s \ne 0$ follow directly.

**Definition 18.2 (The Bogoliubov Transformation).**
For every mode $m \ge 1$, we define the new dressed creation and annihilation operators in $\mathrm{End}_{\mathbb{C}}(\mathrm{Fock})$:
$$
\tilde{\rho}_{m, R} := c \cdot \rho_{m, R} + s \cdot \rho_{-m, L} \tag{18.2}
$$
$$
\tilde{\rho}_{m, L} := s \cdot \rho_{-m, R} + c \cdot \rho_{m, L} \tag{18.3}
$$
By taking the adjoints with $c, s \in \mathbb{R}$ (proved in `Bosonize.A07Interactions.bogoliubov_creator_adjoint`, ledger item c07), the complementary lowering operators are exactly:
$$
\tilde{\rho}_{-m, R} := c \cdot \rho_{-m, R} + s \cdot \rho_{m, L} \tag{18.4}
$$
$$
\tilde{\rho}_{-m, L} := s \cdot \rho_{m, R} + c \cdot \rho_{-m, L} \tag{18.5}
$$

*Lean 4 Proof Strategy:* Define these transformations as linear maps on the `FockSpace` endomorphisms. In the formalization, `A07Interactions.bogoliubovCreator` and `A07Interactions.bogoliubovAnnihilator` define these combinations for arbitrary branches and orientations, and `bogoliubov_creator_adjoint` proves $\tilde{\rho}_{m,\eta}^\dagger = \tilde{\rho}_{-m,\eta}$.

**Helper Lemma 18.3 (Exact Inverse Transformation).**
The inverse two-by-two scalar transformation is global linear algebra on any complex module:
$$
\rho_{m, R} = c \cdot \tilde{\rho}_{m, R} - s \cdot \tilde{\rho}_{-m, L} \tag{18.6a}
$$
$$
\rho_{m, L} = c \cdot \tilde{\rho}_{m, L} - s \cdot \tilde{\rho}_{-m, R} \tag{18.6b}
$$
$$
\rho_{-m, R} = c \cdot \tilde{\rho}_{-m, R} - s \cdot \tilde{\rho}_{m, L} \tag{18.6c}
$$
$$
\rho_{-m, L} = c \cdot \tilde{\rho}_{-m, L} - s \cdot \tilde{\rho}_{m, R} \tag{18.6d}
$$

*Global operator status:* In Lean, `HyperbolicPair.inverse_combination` proves the underlying module identity $c(cX + sY) - s(cY + sX) = (c^2 - s^2)X = X$ on any complex vector space $E$. Consequently, the four inverse relations `bogoliubov_creator_inverse_right`, `bogoliubov_creator_inverse_left`, `bogoliubov_annihilator_inverse_right`, and `bogoliubov_annihilator_inverse_left` hold as **global operator equalities** on all finite-Fock endomorphisms without any budget restriction or CCR assumption (resolving tracking item CH18-N14).

#### 18.2 Invariance of the Kac-Moody Algebra

**Theorem 18.4 (Kac-Moody Preservation on the Budget).**
The inverse scalar transformation does not immediately prove an algebra automorphism of all finite-Fock endomorphisms, because boundary commutators exist outside the budget. However, evaluated strictly as an action on a state $\psi \in \mathcal{B}_{K, \vec{N}}$ satisfying the branch margin condition ($2M + K + |N_\nu| \le h$), the Kac-Moody algebra is exactly preserved:
$$
[\tilde{\rho}_{-m, R}, \tilde{\rho}_{m, R}] \psi = m(c^2 - s^2) \psi = m \psi \tag{18.7}
$$

*Global versus budget-only commutators:*
1. *Cross-branch annihilator-creator:* The commutator $[\tilde{\rho}_{-m,\eta}, \tilde{\rho}_{m,\bar\eta}] = 0$ is a **global identity** on the entire finite Fock space (`bogoliubov_cross_annihilator_creator`), because distinct-species density modes commute unconditionally (`A05.rho_cross_commute`).
2. *Same-branch CCR and cross-branch creator/annihilator pairs:* The same-branch CCR $[\tilde{\rho}_{-m,\eta}, \tilde{\rho}_{m,\eta}] \psi = m \psi$ (`A07Interactions.bogoliubov_ccr_on_budget`), the cross-branch creator commutator $[\tilde{\rho}_{m,R}, \tilde{\rho}_{m,L}] \psi = 0$ (`bogoliubov_cross_creator_creator_on_budget`), and the cross-branch annihilator commutator $[\tilde{\rho}_{-m,R}, \tilde{\rho}_{-m,L}] \psi = 0$ (`bogoliubov_cross_annihilator_annihilator_on_budget`) hold **on budget vectors** $\psi \in \mathcal{B}_{K, \vec{N}}$ under the margin hypothesis `A06.branchMargins h M K Ns branches`. The cross-terms cancel on the budget because the two branches carry opposite Schwinger signs ($+m$ versus $-m$).

#### 18.3 Exact Diagonalization and the Luttinger Parameters

If we directly expand the diagonal target Hamiltonian $H_{\text{diag}} = \frac{2\pi u}{L} \sum_{m=1}^M (\tilde{\rho}_{m, R} \tilde{\rho}_{-m, R} + \tilde{\rho}_{m, L} \tilde{\rho}_{-m, L})$ using the transformation definitions (without redundant outer $m$ factors), we obtain:
$$
H_{\text{diag}} = \frac{2\pi u}{L} \sum_{m=1}^M \left[ (c^2 + s^2)(\rho_{m, R}\rho_{-m, R} + \rho_{m, L}\rho_{-m, L}) + 2cs(\rho_{m, R}\rho_{m, L} + \rho_{-m, R}\rho_{-m, L}) \right] + \Delta E_{\text{vac}} \tag{18.8}
$$
where the vacuum constant is $\Delta E_{\text{vac}} = \frac{2\pi}{L} \cdot 2us^2 \sum_{m=1}^M m I$.

**Definition 18.5 (Luttinger Parameter Record `LuttingerParams`).**
We match this expansion to the raw pairing Luttinger Hamiltonian from Chapter 17 ($v_1 = v_F + g_4 / 2\pi$, $v_2 = g_2 / 2\pi$). We assume stability $v_1 > |v_2|$ (not merely $v_1^2 > v_2^2$, to guarantee positive velocity).
We define the parameter record `LuttingerParams` containing:
1. Renormalized sound velocity $u := \sqrt{v_1^2 - v_2^2} > 0$.
2. Hyperbolic parameters $c, s \in \mathbb{R}$ satisfying $c^2 - s^2 = 1$, determined by:
$$
c^2 + s^2 = \frac{v_1}{u}, \quad 2cs = \frac{v_2}{u} \tag{18.9}
$$
Cross-multiplying yields the algebraic relation $v_2(c^2 + s^2) = v_1(2cs)$ (`tanh_relation_of_params`), corresponding to $\tanh 2\xi = v_2 / v_1$.
3. Luttinger dimensionless parameter $g > 0$ and its inverse $g^{-1}$:
$$
g := (c - s)^2 = \frac{v_1 - v_2}{u} = \sqrt{\frac{v_1 - v_2}{v_1 + v_2}} > 0, \quad g^{-1} := (c + s)^2 = \frac{v_1 + v_2}{u} = \sqrt{\frac{v_1 + v_2}{v_1 - v_2}} > 0 \tag{18.10}
$$
Since $(c-s)(c+s) = c^2 - s^2 = 1$, we have the exact algebraic identity $g \cdot g^{-1} = 1$ (`luttingerG_mul_inv`, `luttingerGInv_eq_inv`).
Furthermore, $c^2 + s^2 = (g + g^{-1}) / 2$ (`hyperbolic_coeff_eq_luttinger`).

**Remark 18.5a (Physical Interpretation of $g$ and Repulsion — CH18-N2b).**
The dimensionless Luttinger parameter $g = (c - s)^2$ quantifies interaction effects relative to the non-interacting Fermi gas:
$$
g < 1 \iff v_2 > 0 \quad (\text{repulsive inter-branch interaction}),
$$
$$
g = 1 \iff v_2 = 0 \quad (\text{non-interacting free fermions}),
$$
$$
g > 1 \iff v_2 < 0 \quad (\text{attractive inter-branch interaction}).
$$
In Lean, `luttingerG_pos_of_params` proves $g > 0$, `luttingerG_mul_u_of_params` proves $g \cdot u = v_1 - v_2$, `luttingerGInv_mul_u_of_params` proves $g^{-1} \cdot u = v_1 + v_2$, and `v2_eq_zero_iff_s_eq_zero` proves $v_2 = 0 \iff s = 0$. The equivalence $g < 1 \iff v_2 > 0$ is stated here as a physical interpretation remark, reflecting the standard convention that forward repulsion suppresses $g$ below unity.

**Theorem 18.6 (Exact Diagonalization on Budget).**
By substituting the matching parameters, the interacting Hamiltonian evaluates on budget vectors $\psi \in \mathcal{B}_{K, \vec{N}}$ (satisfying branch margin conditions $2M + K + |N_\nu| \le h$ and Sugawara margin) to:
$$
H_{\text{Lutt}} \psi = \left[ \frac{2\pi u}{L} \sum_{m=1}^{M} \left( \tilde{\rho}_{m, R} \tilde{\rho}_{-m, R} + \tilde{\rho}_{m, L} \tilde{\rho}_{-m, L} \right) + E_{\text{zero}} - \Delta E_{\text{vac}} \right] \psi \tag{18.11}
$$
where $\Delta E_{\text{vac}} = \frac{2\pi}{L} \cdot 2us^2 \sum_{m=1}^M m I$.

**Remark 18.6a (Closed-Form Vacuum Shift Scalar — CH18-N3).**
In the finite model, `vacuumShiftScalar` evaluates the normal-ordering correction as $\Delta E_{\text{vac}} = \frac{2\pi}{2h} \sum_{m=1}^M 2 u s^2 m$.
The proved algebraic identity $2 u s^2 = v_1 - u$ (`vacuum_shift_prefactor_of_params`) shows that the per-mode coefficient is independent of $m$. Factoring this constant out of the arithmetic mode sum $\sum_{m=1}^M m = \frac{M(M+1)}{2}$ yields the explicit closed form:
$$
\Delta E_{\text{vac}} = \frac{2\pi}{2h} (v_1 - u) \frac{M(M+1)}{2}.
$$
Since $u = \sqrt{v_1^2 - v_2^2} \le v_1$ with equality if and only if $v_2 = 0$ (`u_lt_v1_of_v2_ne_zero`, `v2_eq_zero_iff_s_eq_zero`), we have $2 u s^2 = v_1 - u \ge 0$, and $\Delta E_{\text{vac}} > 0$ if and only if $v_2 \ne 0 \iff s \ne 0$.

*Lean 4 Proof Strategy:* In Lean, `luttinger_oscillator_dressed_on_budget` sums the per-mode theorem `A07Interactions.bogoliubov_expansion_on_budget` over $m \in \{1,\dots,M\}$, subtracting `vacuumShiftScalar`. Then `luttinger_hamiltonian_dressed_on_budget` combines this oscillator identity with `Ch17.luttinger_hamiltonian_on_budget` on `A05.jointBudget h Ns K` to obtain the complete finite Hamiltonian identity.

**Corollary 18.7 (Physical Velocity Comparison).**
If $v_1 > 0$ and $v_2 \neq 0$, then $u = \sqrt{v_1^2 - v_2^2} < v_1$ (`u_lt_v1_of_v2_ne_zero`). Repulsive $g_2$ alone does *not* guarantee a speed larger than the bare $v_F$; the intra-branch $g_4$ contribution must outcompete the $g_2$ mixing. The physical corollary is therefore stated as $u < v_1$, not $u > v_F$.

#### 18.4 State Semantics and Energy-Shell Schrieffer-Wolff Decomposition

**Theorem 18.8 (Obstruction to Simultaneous Bare and Dressed Vacuum on Current-Action Regime).**
Let $m \ge 1$ be a retained mode, and assume $s \neq 0$. On any nonzero state $\psi\ne0$ in a current-action regime where the scalar CCR $[\rho_{-m,\nu}, \rho_{m,\nu}]\psi = m \psi$ holds (such as any sector ground state $|\vec{N}\rangle_0$ in an admissible sector within budget margins):
(i) The state $\psi$ cannot be simultaneously annihilated by bare lowering modes ($\rho_{-m,\nu}\psi = 0$) and dressed lowering modes ($\tilde{\rho}_{-m,\nu}\psi = 0$).
*(Proof: If $\rho_{-m,R}\psi = 0$ and $\tilde{\rho}_{-m,R}\psi = (c \rho_{-m,R} + s \rho_{m,L})\psi = 0$ with $s \neq 0$, then $\rho_{m,L}\psi = 0$. Similarly, $\tilde{\rho}_{-m,L}\psi = 0 \implies \rho_{m,R}\psi = 0$. Then $m \psi = [\rho_{-m,R}, \rho_{m,R}]\psi = \rho_{-m,R}(\rho_{m,R}\psi) - \rho_{-m,R}(\rho_{-m,R}\psi) = 0$, forcing $\psi = 0$).*

*(Scope Warning: This obstruction requires the nonvacuous current-action hypothesis $[\rho_{-m}, \rho_m]\psi = m\psi$; boundary kets such as the completely empty ket $\delta_\emptyset$ or fully occupied ket $\delta_{\Lambda^*}$ are annihilated by all non-zero density modes $\rho_m$ for trivial degree reasons, so the obstruction does not hold globally on all of finite Fock space).*

**Constructive ground excitation:**
On the constructed finite sector ground ket $|\vec{N}\rangle_0$, the dressed annihilators do not vanish; rather, they map directly to explicit single-mode excitations of the opposite branch:
$$
\tilde{\rho}_{-m, R} |\vec{N}\rangle_0 = s \cdot \rho_{m, L} |\vec{N}\rangle_0 = s \cdot \text{excitedKet}(\text{left}, m) \tag{18.12a}
$$
$$
\tilde{\rho}_{-m, L} |\vec{N}\rangle_0 = s \cdot \rho_{m, R} |\vec{N}\rangle_0 = s \cdot \text{excitedKet}(\text{right}, m) \tag{18.12b}
$$
propositions proved as `dressed_annihilator_ground_right` and `dressed_annihilator_ground_left`.
When $s \ne 0$ and under the margin condition `marginAt`, these excited kets are strictly non-zero (`dressed_annihilator_ground_right_ne_zero`, `dressed_annihilator_ground_left_ne_zero`).
Theorem 18.8 is formalized as `no_common_bare_dressed_vacuum`: under `branchMargins`, bare and dressed lowering annihilation cannot simultaneously hold on a non-zero budget state.

Consequently:
1. The finite Hamiltonian must be evaluated on its own constructed finite ground vector (or density matrix) with boundary corrections.
2. Abstract quasi-free Gaussian CCR states (where an untruncated state $\omega_{\tilde{\Omega}}$ satisfies the lowering mode annihilation condition $\omega_{\tilde{\Omega}}(\tilde{\rho}_{-m,\nu}^\dagger \tilde{\rho}_{-m,\nu}) = 0$) are representations of an infinite CCR algebra, not finite-Fock vectors. The two frameworks must be kept conceptually distinct.

**Theorem 18.9 (Energy-Shell Schrieffer-Wolff Decomposition).**
Let $\mathcal{B}_K = \mathcal{B}_{K-1} \oplus \mathcal{H}_K$ be the budget decomposition by energy shells.
1. *Energy shell vs. mode decimation:* Projecting $\mathcal{B}_K \to \mathcal{B}_{K-1}$ discards states with total partition energy $E = K$. This is distinct from removing an oscillator mode factor (e.g., at $K=2$, $\mathcal{B}_2$ contains both $X_1^2$ and $X_2$; shell projection removes both, while mode decimation of mode 2 would retain $X_1^2$). Formalized in `Bosonize.A10.energy_shell_discards_double_mode_one`.
2. *Block-diagonal SW transformation:* If an unperturbed baseline $H_0$ is block diagonal with respect to the energy-shell projection $P$, and a perturbation $V$ satisfies $P V Q = Q V P = 0$, then the Schrieffer-Wolff generator $S_1 = 0$, and the effective Hamiltonian on $\mathcal{B}_{K-1}$ has zero second-order correction ($H_{\text{eff}} = P (H_0 + V) P$). Formalized in `Bosonize.A10.sw_off_zero_implies_effective_exact`.
3. *Physical RG context:* The statement that the Luttinger Liquid is an RG fixed line is a physical continuum scaling interpretation requiring a defined parameter map and rescaling rule, distinct from this finite discrete energy-shell projection.

#### 18.5 Constructive Realization in Lean

The formalization in `BosonizeStubs/Ch18Bogoliubov.lean` (namespace `Bosonize.Ch18`) implements the complete algebraic and operator theory of the Bogoliubov transformation over the finite multispecies CAR Hilbert space constructed in previous chapters.

1. **Carrier and State Spaces:**
   The underlying carrier for the operator theorems is `Bosonize.A05.FockSpace σ h` over any finite, linearly ordered species type $\sigma$ (`{σ : Type*} [Fintype σ] [LinearOrder σ]`) equipped with a pair of distinct branches `branches : Bosonize.A06.Branches σ` (Right and Left) on a finite band of size $L = 2h$ with momentum labels $-h < k \le h$. (Only the concrete witness specializes $\sigma$ to `Fin 2` with `Ch16.standardBranches`).
   States are evaluated on the subspace `Bosonize.A05.jointBudget h Ns K`, which restricts states to fixed charge eigenvalues $\hat{N}_\nu \psi = N_\nu \psi$ and bounds the total partition excitation energy by $K$.
   The sector charges must be admissible (`A05.admissible h Ns`, satisfying $-h \le N_\nu \le h$).
   All restricted operator identities require the branch margin condition `A06.branchMargins h M K Ns branches`, defined as:
   $$
   2M + K + |N_R| \le h, \qquad 2M + K + |N_L| \le h.
   $$

2. **Hyperbolic Parameter Structure:**
   The structure `HyperbolicPair` bundles real scalars $c, s \in \mathbb{R}$ with the invariant $c^2 - s^2 = 1$.
   The constructor `HyperbolicPair.ofParams` projects from `A07Interactions.HyperbolicParams v1 v2`.
   The theorem `hyperbolic_params_nonempty` proves that for any stable velocities $|v_2| < v_1$, there exists a valid parameter record with $u > 0$ and $c > 0$.
   The scalar theory establishes $g \cdot g^{-1} = 1$ (`luttingerG_mul_inv`, `luttingerGInv_eq_inv`), $g \cdot u = v_1 - v_2$ (`luttingerG_mul_u_of_params`), $g^{-1} \cdot u = v_1 + v_2$ (`luttingerGInv_mul_u_of_params`), $g = \sqrt{(v_1 - v_2)/(v_1 + v_2)}$ (`luttingerG_eq_sqrt_of_params`), $c^2 + s^2 = (g + g^{-1})/2$ (`hyperbolic_coeff_eq_luttinger`), $v_2 = 0 \iff s = 0$ (`v2_eq_zero_iff_s_eq_zero`), $u < v_1$ for $v_2 \ne 0$ (`u_lt_v1_of_v2_ne_zero`), and $2us^2 = v_1 - u$ (`vacuum_shift_prefactor_of_params`).

3. **Classification of Global vs. Budget-Restricted Identities:**
   The Lean proofs rigorously separate identities that hold on all endomorphisms from those that hold only on budget vectors:
   - *Global identities (unrestricted):*
     - `HyperbolicPair.inverse_combination`: module inversion identity on any complex vector space.
     - `bogoliubov_creator_inverse_right`, `bogoliubov_creator_inverse_left`: express bare creators in terms of dressed operators.
     - `bogoliubov_annihilator_inverse_right`, `bogoliubov_annihilator_inverse_left`: express bare annihilators in terms of dressed operators.
     - `bogoliubov_cross_annihilator_creator`: $[\tilde{\rho}_{-m,\eta}, \tilde{\rho}_{m,\bar\eta}] = 0$ globally on `FockSpace`.
     - `A07Interactions.bogoliubov_creator_adjoint`: $\tilde{\rho}_{m,\eta}^\dagger = \tilde{\rho}_{-m,\eta}$ Hilbert space adjoint.
   - *Budget-restricted identities (requiring `jointBudget` and `branchMargins`):*
     - `A07Interactions.bogoliubov_ccr_on_budget`: $[\tilde{\rho}_{-m,\eta}, \tilde{\rho}_{m,\eta}] v = m v$.
     - `bogoliubov_cross_creator_creator_on_budget`: $[\tilde{\rho}_{m,R}, \tilde{\rho}_{m,L}] v = 0$.
     - `bogoliubov_cross_annihilator_annihilator_on_budget`: $[\tilde{\rho}_{-m,R}, \tilde{\rho}_{-m,L}] v = 0$.
     - `luttinger_oscillator_dressed_on_budget`: sums the per-mode expansion over $m \in \{1,\dots,M\}$.
     - `luttinger_hamiltonian_dressed_on_budget`: full Hamiltonian identity on budget vectors.
     - `no_common_bare_dressed_vacuum`: obstruction to simultaneous bare and dressed annihilation.

4. **Constructive Ground Action and Minimal Obstruction:**
   Rather than postulating an unphysical dressed vacuum ket, the implementation proves constructive action formulas on the sector ground ket:
   `dressed_annihilator_ground_right` and `dressed_annihilator_ground_left` prove $\tilde{\rho}_{-m, R} |\vec{N}\rangle_0 = s \cdot \text{excitedKet}_L(m)$ and $\tilde{\rho}_{-m, L} |\vec{N}\rangle_0 = s \cdot \text{excitedKet}_R(m)$.
   When $s \ne 0$ and under `marginAt`, these excited vectors are strictly non-zero (`dressed_annihilator_ground_right_ne_zero`, `dressed_annihilator_ground_left_ne_zero`).
   The theorem `no_common_bare_dressed_vacuum` proves that no non-zero budget state can be simultaneously annihilated by bare and dressed modes for $s \ne 0$.

5. **Concrete Witness:**
   The theorem `concrete_bogoliubov_witness` evaluates the complete formalization on an explicit non-trivial witness:
   - Velocities: $v_1 = 17$, $v_2 = 15$, matched to $v_F = 1, g_4 = 32\pi, g_2 = 30\pi$ via `concrete_velocity_match`.
   - Renormalized sound speed: $u = 8 = \sqrt{17^2 - 15^2}$.
   - Hyperbolic parameters: $c = 5/4$, $s = 3/4$, satisfying $c^2 - s^2 = 25/16 - 9/16 = 1$ and $s \ne 0$.
   - Luttinger parameter: $g = (5/4 - 3/4)^2 = (1/2)^2 = 1/4 < 1$ (repulsive).
   - Normal-ordering prefactor: $2 u s^2 = 2 \cdot 8 \cdot (9/16) = 9 = 17 - 8 = v_1 - u$.
   - Geometry: carrier cutoff $h = 8$, mode cutoff $M = 2$, budget cutoff $K = 2$, sector charges $N_R = N_L = 0$.
   - The branch margins $2(2) + 2 + 0 = 6 \le 8$ and Sugawara margins $2 < 8$ are strictly satisfied.
   - Vacuum shift scalar: $\Delta E_{\text{vac}} = \frac{2\pi}{16} \cdot 9 \cdot (1 + 2) = \frac{27\pi}{8} \ne 0$.
   - The sector ground ket $|0\rangle$ is in the budget and non-zero; the dressed annihilator $\tilde{A}_R |0\rangle \ne 0$ and dressed mode number $\tilde{D}_2 |0\rangle \ne 0$ are non-zero.

6. **Finite Scope and Open Limitations:**
   The verified diagonalization is an operator action identity on the discrete subspace `jointBudget h Ns K` for the chosen pairing model; it does not constitute a spectral theorem or construct a unitary operator $U = e^{iS}$ on finite Fock space. The earlier "Lean 4 Proof Strategy" paragraphs remain explanatory proposals; this section records the actual verified construction.
