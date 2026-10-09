### Chapter 18: The Bogoliubov Transformation

To identify the true physical excitations of the Luttinger liquid, we must decouple the Right and Left moving density waves algebraically. This requires finding a new set of bosonic operators that diagonalize the pairing Hamiltonian matrix while preserving the underlying Kac-Moody algebra. The mathematical formalization strictly follows [Appendix A07](../appendices/a07_interactions_and_bogoliubov.md), [Appendix A08](../appendices/a08_states_and_correlations.md), and [Appendix A10](../appendices/a10_discrete_rg_and_schrieffer_wolff.md).

#### 18.1 The Hyperbolic Transformation

**Definition 18.1 (Algebraic Hyperbolic Parameters).**
We define the transformation purely algebraically. A hyperbolic pair consists of real scalars $c, s \in \mathbb{R}$ satisfying the exact identity:
$$
c^2 - s^2 = 1 \tag{18.1}
$$

*Lean 4 Proof Strategy:* Define a structure `HyperbolicPair` containing `c s : ℝ` and a proof field `h : c^2 - s^2 = 1`. This structure bundles the scalars and their invariant, which can then be passed to the transformation functions. No auxiliary lemmas needed for the definition itself, but typical algebraic facts like `(c - s)(c + s) = 1` could be useful auxiliary lemmas.

**Definition 18.2 (The Bogoliubov Transformation).**
For every mode $m \ge 1$, we define the new dressed creation/annihilation operators in $\mathrm{End}_{\mathbb{C}}(\mathrm{Fock})$:
$$
\tilde{\rho}_{m, R} := c \cdot \rho_{m, R} + s \cdot \rho_{-m, L} \tag{18.2}
$$
$$
\tilde{\rho}_{m, L} := s \cdot \rho_{-m, R} + c \cdot \rho_{m, L} \tag{18.3}
$$
By taking the adjoints (and noting $c, s \in \mathbb{R}$), the complementary operators are exactly:
$$
\tilde{\rho}_{-m, R} := c \cdot \rho_{-m, R} + s \cdot \rho_{m, L} \tag{18.4}
$$
$$
\tilde{\rho}_{-m, L} := s \cdot \rho_{m, R} + c \cdot \rho_{-m, L} \tag{18.5}
$$

*Lean 4 Proof Strategy:* Define these transformations as linear maps on the `FockSpace` endomorphisms. Since we evaluate them on budgets, they are defined pointwise as combinations of the basic `rho m R` and `rho m L` operators. Provide definitions like `bogoliubov_rho_R (hp : HyperbolicPair) (m : ℕ)` returning the composite linear map.

**Helper Lemma 18.3 (Exact Inverse Transformation).**
The inverse two-by-two scalar transformation is global linear algebra:
$$
\rho_{m, R} = c \cdot \tilde{\rho}_{m, R} - s \cdot \tilde{\rho}_{-m, L} \tag{18.6}
$$

Expand scalar actions using module laws, collect the coefficients of each operator, and normalize only the real/complex scalars using `ring` and `hp.h`. The inverse is global linear algebra and needs no CCR hypothesis or commutative operator multiplication.

#### 18.2 Invariance of the Kac-Moody Algebra

**Theorem 18.4 (Kac-Moody Preservation on the Budget).**
The inverse scalar transformation does not immediately prove an algebra automorphism of all finite-Fock endomorphisms, because boundary commutators exist outside the budget. However, evaluated strictly as an action on a state $\psi \in \mathcal{B}_{K, \vec{N}_{max}}$ satisfying the M2 margin condition, the Kac-Moody algebra is exactly preserved:
$$
[\tilde{\rho}_{-m, R}, \tilde{\rho}_{m, R}] \psi = m(c^2 - s^2) \psi = m \psi \tag{18.7}
$$

*Lean 4 Proof Strategy:* Formalize by expanding the commutator `[A + B, C + D]` using bilinearity, then applying the base Kac-Moody commutation relations for the raw $\rho$ operators. The cross terms like `[\rho_{-m,R}, \rho_{-m,L}]` vanish by commutativity of independent branches. Finally, factor out $m \psi$ to leave $c^2 - s^2$, which simplifies to $1$ via `hp.h`. Requires the M2 margin condition on $\psi$ to ensure the bare commutators are exact.

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
3. Luttinger dimensionless parameter $g > 0$ and its inverse $g^{-1}$:
$$
g := (c - s)^2 = \frac{v_1 - v_2}{u} = \sqrt{\frac{v_1 - v_2}{v_1 + v_2}} > 0, \quad g^{-1} := (c + s)^2 = \frac{v_1 + v_2}{u} = \sqrt{\frac{v_1 + v_2}{v_1 - v_2}} > 0 \tag{18.10}
$$
Since $(c-s)(c+s) = c^2 - s^2 = 1$, we have the exact algebraic identity $g \cdot g^{-1} = 1$. Note: the symbol $g$ denotes this interaction parameter, kept distinct from the energy budget cutoff $K$.

*Lean 4 Proof Strategy:* Bundle $u, c, s, g, g^{-1}$ into a structure `LuttingerParams` with proof fields $u > 0$, $c^2 - s^2 = 1$, $g = (c-s)^2$, $g^{-1} = (c+s)^2$, and $g g^{-1} = 1$. Prove that $v_1 > |v_2|$ yields valid real witnesses using `Real.sqrt` and `positivity`.

**Theorem 18.6 (Exact Diagonalization on Budget).**
By substituting the matching parameters, the interacting Hamiltonian evaluates on budget vectors $\psi \in \mathcal{B}_{K, \vec{N}_{\max}}$ (satisfying M2 margin conditions) to:
$$
H_{\text{Lutt}} \psi = \left[ \frac{2\pi u}{L} \sum_{m=1}^{M} \left( \tilde{\rho}_{m, R} \tilde{\rho}_{-m, R} + \tilde{\rho}_{m, L} \tilde{\rho}_{-m, L} \right) + E_{\text{zero}} - \Delta E_{\text{vac}} \right] \psi \tag{18.11}
$$
where $\Delta E_{\text{vac}} = \frac{2\pi}{L} \cdot 2us^2 \sum_{m=1}^M m I$.

*Lean 4 Proof Strategy:* Express both sides as operators applied to $\psi$. Expand the Bogoliubov operators $\tilde{\rho}$ into raw $\rho$ operators. Match the coefficients term-by-term using Definition 18.5. The normal-ordering correction $\Delta E_{\text{vac}}$ arises from reordering $\rho_{-m} \rho_m = \rho_m \rho_{-m} + m I$ via the Kac-Moody relation, which gives the exact scalar sum $\frac{2\pi}{L} 2us^2 \sum_{m=1}^M m I$.

**Corollary 18.7 (Physical Velocity Comparison).**
If $v_1 > 0$ and $v_2 \neq 0$, $u = \sqrt{v_1^2 - v_2^2} < v_1$. Repulsive $g_2$ alone does *not* guarantee a speed larger than the bare $v_F$; the intra-branch $g_4$ contribution must outcompete the $g_2$ mixing.

#### 18.4 State Semantics and Energy-Shell Schrieffer-Wolff Decomposition

**Theorem 18.8 (Obstruction to Simultaneous Bare and Dressed Vacuum on Current-Action Regime).**
Let $m \ge 1$ be a retained mode, and assume $s \neq 0$. On any nonzero state $\psi\ne0$ in a current-action regime where the scalar CCR $[\rho_{-m,\nu}, \rho_{m,\nu}]\psi = m \psi$ holds (such as any sector ground state $|\vec{N}\rangle_0$ in an admissible sector within budget margins):
(i) The state $\psi$ cannot be simultaneously annihilated by bare lowering modes ($\rho_{-m,\nu}\psi = 0$) and dressed lowering modes ($\tilde{\rho}_{-m,\nu}\psi = 0$).
*(Proof: If $\rho_{-m,R}\psi = 0$ and $\tilde{\rho}_{-m,R}\psi = (c \rho_{-m,R} + s \rho_{m,L})\psi = 0$ with $s \neq 0$, then $\rho_{m,L}\psi = 0$. Similarly, $\tilde{\rho}_{-m,L}\psi = 0 \implies \rho_{m,R}\psi = 0$. Then $m \psi = [\rho_{-m,R}, \rho_{m,R}]\psi = \rho_{-m,R}(\rho_{m,R}\psi) - \rho_{m,R}(\rho_{-m,R}\psi) = 0$, forcing $\psi = 0$).*

*(Scope Warning: This obstruction requires the nonvacuous current-action hypothesis $[\rho_{-m}, \rho_m]\psi = m\psi$; boundary kets such as the completely empty ket $\delta_\emptyset$ or fully occupied ket $\delta_{\Lambda^*}$ are annihilated by all non-zero density modes $\rho_m$ for trivial degree reasons, so the obstruction does not hold globally on all of finite Fock space).*

Consequently:
1. The finite Hamiltonian must be evaluated on its own constructed finite ground vector (or density matrix) with boundary corrections.
2. Abstract quasi-free Gaussian CCR states (where an untruncated state $\omega_{\tilde{\Omega}}$ satisfies the lowering mode annihilation condition $\omega_{\tilde{\Omega}}(\tilde{\rho}_{-m,\nu}^\dagger \tilde{\rho}_{-m,\nu}) = 0$) are representations of an infinite CCR algebra, not finite-Fock vectors. The two frameworks must be kept conceptually distinct.

*Lean 4 Proof Strategy:* Require ψ≠0 explicitly. Use the two-branch transform `tildeA_R=c • A_R+s • C_L`, bare annihilation by A_R and A_L, and scalar CCR `[A_L,C_L]ψ=m • ψ` for one positive retained mode. Dressed right annihilation and s≠0 force C_Lψ=0, contradicting mψ≠0. Do not replace the actual cross-branch transform by a same-branch shorthand.

**Theorem 18.9 (Energy-Shell Schrieffer-Wolff Decomposition).**
Let $\mathcal{B}_K = \mathcal{B}_{K-1} \oplus \mathcal{H}_K$ be the budget decomposition by energy shells.
1. *Energy shell vs. mode decimation:* Projecting $\mathcal{B}_K \to \mathcal{B}_{K-1}$ discards states with total partition energy $E = K$. This is distinct from removing an oscillator mode factor (e.g., at $K=2$, $\mathcal{B}_2$ contains both $X_1^2$ and $X_2$; shell projection removes both, while mode decimation of mode 2 would retain $X_1^2$).
2. *Block-diagonal SW transformation:* If an unperturbed baseline $H_0$ is block diagonal with respect to the energy-shell projection $P$, and a perturbation $V$ satisfies $P V Q = Q V P = 0$, then the Schrieffer-Wolff generator $S_1 = 0$, and the effective Hamiltonian on $\mathcal{B}_{K-1}$ has zero second-order correction ($H_{\text{eff}} = P (H_0 + V) P$).
3. *Physical RG context:* The statement that the Luttinger Liquid is an RG fixed line is a physical continuum scaling interpretation requiring a defined parameter map and rescaling rule, distinct from this finite discrete energy-shell projection.

*Minimal vacuum-obstruction proof:* Assume one retained positive mode, bare annihilation on both branches, and the dressed right annihilator kills a nonzero ψ. With s≠0 these imply the left creator kills ψ too; the left scalar CCR on ψ then gives mψ=0, a contradiction. A normalized or explicitly nonzero candidate is essential. Same-mode CCR suffices for this obstruction and each diagonalization summand; an all-pair margin is a convenient stronger wrapper only when needed.
