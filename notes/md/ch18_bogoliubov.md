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

*Lean 4 Proof Strategy:* State the inverse as an equality of operators. The proof will be a direct application of the definitions from 18.2 and using `hp.h` (the identity $c^2 - s^2 = 1$). Use `ring` and `simp` with the linearity of operator addition and scalar multiplication. Auxiliary lemma: a basic algebraic simplification showing `c(c x + s y) - s(s x + c y) = (c^2 - s^2)x = x`.

#### 18.2 Invariance of the Kac-Moody Algebra

**Theorem 18.4 (Kac-Moody Preservation on the Budget).**
The inverse scalar transformation does not immediately prove an algebra automorphism of all finite-Fock endomorphisms, because boundary commutators exist outside the budget. However, evaluated strictly as an action on a state $\psi \in \mathcal{B}_{K, \vec{N}_{max}}$ satisfying the M2 margin condition, the Kac-Moody algebra is exactly preserved:
$$
[\tilde{\rho}_{-m, R}, \tilde{\rho}_{m, R}] \psi = m(c^2 - s^2) \psi = m \psi \tag{18.7}
$$

*Lean 4 Proof Strategy:* Formalize by expanding the commutator `[A + B, C + D]` using bilinearity, then applying the base Kac-Moody commutation relations for the raw $\rho$ operators. The cross terms like `[\rho_{-m,R}, \rho_{-m,L}]` vanish by commutativity of independent branches. Finally, factor out $m \psi$ to leave $c^2 - s^2$, which simplifies to $1$ via `hp.h`. Requires the M2 margin condition on $\psi$ to ensure the bare commutators are exact.

#### 18.3 Exact Diagonalization and the Luttinger Parameters

If we directly expand the diagonal target Hamiltonian $H_{\text{diag}} = \frac{2\pi u}{L} \sum m (\tilde{\rho}_{m, R} \tilde{\rho}_{-m, R} + \tilde{\rho}_{m, L} \tilde{\rho}_{-m, L})$ using the transformation definitions, we obtain:
$$
H_{\text{diag}} = \frac{2\pi u}{L} \sum m \left[ (c^2 + s^2)(\rho_{m, R}\rho_{-m, R} + \rho_{m, L}\rho_{-m, L}) + 2cs(\rho_{m, R}\rho_{m, L} + \rho_{-m, R}\rho_{-m, L}) \right] + 2us^2 \frac{2\pi}{L}\sum m I \tag{18.8}
$$

**Definition 18.5 (Algebraic Luttinger Parameters).**
We match this expansion to the raw pairing Luttinger Hamiltonian from Chapter 17 ($v_1 = v_F + g_4 / 2\pi$, $v_2 = g_2 / 2\pi$). We require $v_1 > |v_2|$ (not just $v_1^2 > v_2^2$, to guarantee positive energy).
We define the renormalized sound velocity $u > 0$ and the hyperbolic parameters via:
$$
u = \sqrt{v_1^2 - v_2^2} \tag{18.9}
$$
$$
c^2 + s^2 = \frac{v_1}{u}, \quad 2cs = \frac{v_2}{u} \tag{18.10}
$$
*(Squaring these yields $(c^2-s^2)^2 = 1$, but we supply the required sign $+1$ explicitly in the structure).*

*Lean 4 Proof Strategy:* Define a function computing $u, c, s$ from $v_1, v_2$ assuming the hypothesis $v_1 > |v_2|$. Prove that the resulting $(c,s)$ form a valid `HyperbolicPair` (satisfying $c^2 - s^2 = 1$) by algebraic verification in `ℝ`. `nlinarith` or `ring` tactics, combined with properties of `Real.sqrt`, will verify the identity algebraically.

**Theorem 18.6 (Exact Diagonalization).**
By substituting the matching parameters, the interacting Hamiltonian evaluates exactly to the free diagonalized bosonic Hamiltonian on the budget, plus an exact vacuum zero-point shift originating from the $[ \rho_{-m}, \rho_m ]$ normal ordering commutators during expansion:
$$
\forall \psi \in \mathcal{B}_{K, \vec{N}_{max}}, \quad H_{\text{Lutt}} \psi = \left[ \frac{2\pi u}{L} \sum_{m=1}^{M} m \left( \tilde{\rho}_{m, R} \tilde{\rho}_{-m, R} + \tilde{\rho}_{m, L} \tilde{\rho}_{-m, L} \right) + E_{\text{zero}} - \Delta E_{\text{vac}} \right] \psi \tag{18.11}
$$
where $\Delta E_{\text{vac}} = \frac{2\pi}{L} \cdot 2us^2 \sum m I$.

*Lean 4 Proof Strategy:* Express both sides as operators applied to $\psi$ on the specific budget. Expand $H_{\text{Lutt}}$ and the Bogoliubov operators into combinations of raw $\rho$ operators. Match the coefficients term-by-term using the relations from Definition 18.5. The normal-ordering correction $\Delta E_{\text{vac}}$ arises from reordering $\rho_{m} \rho_{-m}$ into $\rho_{-m} \rho_m + m$ via the Kac-Moody relation (requires M2 margin condition). Use `ring` combined with the operator expansions to conclude equality.

**Corollary 18.7 (Physical Velocity).**
If $v_1 > 0$ and $v_2 \neq 0$, $u = \sqrt{v_1^2 - v_2^2} < v_1$. Repulsive $g_2$ alone does *not* guarantee a speed larger than the bare $v_F$; the intra-branch $g_4$ contribution must outcompete the $g_2$ mixing.

#### 18.4 State Existence and RG Fixed Line

**Theorem 18.8 (Ground State Existence).**
There is generally no normalized positive vacuum satisfying both bare and dressed annihilation conditions on the exact finite slice. The actual finite Hamiltonian needs its own ground-state construction (e.g. via diagonalizing a finite positive density matrix). The vacuum state evaluated by algebraic trace projections must be separated from an abstract untruncated continuous CCR functional.

*Lean 4 Proof Strategy:* State this as an impossibility or non-existence theorem: $\neg \exists \psi \neq 0, \forall m, (\rho_{m,R} \psi = 0 \land \tilde{\rho}_{m,R} \psi = 0)$ except when $s = 0$. Proof by contradiction: assuming such a state exists, substituting the inverse Bogoliubov relations would force $s \cdot \rho_{-m,L} \psi = 0$, which contradicts the non-triviality of the state if $s \neq 0$.

**Theorem 18.9 (Luttinger Liquid Fixed Line).**
Because the interaction maps exactly to a diagonal quadratic matrix, the discrete Schrieffer-Wolff decimation map $\mathbb{E}_K$ (see Appendix A10) cleanly deletes the highest mode $K$ without generating any off-diagonal loop corrections among the lower modes $m < K$. This formalizes the Luttinger Liquid as an exact discrete algebraic RG fixed line.

*Lean 4 Proof Strategy:* Apply the Schrieffer-Wolff map $\mathbb{E}_K$ to the diagonalized Hamiltonian. Since $H_{\text{diag}}$ has no terms coupling mode $K$ to modes $m < K$, the off-diagonal parts $V_{ab}$ in the decimation are exactly zero. Thus the effective Hamiltonian $H_{\text{eff}}$ on the low-energy space is simply the truncation of $H_{\text{diag}}$ up to $K-1$, proving the fixed-line property.
