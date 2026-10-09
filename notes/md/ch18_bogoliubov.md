### Chapter 18: The Bogoliubov Transformation

To identify the true physical excitations of the Luttinger liquid, we must decouple the Right and Left moving density waves algebraically. This requires finding a new set of bosonic operators that diagonalize the pairing Hamiltonian matrix while preserving the underlying Kac-Moody algebra. The mathematical formalization strictly follows [Appendix A07](../appendices/a07_interactions_and_bogoliubov.md), [Appendix A08](../appendices/a08_states_and_correlations.md), and [Appendix A10](../appendices/a10_discrete_rg_and_schrieffer_wolff.md).

#### 18.1 The Hyperbolic Transformation

**Definition 18.1 (Algebraic Hyperbolic Parameters).**
We define the transformation purely algebraically. A hyperbolic pair consists of real scalars $c, s \in \mathbb{R}$ satisfying the exact identity:
$$
c^2 - s^2 = 1 \tag{18.1}
$$

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

**Helper Lemma 18.3 (Exact Inverse Transformation).**
The inverse two-by-two scalar transformation is global linear algebra:
$$
\rho_{m, R} = c \cdot \tilde{\rho}_{m, R} - s \cdot \tilde{\rho}_{-m, L} \tag{18.6}
$$

#### 18.2 Invariance of the Kac-Moody Algebra

**Theorem 18.4 (Kac-Moody Preservation on the Budget).**
The inverse scalar transformation does not immediately prove an algebra automorphism of all finite-Fock endomorphisms, because boundary commutators exist outside the budget. However, evaluated strictly as an action on a state $\psi \in \mathcal{B}_{K, \vec{N}_{max}}$ satisfying the M2 margin condition, the Kac-Moody algebra is exactly preserved:
$$
[\tilde{\rho}_{-m, R}, \tilde{\rho}_{m, R}] \psi = m(c^2 - s^2) \psi = m \psi \tag{18.7}
$$

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

**Theorem 18.6 (Exact Diagonalization).**
By substituting the matching parameters, the interacting Hamiltonian evaluates exactly to the free diagonalized bosonic Hamiltonian on the budget, plus an exact vacuum zero-point shift originating from the $[ \rho_{-m}, \rho_m ]$ normal ordering commutators during expansion:
$$
\forall \psi \in \mathcal{B}_{K, \vec{N}_{max}}, \quad H_{\text{Lutt}} \psi = \left[ \frac{2\pi u}{L} \sum_{m=1}^{M} m \left( \tilde{\rho}_{m, R} \tilde{\rho}_{-m, R} + \tilde{\rho}_{m, L} \tilde{\rho}_{-m, L} \right) + E_{\text{zero}} - \Delta E_{\text{vac}} \right] \psi \tag{18.11}
$$
where $\Delta E_{\text{vac}} = \frac{2\pi}{L} \cdot 2us^2 \sum m I$.

**Corollary 18.7 (Physical Velocity).**
If $v_1 > 0$ and $v_2 \neq 0$, $u = \sqrt{v_1^2 - v_2^2} < v_1$. Repulsive $g_2$ alone does *not* guarantee a speed larger than the bare $v_F$; the intra-branch $g_4$ contribution must outcompete the $g_2$ mixing.

#### 18.4 State Existence and RG Fixed Line

**Theorem 18.8 (Ground State Existence).**
There is generally no normalized positive vacuum satisfying both bare and dressed annihilation conditions on the exact finite slice. The actual finite Hamiltonian needs its own ground-state construction (e.g. via diagonalizing a finite positive density matrix). The vacuum state evaluated by algebraic trace projections must be separated from an abstract untruncated continuous CCR functional.

**Theorem 18.9 (Luttinger Liquid Fixed Line).**
Because the interaction maps exactly to a diagonal quadratic matrix, the discrete Schrieffer-Wolff decimation map $\mathbb{E}_K$ (see Appendix A10) cleanly deletes the highest mode $K$ without generating any off-diagonal loop corrections among the lower modes $m < K$. This formalizes the Luttinger Liquid as an exact discrete algebraic RG fixed line.
