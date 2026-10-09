# BOSONIZE-LEAN: Mathematical Reference Notes

## Part V: Phase 5 Interactions & The Luttinger Liquid

### Chapter 18: The Bogoliubov Transformation

In Chapter 17, we reduced the fully interacting, forward-scattering 1D Hamiltonian down to a quadratic bosonic form on the budget subspace. However, because of the $g_2$ inter-branch scattering term, the Right and Left moving density waves are coupled.
To identify the true physical excitations (the independent "quasi-particles" of the Luttinger liquid), we must mathematically decouple them. This requires finding a new set of bosonic operators that diagonalize the Hamiltonian matrix while perfectly preserving the underlying Kac-Moody algebra. This canonical transformation is known as the **Bogoliubov Transformation**.

#### 18.1 The Hyperbolic Transformation

**Physical Intuition (Why Hyperbolic?):**
If we want to mix two standard variables (like $x$ and $y$) to diagonalize a matrix, we typically use a standard 2D rotation matrix parameterized by $\cos(\theta)$ and $\sin(\theta)$.
However, in our quantum algebra, the operators must satisfy the Kac-Moody commutator: $[\rho_{-m}, \rho_m] = m$.
If we mix a Right-creator ($\rho_{m, R}$) with a Left-annihilator ($\rho_{-m, L}$), we must check the commutator of the new mixed operator. Because swapping the indices on the Left-annihilator commutator yields a *negative* sign ($[\rho_{m, L}, \rho_{-m, L}] = -m$), the squared coefficients in our transformation will subtract rather than add.
To ensure the new operator evaluates back to $+m$, the coefficients $c$ and $s$ must satisfy $c^2 - s^2 = 1$. This is precisely the defining identity of hyperbolic geometry. Therefore, the transformation must be a hyperbolic rotation.

**Definition 18.1 (Algebraic Hyperbolic Parameters).**
To avoid relying on real-analysis transcendental functions like $\cosh$ and $\sinh$ in Lean, we define the transformation purely algebraically. Let $\mathbb{K}$ be our base commutative ring (e.g., $\mathbb{C}$ or $\mathbb{R}$). A hyperbolic pair is defined as any two scalars $c, s \in \mathbb{K}$ satisfying the strict algebraic identity:

$$
c^2 - s^2 = 1 \tag{18.1}
$$

**Definition 18.2 (The Bogoliubov Transformation).**
For every mode $m \in \Lambda^*$ (where $m \ge 1$), we define the new dressed density operators $\tilde{\rho}_{m, R}$ and $\tilde{\rho}_{m, L}$ as global linear combinations of the bare operators in $\mathrm{End}_{\mathbb{C}}(\mathrm{Fock}(\Lambda^*))$:

$$
\tilde{\rho}_{m, R} := c \cdot \rho_{m, R} + s \cdot \rho_{-m, L} \tag{18.2}
$$

$$
\tilde{\rho}_{-m, L} := s \cdot \rho_{m, R} + c \cdot \rho_{-m, L} \tag{18.3}
$$

By taking the adjoints of these definitions (and noting $c, s$ are chosen to be real), the complementary operators are exactly:

$$
\tilde{\rho}_{-m, R} := c \cdot \rho_{-m, R} + s \cdot \rho_{m, L} \tag{18.4}
$$

$$
\tilde{\rho}_{m, L} := s \cdot \rho_{-m, R} + c \cdot \rho_{m, L} \tag{18.5}
$$

#### 18.2 Invariance of the Kac-Moody Algebra

**Physical Intuition (Conservation of Statistics):**
For these new mathematical objects ($\tilde{\rho}$) to physically represent actual independent bosons (density waves), they must obey the exact same rules as the original bosons. We must prove that this transformation acts as an **automorphism** of the algebra—it scrambles the operators internally but preserves the overall structural rules perfectly. Because the algebra only exists exactly on our finite lattice within the low-energy budget, this invariance must be stated strictly as an action on that subspace.

**Helper Lemma 18.3 (Cross-Branch Commutativity).**
Because the Right and Left branches operate on completely disjoint underlying fermion indices, any bare $R$ mode strictly commutes with any bare $L$ mode on the entire Fock space:
$\forall m, n \in \mathbb{Z}, \quad [\rho_{m, R}, \rho_{n, L}] = 0$.

**Theorem 18.4 (Kac-Moody Preservation on the Budget).**
Let $\psi \in \mathcal{B}_{K, \vec{N}_{max}}$ be a state in the energy budget. If the shift parameters satisfy the M2 Margin Condition ($\vert{}m\vert{} + \vert{}n\vert{} + K + N_{\max} \le h$), then the dressed operators satisfy the exact independent Kac-Moody algebra on the subspace:

$$
[\tilde{\rho}_{-m, R}, \tilde{\rho}_{m, R}] \psi = m \psi \tag{18.6}
$$

$$
[\tilde{\rho}_{-m, L}, \tilde{\rho}_{m, L}] \psi = m \psi \tag{18.7}
$$

$$
[\tilde{\rho}_{\pm m, R}, \tilde{\rho}_{\pm m, L}] \psi = 0 \tag{18.8}
$$

*Formal Proof Sketch for Lean:* Expanding the bracket linearly for the Right dressed mode:
$[\tilde{\rho}_{-m, R}, \tilde{\rho}_{m, R}] \psi = [c \rho_{-m, R} + s \rho_{m, L}, c \rho_{m, R} + s \rho_{-m, L}] \psi$.
By Lemma 18.3, the mixed cross-branch terms vanish. This leaves:
$= (c^2 [\rho_{-m, R}, \rho_{m, R}] + s^2 [\rho_{m, L}, \rho_{-m, L}]) \psi$.
By Theorem 10.5 (Kac-Moody on the Budget), under the M2 margin, this evaluates to:
$= (c^2 (m) + s^2 (-m)) \psi = m(c^2 - s^2) \psi$.
By Definition 18.1, $c^2 - s^2 = 1$, yielding exactly $m \psi$. $\blacksquare$

#### 18.3 Exact Diagonalization and the Luttinger Parameters

**Physical Intuition (Tuning the Rotation):**
If we substitute our new dressed operators back into the interacting Hamiltonian (Theorem 17.8), the Hamiltonian will expand into a massive polynomial containing both diagonal terms ($\tilde{\rho}_R \tilde{\rho}_R$) and off-diagonal cross-terms ($\tilde{\rho}_R \tilde{\rho}_L$).
We simply choose the specific hyperbolic parameters ($c, s$) that force the scalar coefficient of the cross-terms to equal exactly zero. Once the cross-terms vanish, the Right and Left dressed modes are perfectly decoupled, proving the interacting system is algebraically equivalent to a free system with a modified speed of sound.

**Helper Lemma 18.5 (Exact Inverse Transformation).**
Because $c^2 - s^2 = 1$, the Bogoliubov transformation is algebraically invertible globally on $\mathrm{End}_{\mathbb{C}}(\mathcal{F})$. The bare operators can be expressed strictly in terms of the dressed operators:

$$
\rho_{m, R} = c \cdot \tilde{\rho}_{m, R} - s \cdot \tilde{\rho}_{-m, L} \tag{18.9}
$$

**Definition 18.6 (Algebraic Luttinger Parameters).**
Let the bare forward scattering velocities from Chapter 17 be defined as:
$v_1 := v_F + \frac{g_4}{2\pi}$ (Intra-branch velocity)
$v_2 := \frac{g_2}{2\pi}$ (Inter-branch coupling)

Assuming weak/repulsive interaction such that $v_1^2 > v_2^2$, we define the renormalized **sound velocity** $u$ and specify the required hyperbolic parameters $c, s$ through the following algebraic matching relations:

$$
u^2 := v_1^2 - v_2^2 \tag{18.10}
$$

$$
c^2 + s^2 = \frac{v_1}{u}, \quad 2cs = -\frac{v_2}{u} \tag{18.11}
$$

*(Note: In Lean, we verify that this choice is mathematically valid by checking the constraint: $(c^2+s^2)^2 - (2cs)^2 = (c^2-s^2)^2 = \frac{v_1^2 - v_2^2}{u^2} = 1$. This proves $c^2-s^2=1$, satisfying Definition 18.1).*

**Theorem 18.7 (Exact Diagonalization of the Luttinger Liquid).**
Let $H_{\text{Lutt}}$ be the fully interacting Hamiltonian defined in Theorem 17.8. Under the R2 margin condition, and using the hyperbolic parameters defined in 18.6, the off-diagonal terms identically cancel. For any state vector $\psi \in \mathcal{B}_{K, \vec{N}_{max}}$, the interacting Hamiltonian evaluates exactly to a free bosonic Hamiltonian governing the dressed modes:

$$
\forall \psi \in \mathcal{B}_{K, \vec{N}_{max}}, \quad H_{\text{Lutt}} \psi = \left[ \frac{2\pi u}{L} \sum_{m=1}^{h-1} \left( \tilde{\rho}_{m, R} \tilde{\rho}_{-m, R} + \tilde{\rho}_{m, L} \tilde{\rho}_{-m, L} \right) + E_{\text{zero}} \right] \psi \tag{18.12}
$$

**Corollary 18.8 (Physical Interpretation).**
1. **Renormalized Velocity:** The original fermions traveled at velocity $v_F$. The new, collective "Luttinger quasi-particles" travel strictly at the new sound velocity $u$. If the interaction is repulsive ($v_2 > 0$), the collective waves travel faster than the bare fermions.
2. **The Luttinger Parameter ($g$):** The dimensionless parameter $g := \sqrt{\frac{v_1 - v_2}{v_1 + v_2}}$ determines the correlation decay rates. For non-interacting fermions, $g=1$. For repulsive interactions, $g < 1$.

#### 18.4 Technical Notes for the Lean 4 Formalization (Chapter 18)

1. **Defining the Transformation cleanly in Lean:**
   * **Hazard:** Do not import Lean's real analysis topology to define `Real.cosh` and `Real.sinh`. The operators live in pure abstract algebra.
   * **Solution:** Define a structure `HyperbolicPair (K : Type) [CommRing K]` containing fields `c`, `s`, and a proof `h_hyper : c^2 - s^2 = 1`.
   * When manipulating the Hamiltonian, all scalar coefficient simplifications can be done entirely by Lean's standard `ring` tactic utilizing `h_hyper`.

2. **Avoiding Global `AlgEquiv`:**
   * While it is tempting to define the transformation as a global `AlgEquiv` over the Lie algebra, remember that the Kac-Moody relations *do not hold globally*—they fail at the band edges.
   * Therefore, do exactly what we did for the Sugawara construction (Chapter 12): formulate Theorem 18.4 and Theorem 18.7 strictly as equalities of vectors resulting from applying the operators to `(ψ : BudgetSpace L K Nmax)`.

3. **Isolating the Diagonalization Logic (`ring` tactic):**
   * To prove Theorem 18.7 in Lean, use Lemma 18.5 to substitute the occurrences of the bare modes $\rho$ inside the definition of $H_{\text{Lutt}}$ with expressions containing the dressed modes $\tilde{\rho}$.
   * Use `LinearMap` properties to expand the resulting massive polynomial.
   * Lean's `ring` tactic (with the relations from 18.11 fed in) will algebraically evaluate the coefficient for the cross-term $\tilde{\rho}_R \tilde{\rho}_L$ exactly to `0`, isolating the diagonal components without manual algebraic tracking.
