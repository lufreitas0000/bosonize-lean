### Chapter 15: Dual Fields ($\phi$ and $\theta$)

Phase 4 bridges the discrete momentum modes to macroscopic continuous-looking physics. The exact algebraic finite-difference framework aligns with the corrections in [Appendix A06](../appendices/a06_chiral_fields_and_lattice_kernels.md).

#### 15.1 Defining the Chiral Phase Fields with Orientation

If identical copies of the same chiral representation are used, their commutators have the same sign and fail to produce the required cross-field cancellations. We must explicitly construct fields with opposite chirality orientations $\eta \in \{+1, -1\}$.

**Definition 15.1 (Oriented Chiral Fluctuation Field).**
Let $M$ be an independent mode cutoff satisfying $M \ge 1$ and the no-aliasing condition $2M < L$ (so $M \le h-1$).
For each species branch and assigned orientation $\eta \in \{+1, -1\}$, the purely bosonic, Hermitian chiral fluctuation field is defined on the retained modes:

$$
\varphi_\eta(x) := i \sum_{m=1}^{M} \frac{1}{m} \left( \zeta^{\eta m x} \rho_{-m, \eta} - \zeta^{-\eta m x} \rho_{m, \eta} \right) \tag{15.1}
$$

*Lean 4 Proof Strategy:*
Define `chiralFluctuationField (M : ℕ) (η : Int) (x : Int)` as a `Finset` sum over `m ∈ Icc 1 M`. The character $\zeta$ is a primitive $L$-th root of unity. Opposite orientation branches commute: `[rho m 1, rho n (-1)] = 0`. By choosing an explicit cutoff $M$ distinct from $h-1$, the uniform margin condition $2M + K + N_{\max} \le h$ remains non-vacuous on non-trivial budgets.

By reversing the spatial character, opposite orientations yield opposite chiral kernels while retaining the same standard current modes.

**Lemma 15.2 (Hermiticity).**
Because $\rho_{-m} = \rho_m^\dagger$, conjugating the roots exactly flips the sum, proving strict self-adjointness: $\varphi_\eta^\dagger(x) = \varphi_\eta(x)$.

*Lean 4 Proof Strategy:*
Assuming `OperatorAlgebra` implements a `StarRing` typeclass, state the lemma as `star (chiralFluctuationField M η x) = chiralFluctuationField M η x`.

#### 15.2 The Macroscopic Dual Fields

**Definition 15.3 (The Phase and Density Fields).**
Combining a right-moving branch ($\eta = +1$) and a left-moving branch ($\eta = -1$):

$$
\phi(x) := \varphi_{+1}(x) + \varphi_{-1}(x) \tag{15.2}
$$

$$
\theta(x) := \varphi_{+1}(x) - \varphi_{-1}(x) \tag{15.3}
$$

*Lean 4 Proof Strategy:*
Define `phiField M x := chiralFluctuationField M 1 x + chiralFluctuationField M (-1) x` and `thetaField M x := chiralFluctuationField M 1 x - chiralFluctuationField M (-1) x`.

**Lemma 15.4 (Field Commutators on the Budget).**
Evaluating on input vectors $\psi \in \mathcal{B}_{K, \vec{N}_{\max}}$ under the uniform margin condition $2M + K + N_{\max} \le h$, the identical-branch commutators cancel correctly for self-commutators, producing the exact field commutators with an explicit lattice kernel:

$$
\forall \psi \in \mathcal{B}_{K, \vec{N}_{\max}}, \quad [\phi(x), \phi(y)] \psi = 0, \quad [\theta(x), \theta(y)] \psi = 0 \tag{15.4}
$$

$$
\forall \psi \in \mathcal{B}_{K, \vec{N}_{\max}}, \quad [\phi(x), \theta(y)] \psi = 2i \left[ \sum_{m=1}^{M} \frac{2}{m} \sin\left(\frac{2\pi m (x-y)}{L}\right) \right] \psi =: 2i C(x,y) \psi \tag{15.5}
$$

*(Note: These are evaluated as actions on budget vectors, not as unrestricted global identities on the full Fock space).*

*Lean 4 Proof Strategy:*
Expand the Lie brackets into four cross-commutators. Cross-terms between opposite chiral branches vanish. The same-branch commutators evaluate on $\psi \in \mathcal{B}_{K, \vec{N}_{\max}}$ via the Kac-Moody theorem (Theorem 10.4) since $2M + K + N_{\max} \le h$.

#### 15.3 Exact Gradients and the Zero-Mode Obstruction

**Physical Intuition (Exact Forward Difference):**
To define $\partial_x \phi \propto \rho$ strictly algebraically, we use the exact discrete forward difference $\Delta_x f(x) = f(x+1) - f(x)$.

**Lemma 15.5 (Exact Gradient).**
Applying $\Delta_x$ explicitly evaluates to:

$$
(\Delta \varphi_\eta)(x) = i \sum_{m=1}^{M} \frac{1}{m} \left( (\zeta^{\eta m} - 1)\zeta^{\eta m x} \rho_{-m, \eta} - (\zeta^{-\eta m} - 1)\zeta^{-\eta m x} \rho_{m, \eta} \right) \tag{15.6}
$$

*Lean 4 Proof Strategy:*
Apply discrete difference to the finite sum and factor out $(\zeta^{\pm \eta m} - 1)$ linearly.

*(Note: The factor $(\zeta^m - 1)/m$ is strictly not a constant, and low-momentum limits must not be taken to falsely assert an exact lattice identity).*

**Theorem 15.6 (The Zero-Mode Obstruction).**
Summing any periodic forward difference over the lattice identically yields zero. However, for any cutoff $M < L$ strictly avoiding nonzero multiples of $L$, the band-limited Dirichlet delta kernel $\delta_M(x-y) = \frac{1}{L}\sum_{m=-M}^M \zeta^{m(x-y)}$ contains the zero-mode $m=0$ and sums to 1.
Therefore, a naive exact lattice equation $[\phi(x), (\Delta\theta)(y)] \propto \delta_M(x-y)$ is mathematically impossible. The actual commutator of periodic fluctuation fields strictly has zero spatial average. We must retain the exact differentiated finite kernel without analytically equating it to a constant times $\delta_M$:

$$
\forall \psi \in \mathcal{B}_{K, \vec{N}_{\max}}, \quad [\phi(x), (\Delta \theta)(y)] \psi = \Delta_y [ \phi(x), \theta(y) ] \psi = 2i \Delta_y C(x,y) \psi \tag{15.7}
$$

*Lean 4 Proof Strategy:*
Prove $\sum_{x \in \Lambda} \Delta f(x) = 0$ via telescoping. Since $\phi, \theta$ contain only $m \neq 0$ modes, their forward difference commutator sums to 0. Restricting $M < L$ guarantees no multiple of $L$ contributes as an extra zero mode. Thus $\sum [\phi(x), \Delta \theta(y)] = 0 \neq c \sum \delta_M$ for any $c \neq 0$.

#### 15.4 Technical Notes for the Lean 4 Formalization (Chapter 15)

1. **Non-commutative Spatial Differences:**
   * Chapter 2's Umbral calculus `forwardDiff` relies on a commutative coefficient ring. The algebra of operator-valued fields $\mathrm{End}_{\mathbb{C}}(V)$ is non-commutative.
   * You cannot blindly instantiate `forwardDiff` for endomorphisms. You must define a specific module-valued linear map or use explicit algebraic subtraction $A(x+1) - A(x)$ to evaluate differences without assuming operator commutativity.
2. **Kernels as Character Sums:**
   * Define all kernels explicitly as finite `Finset` sums of characters $\zeta$. Only as a secondary evaluation (valid away from $t=0$) should you prove equivalence to quotients of sines. At $t=0$, division by zero is undefined, whereas the character sum exactly yields $(2M+1)/L$.
