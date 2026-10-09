### Chapter 15: Dual Fields ($\phi$ and $\theta$)

Phase 4 bridges the discrete momentum modes to macroscopic continuous-looking physics. The exact algebraic finite-difference framework aligns with the corrections in [Appendix A06](../appendices/a06_chiral_fields_and_lattice_kernels.md).

#### 15.1 Defining the Chiral Phase Fields with Orientation

If identical copies of the same chiral representation are used, their commutators have the same sign and fail to produce the required cross-field cancellations. We must explicitly construct fields with opposite chirality orientations $\eta \in \{+1, -1\}$.

**Definition 15.1 (Oriented Chiral Fluctuation Field).**
For each species branch and assigned orientation $\eta$, the purely bosonic, Hermitian chiral fluctuation field is defined exactly as:

$$
\varphi_\eta(x) := i \sum_{m=1}^{h-1} \frac{1}{m} \left( \zeta^{\eta m x} \rho_{-m, \eta} - \zeta^{-\eta m x} \rho_{m, \eta} \right) \tag{15.1}
$$

*Lean 4 Proof Strategy:*
Define `chiralFluctuationField (η : Int) (x : Int) : OperatorAlgebra` (where $\eta$ is strictly constrained to $\pm 1$) as a `Finset` sum over `m ∈ Ico 1 h`. The character $\zeta$ should be treated as a primitive $L$-th root of unity (e.g., via `Complex.exp` or a purely algebraic root). The modes $\rho_{m, \eta}$ should be represented as a map `rho : Int → Int → OperatorAlgebra`. Since these represent independent physics branches, state an explicit physical axiom that opposite orientation branches commute: `[rho m 1, rho n (-1)] = 0`.

By reversing the spatial character, opposite orientations yield opposite chiral kernels while retaining the same standard current modes.

**Lemma 15.2 (Hermiticity).**
Because $\rho_{-m} = \rho_m^\dagger$, conjugating the roots exactly flips the sum, proving strict self-adjointness: $\varphi_\eta^\dagger(x) = \varphi_\eta(x)$.

*Lean 4 Proof Strategy:*
Assuming `OperatorAlgebra` implements a `StarRing` typeclass, state the lemma as `star (chiralFluctuationField η x) = chiralFluctuationField η x`. The proof will require applying `star_sum`, `star_mul`, and `star_sub` inside the `Finset` sum. Since `star (ζ) = ζ⁻¹` and `star (rho m η) = rho (-m) η`, conjugating the terms effectively swaps the two components of the subtraction. An auxiliary lemma to formalize the negation swap inside the summand will close the proof.

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
Define `phiField (x : Int) := chiralFluctuationField 1 x + chiralFluctuationField (-1) x` and `thetaField (x : Int) := chiralFluctuationField 1 x - chiralFluctuationField (-1) x`.

**Lemma 15.4 (Exact Field Commutators).**
Using the explicit orientation signs and evaluating on the Kac-Moody budget, the identical-branch commutators cancel correctly, producing the desired macroscopic field commutators with an explicit lattice kernel:

$$
[\phi(x), \phi(y)] = 0, \quad [\theta(x), \theta(y)] = 0 \tag{15.4}
$$

$$
[\phi(x), \theta(y)] = 2i \sum_{m=1}^{h-1} \frac{2}{m} \sin\left(\frac{2\pi m (x-y)}{L}\right) I =: 2i C(x,y) I \tag{15.5}
$$

*Lean 4 Proof Strategy:*
Using the bilinearity of the Lie bracket (`⁅_, _⁆`), expand the definitions of $\phi$ and $\theta$ into four cross-commutators. By the axiom that opposite chiral branches commute, cross-terms like `⁅chiralFluctuationField 1 x, chiralFluctuationField (-1) y⁆` vanish. The remaining terms are identical-branch commutators. For $\phi$ and $\theta$ self-commutators, these identical-branch commutators are combined with a minus sign and cancel out. For the mixed $\phi, \theta$ commutator, they sum together, yielding the exact finite lattice kernel evaluated via the Kac-Moody budget `[rho_m, rho_{-m}] = m * I`. An auxiliary lemma converting complex exponentials $\zeta - \zeta^{-1}$ to $2i \sin$ will cleanly express the final kernel.

#### 15.3 Exact Gradients and the Zero-Mode Obstruction

**Physical Intuition (Exact Forward Difference):**
To define $\partial_x \phi \propto \rho$ strictly algebraically, we use the exact discrete forward difference $\Delta_x f(x) = f(x+1) - f(x)$.

**Lemma 15.5 (Exact Gradient).**
Applying $\Delta_x$ explicitly evaluates to:

$$
(\Delta \varphi_\eta)(x) = i \sum_{m=1}^{h-1} \frac{1}{m} \left( (\zeta^{\eta m} - 1)\zeta^{\eta m x} \rho_{-m, \eta} - (\zeta^{-\eta m} - 1)\zeta^{-\eta m x} \rho_{m, \eta} \right) \tag{15.6}
$$

*Lean 4 Proof Strategy:*
Define a forward difference operator for functions mapping into the operator algebra: `forwardDiff (f : Int → OperatorAlgebra) (x : Int) := f (x + 1) - f x`. Apply it to `chiralFluctuationField` and pull the difference operation inside the `Finset.sum` using the linearity of sums. The proof is a purely algebraic manipulation factoring out `ζ^{±η m x}` from `ζ^{±η m (x+1)} - ζ^{±η m x}`.

*(Note: The factor $(\zeta^m - 1)/m$ is strictly not a constant, and low-momentum limits must not be taken to falsely assert an exact lattice identity).*

**Theorem 15.6 (The Zero-Mode Obstruction).**
Summing any periodic forward difference over the lattice identically yields zero. However, the standard band-limited Dirichlet delta kernel $\delta_M(x-y) = \frac{1}{L}\sum \zeta^{m(x-y)}$ contains a zero-mode $m=0$ and sums to 1.
Therefore, a naive exact lattice equation $[\phi(x), (\Delta\theta)(y)] \propto \delta_M(x-y)$ is mathematically impossible. The actual commutator of periodic fluctuation fields strictly has zero spatial average. We must retain the exact differentiated finite kernel without analytically equating it to a constant times $\delta_M$.

$$
[\phi(x), (\Delta \theta)(y)] = \Delta_y [ \phi(x), \theta(y) ] = 2i \Delta_y C(x,y) I \tag{15.7}
$$

*Lean 4 Proof Strategy:*
State and prove a foundational discrete calculus lemma: the sum of a forward difference over a full period is exactly zero, `∑ x ∈ Ico 0 L, forwardDiff f x = 0`, proven via a telescoping sum argument. Because both $\phi$ and $\theta$ are built solely from $m \neq 0$ fluctuation modes, their resulting commutator's forward difference must mathematically sum to zero over space. In contrast, the Dirichlet kernel sum evaluates to 1 because of the zero-mode $m=0$ contribution. Conclude the theorem by establishing that `sum ⁅phiField x, forwardDiff thetaField y⁆ ≠ c * sum δ_M` for any non-zero constant `c`, which formally proves the obstruction.

#### 15.4 Technical Notes for the Lean 4 Formalization (Chapter 15)

1. **Non-commutative Spatial Differences:**
   * Chapter 2's Umbral calculus `forwardDiff` relies on a commutative coefficient ring. The algebra of operator-valued fields $\mathrm{End}_{\mathbb{C}}(V)$ is non-commutative.
   * You cannot blindly instantiate `forwardDiff` for endomorphisms. You must define a specific module-valued linear map or use explicit algebraic subtraction $A(x+1) - A(x)$ to evaluate differences without assuming operator commutativity.
2. **Kernels as Character Sums:**
   * Define all kernels explicitly as finite `Finset` sums of characters $\zeta$. Only as a secondary evaluation (valid away from $t=0$) should you prove equivalence to quotients of sines. At $t=0$, division by zero is undefined, whereas the character sum exactly yields $(2M+1)/L$.
