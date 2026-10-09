### Chapter 8: The Umbral Boson Fock Layer

*Context: This chapter constructs a purely algebraic framework for bosonic operators as the target space for Phase 2.*

To sidestep infinite-dimensional topological vector spaces, we employ an **umbral (polynomial) approach**. The bosonic Fock space is realized purely algebraically on a multivariate polynomial ring. The mathematical formulation follows [Appendix A02](../appendices/a02_car_hilbert_and_normal_ordering.md), [Appendix A03](../appendices/a03_energy_budgets_and_filtered_maps.md), and [Appendix A05](../appendices/a05_exponentials_klein_and_vertex_scope.md).

#### 8.1 Carrier Space and Operators

**Definition 8.1 (Bosonic Carrier Space).**
Let $Q = \{1, \dots, M\}$ be a finite set of positive integer mode indices. The algebraic carrier space $\mathcal{F}_b$ is the commutative ring of multivariate polynomials:
$$
\mathcal{F}_b := \mathbb{C}[X_1, \dots, X_M] \tag{8.1}
$$
The vacuum state is the constant polynomial $1 \in \mathcal{F}_b$.

*Lean 4 Proof Strategy:*
Formalize the index set as `Q := Fin M` or `Q := { i : ℕ // 1 ≤ i ∧ i ≤ M }`. Define the algebraic carrier space $\mathcal{F}_b$ as the ring of multivariate polynomials `MvPolynomial Q ℂ`. The vacuum state $|0\rangle$ is defined as the constant polynomial `MvPolynomial.C 1`.

**Definition 8.2 (Operators and Currents).**
For every $m \in Q$, the creation and annihilation operators are linear endomorphisms:
$$
a_m^\dagger(p) := X_m \cdot p \tag{8.2}
$$
$$
a_m(p) := \frac{\partial}{\partial X_m} p \tag{8.3}
$$
The unnormalized currents are $J_m^\dagger := a_m^\dagger$ and $J_m := m \, a_m$.

*Lean 4 Proof Strategy:*
Define $a_m^\dagger$ as a linear map on `MvPolynomial Q ℂ` corresponding to left multiplication by the indeterminate: `LinearMap.mulLeft ℂ (MvPolynomial.X m)`. Define $a_m$ using the formal partial derivative: `MvPolynomial.pderiv m`. The currents are constructed by scalar multiplication of these linear maps.

#### 8.2 Filtrations and Nilpotency

**Definition 8.3 (Weight Filtration).**
Let $\mathcal{F}_{\le K}$ be the finite-dimensional vector subspace consisting of polynomials whose weighted degree is bounded by $K$:
$$
\mathcal{F}_{\le K} := \mathrm{span}_{\mathbb{C}} \left\{ \prod X_m^{r_m} \mathrel{\Bigg\vert{}} \sum m \cdot r_m \le K \right\} \tag{8.4}
$$

*Lean 4 Proof Strategy:*
Define a custom weight function `weightedDegree : MvPolynomial Q ℂ → ℕ` mapping monomials $\prod X_m^{r_m}$ to $\sum m \cdot r_m$ using `Finsupp.sum`. Define $\mathcal{F}_{\le K}$ as the submodule of polynomials bounded by this weight. To prove strict nilpotency of $a_m$ on this subspace, show that `MvPolynomial.pderiv m` strictly decreases the power of $X_m$, thus taking a sufficiently high power of the derivative evaluates to $0$ on any restricted subspace of bounded weight.

On this finite subspace, the annihilation operator $a_m$ is strictly **nilpotent**. The creation operator $a_m^\dagger$ maps outside the subspace. If a compressed endomorphism is needed, we define $\tilde{a}_m^\dagger := P_K \circ a_m^\dagger$. While compressed creators are nilpotent, their commutator with derivatives has a boundary term and is no longer central. We rely on the ambient infinite-dimensional space for exact global algebraic properties.

*Correction to No-Go Theorems:*
A Heisenberg Lie algebra *does* have nontrivial finite-dimensional representations (e.g., where the central element acts non-invertibly). The strict no-go theorem (Lemma 2.9) only forbids a commutator from equaling a *nonzero scalar identity* in characteristic zero. Our compressed algebra satisfies this because the boundary terms force the trace to exactly zero.

#### 8.3 Lie Algebras and Exact Commutators

**Lemma 8.4 (Exact CCR / Heisenberg Lie Algebra).**
For all $m, m' \in Q$, the CCR holds as an exact algebraic identity on the uncompressed infinite-dimensional polynomial ring:
$$
[a_m, a_{m'}^\dagger] = \delta_{mm'} I, \quad [a_m, a_{m'}] = 0, \quad [a_m^\dagger, a_{m'}^\dagger] = 0 \tag{8.5}
$$

*Lean 4 Proof Strategy:*
Formalize commutators of linear maps as `[A, B] = A ∘ B - B ∘ A`. The relation $[a_m, a_{m'}^\dagger] = \delta_{mm'} I$ translates to showing `pderiv m ∘ (X m' *) - (X m' *) ∘ pderiv m = if m = m' then LinearMap.id else 0`. Prove this by applying both sides to a generic polynomial `P` and utilizing the Leibniz rule for formal derivatives (`MvPolynomial.pderiv_mul`). The vanishing commutators follow from `MvPolynomial.pderiv_comm` (Clairaut's theorem for formal polynomials) and commutativity of polynomial multiplication.

**Lemma 8.5 (Baker-Campbell-Hausdorff and Exponentials).**
Because the uncompressed commutator is a scalar identity, BCH truncates exactly. We formalize exponentials over a formal parameter $t$. For scalars $\alpha, \beta$:
$$
e^{t \alpha a_m} e^{t \beta a_{m'}^\dagger} = e^{t \beta a_{m'}^\dagger} e^{t \alpha a_m} e^{t^2 \alpha \beta \delta_{mm'} I} \tag{8.6}
$$
*Note: Because compressed creators are not central, they do not inherit this scalar BCH relation. For bounded Wick/Hermite identities, we strictly use direct word induction.*

*Lean 4 Proof Strategy:*
Formalize these operations in a ring of formal power series `PowerSeries (End (MvPolynomial Q ℂ))` over $t$. Define an auxiliary lemma for operators $A, B$ that commute with their commutator $[A, B]$, leading to the exact truncation of the BCH expansion. Alternatively, avoid full formal series and prove this by evaluating Taylor truncations up to a fixed degree acting on $\mathcal{F}_{\le K}$, relying on nilpotency bounds for convergence.

#### 8.4 Wick's Theorem and Exponentials

For a truly nilpotent endomorphism $A$ with $A^{d+1}=0$ on its carrier, we define `expNil(A) = \sum_{j=0}^d A^j / j!`. We do not name an arbitrary Taylor polynomial the exact exponential of an unprojected operator.

**Theorem 8.6 (Wick's Theorem).**
Any product of linear bosonic operators can be written as a sum of normal-ordered products. For an unnormalized position operator $\hat{x}_m := a_m + a_m^\dagger$:
$$
(\hat{x}_m)^n = \sum_{k=0}^{\lfloor n/2 \rfloor} \frac{n!}{k!(n-2k)! 2^k} :(\hat{x}_m)^{n-2k}: \tag{8.7}
$$
Evaluating this on the vacuum state yields the probabilist's Hermite polynomials.

*Lean 4 Proof Strategy:*
Define normal ordering `: :` structurally by moving all `a_m` operators (`MvPolynomial.pderiv`) to the right of `a_m^\dagger` operators (`X *`). Proceed by induction on $n$. For the inductive step, apply $(a_m + a_m^\dagger)$ to the expansion for $n$. Distribute and use the CCR identity $[a_m, (a_m^\dagger)^p] = p (a_m^\dagger)^{p-1}$ (proved via an auxiliary induction on $p$) to commute the new $a_m$ past creation operators. This generates the expected combinatorial contraction terms. The combinatorial coefficients will satisfy the standard Hermite polynomial recurrence relation, verified using Mathlib's binomial coefficients (`Nat.choose`).
