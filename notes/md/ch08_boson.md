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

**Definition 8.2 (Operators, Currents, and Adjoint Form).**
For each mode $m \in Q$, the algebraic operators on $\mathcal{F}_b$ are defined as:
1. **Creation and Annihilation Derivatives:**
$$
X_m \cdot p, \qquad D_m p := \frac{\partial}{\partial X_m} p \tag{8.2}
$$
2. **Inner Product and Adjoint Selection:**
On monomials $X^r = \prod X_m^{r_m}$, the standard factorial form $w_{\mathrm{std}}(r) = \prod_m r_m!$ makes $D_m$ adjoint to $X_m$.
For the chiral density current theory, we select the **Haldane inner product** with weight:
$$
w(r) := \prod_{m \in Q} m^{r_m} r_m! \tag{8.3}
$$
Under this form, the annihilation operator $A_m := m D_m$ is the exact Hilbert adjoint of the creation operator $C_m := X_m$:
$$
C_m := X_m, \qquad A_m := m \frac{\partial}{\partial X_m}, \qquad A_m^\dagger = C_m
$$
Under the Haldane form, $D_m$ alone is not the adjoint of $X_m$ for $m > 1$; we reserve the adjoint dagger strictly for the selected Haldane inner product.

3. **Bosonic Number and Energy Observables:**
We explicitly define the total bosonic number operator $\hat{N}_b$ and the chiral bosonic Hamiltonian $\hat{H}_b$:
$$
\hat{N}_b := \sum_{m \in Q} X_m D_m = \sum_{m \in Q} \frac{1}{m} C_m A_m \tag{8.4}
$$
$$
\hat{H}_b := \sum_{m \in Q} m X_m D_m = \sum_{m \in Q} C_m A_m \tag{8.5}
$$
On a single-mode state $X_m$, $\hat{N}_b X_m = X_m$ (eigenvalue 1) and $\hat{H}_b X_m = m X_m$ (eigenvalue $m$).

*Lean 4 Proof Strategy:*
Define $C_m$ as `LinearMap.mulLeft ℂ (MvPolynomial.X m)` and $A_m$ as `m • MvPolynomial.pderiv m`. Define the Haldane bilinear form on monomials with weight $w(r)$. Prove $\langle C_m P, Q \rangle = \langle P, A_m Q \rangle$. Define $\hat{N}_b$ and $\hat{H}_b$ as linear combinations of $C_m \circ A_m$.

#### 8.2 Filtrations and Nilpotency

**Definition 8.3 (Weight Filtration).**
Let $\mathcal{F}_{\le K}$ be the finite-dimensional vector subspace consisting of polynomials whose weighted degree is bounded by $K$:
$$
\mathcal{F}_{\le K} := \mathrm{span}_{\mathbb{C}} \left\{ \prod X_m^{r_m} \mathrel{\Bigg\vert{}} \sum m \cdot r_m \le K \right\} \tag{8.6}
$$

*Lean 4 Proof Strategy:*
Define a custom weight function `weightedDegree : MvPolynomial Q ℂ → ℕ` mapping monomials $\prod X_m^{r_m}$ to $\sum m \cdot r_m$ using `Finsupp.sum`. Define $\mathcal{F}_{\le K}$ as the submodule of polynomials bounded by this weight. To prove strict nilpotency of $A_m$ on this subspace, show that `MvPolynomial.pderiv m` strictly decreases the power of $X_m$, thus taking a sufficiently high power of the derivative evaluates to $0$ on any restricted subspace of bounded weight.

On this finite subspace, the annihilation operator $A_m$ is strictly **nilpotent**. The creation operator $C_m$ maps outside the subspace. If a compressed endomorphism is needed, we define $\tilde{C}_m := P_K \circ C_m$. While compressed creators are nilpotent, their commutator with derivatives has a boundary term and is no longer central. We rely on the ambient infinite-dimensional space for exact global algebraic properties.

*Correction to No-Go Theorems:*
A Heisenberg Lie algebra *does* have nontrivial finite-dimensional representations (e.g., where the central element acts non-invertibly or by zero). The strict no-go theorem (Lemma 2.6 trace argument) only forbids a commutator from equaling a *nonzero scalar identity* on a nonzero carrier in characteristic zero. Our compressed algebra satisfies this because the boundary terms force the trace to exactly zero.

#### 8.3 Lie Algebras and Exact Commutators

**Lemma 8.4 (Exact CCR / Heisenberg Lie Algebra).**
For all $m, m' \in Q$, the CCR holds as an exact algebraic identity on the uncompressed infinite-dimensional polynomial ring:
$$
[A_m, C_{m'}] = m \delta_{mm'} I, \quad [A_m, A_{m'}] = 0, \quad [C_m, C_{m'}] = 0 \tag{8.7}
$$

*Lean 4 Proof Strategy:*
Formalize commutators of linear maps as `[A, B] = A ∘ B - B ∘ A`. The relation $[A_m, C_{m'}] = m \delta_{mm'} I$ translates to `m • pderiv m ∘ (X m' *) - (X m' *) ∘ (m • pderiv m) = if m = m' then m • id else 0`. Prove this using the Leibniz rule `MvPolynomial.pderiv_mul`.

**Lemma 8.5 (Baker-Campbell-Hausdorff and Exponentials).**
Because the uncompressed commutator is a scalar identity, BCH truncates exactly. We formalize exponentials over a formal parameter $t$. For scalars $\alpha, \beta$:
$$
e^{t \alpha A_m} e^{t \beta C_{m'}} = e^{t \beta C_{m'}} e^{t \alpha A_m} e^{t^2 m \alpha \beta \delta_{mm'} I} \tag{8.8}
$$
*Note: Because compressed creators are not central, they do not inherit this scalar BCH relation. For bounded Wick identities, we strictly use direct word induction.*

*Lean 4 Proof Strategy:*
Formalize these operations in a ring of formal power series `PowerSeries (End (MvPolynomial Q ℂ))` over $t$. Define an auxiliary lemma for operators $A, B$ that commute with their commutator $[A, B]$, leading to the exact truncation of the BCH expansion.

#### 8.4 Wick's Theorem and Exponentials

For a truly nilpotent endomorphism $A$ with $A^{d+1}=0$ on its carrier, we define `expNil(A) = \sum_{j=0}^d A^j / j!`. We do not name an arbitrary Taylor polynomial the exact exponential of an unprojected operator.

**Theorem 8.6 (Wick's Theorem and Polynomials).**
Any product of linear bosonic operators can be written as a sum of normal-ordered products. For the symmetric combination $\hat{x}_m := D_m + X_m$:
$$
(\hat{x}_m)^n = \sum_{k=0}^{\lfloor n/2 \rfloor} \frac{n!}{k!(n-2k)! 2^k} :(\hat{x}_m)^{n-2k}: \tag{8.9}
$$
Evaluating this on the vacuum state $1 \in \mathcal{F}_b$ yields the polynomial $P_n(X) := (D_m + X_m)^n 1$, which satisfies the recurrence:
$$
P_{n+1}(X) = X P_n(X) + P_n'(X) = X P_n(X) + n P_{n-1}(X)
$$
with formal generating function $\sum_{n=0}^\infty P_n(X) \frac{t^n}{n!} = \exp\left( Xt + \frac{t^2}{2} \right)$.
*(Note on Hermite polynomials: The probabilists' Hermite polynomials $\mathrm{He}_n(X)$, with $\mathrm{He}_2(X) = X^2 - 1$ and generating function $\exp(Xt - t^2/2)$, correspond instead to the operator $(X_m - D_m)^n 1$ with a signed contraction. For $(D+X)^2 1 = X^2 + 1$, the vacuum state generates $P_n(X)$ with positive signs).*

*Lean 4 Proof Strategy:*
Define normal ordering `: :` structurally by moving all derivatives $D_m$ to the right of multiplications $X_m$. Proceed by induction on $n$. Prove the recurrence $P_{n+1} = X P_n + n P_{n-1}$ by induction on $n$ with coefficients in $\mathbb{Z}$, then cast to $\mathbb{C}$.
