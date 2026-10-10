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
Use `Fin M` with positive weight `weight i := i.val + 1`, or the subtype of positive modes at most M. The zero-based value alone is not a mode weight: it would make a fixed weight slice infinite-dimensional. Define the carrier `MvPolynomial Q ℂ` and constant vacuum 1.

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
Use the checked creator `LinearMap.mulLeft ℂ (MvPolynomial.X i)` and derivative `(MvPolynomial.pderiv i).toLinearMap`: `pderiv` is a bundled derivation. Scale it by the positive mode weight. Define the Haldane Hermitian form by finite support sums, conjugate-linear in the first argument and linear in the second, and prove the creator/annihilator pairing identity on monomials.

#### 8.2 Filtrations and Nilpotency

**Definition 8.3 (Weight Filtration).**
Let $\mathcal{F}_{\le K}$ be the finite-dimensional vector subspace consisting of polynomials whose weighted degree is bounded by $K$:
$$
\mathcal{F}_{\le K} := \mathrm{span}_{\mathbb{C}} \left\{ \prod X_m^{r_m} \mathrel{\Bigg\vert{}} \sum m \cdot r_m \le K \right\} \tag{8.6}
$$

*Lean 4 Proof Strategy:*
Define the budget as the span of bounded-weight monomials, equivalently requiring every supported monomial to have weight at most K. Prove closure under addition/scalars, finiteness of its index set from positive weights, and the derivative grading. These establish finite dimension and power vanishing; finite dimension alone is insufficient.

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
Define a formal exponential coefficient by `((j! : ℂ)⁻¹) • A^j` in a series carrier that supports noncommutative coefficients and a central parameter. Check the installed series API before choosing it, or prove finite coefficient identities modulo a power of t. `PowerSeries.exp` takes a coefficient type, not an operator; do not apply ambient scalar BCH to compressed creators.

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
Define normal symbols separately from represented words, with a fixed ordered linear evaluation. Prove the word expansion including contractions by induction, then derive the vacuum recurrence. Ignoring contractions is not a well-defined operation on the represented operator algebra.

#### 8.5 Constructive realization in Lean

The construction in [the Lean chapter](../../Bosonize/Core/Ch08Boson.lean) realizes the algebraic oscillator theory above on finitely supported polynomials. Its [companion notebook](../../docs/companion/Bosonize/Core/Ch08Boson.md) records the exact declarations and verification evidence. The mathematical discussion here explains how the realization works and where its scope differs from the broader reference theory.

**Positive modes and the weighted form.** The variables are indexed by a finite set of size $M$, with the positive weight of index $i$ equal to $i+1$. Thus the variable labels start at zero in the implementation, while the physical oscillator weights remain $1,\ldots,M$. An occupation vector $r$ determines the monomial $X^r$, particle number $\sum_i r_i$, and energy $E(r)=\sum_i(i+1)r_i$. The vacuum is the constant polynomial $1$. Constants remain a legitimate carrier when $M=0$; assertions about a selected mode require that such a mode actually exists.

For polynomials $p=\sum_r p_rX^r$ and $q=\sum_r q_rX^r$, the chosen form is
$$
\langle p,q\rangle_H=\sum_r\overline{p_r}\,w(r)q_r,
\qquad w(r)=\prod_i(i+1)^{r_i}r_i!.
$$
Only finitely many coefficients contribute. Positive mode weights make every $w(r)$ positive, so the form is Hermitian, positive, and definite. Its positivity follows directly from $\langle p,p\rangle_H=\sum_r w(r)|p_r|^2$; equality to zero forces every coefficient to vanish. No infinite sum or Hilbert-space completion is needed for this argument.

Multiplication by $X_i$ raises an occupation, while differentiation lowers it and multiplies by $r_i$. The identity
$$
w(r+e_i)=(i+1)(r_i+1)w(r)
$$
therefore gives $\langle C_i p,q\rangle_H=\langle p,A_iq\rangle_H$, where $A_i=(i+1)D_i$. This is the precise algebraic realization of the adjoint language in §8.1. The ambient carrier has a verified pairing identity; genuine Hilbert adjoints are constructed on the finite carriers below. On monomials, the number and Hamiltonian operators have eigenvalues $\sum_i r_i$ and $E(r)$ respectively.

**A finite carrier constructed from an energy budget.** Positivity of the weights implies $r_i\le K$ whenever $E(r)\le K$. The finite box $\{0,\ldots,K\}^M$ therefore contains every admissible occupation. Filtering this box by the energy inequality gives an explicit finite indexing set $I_K$. The budget is exactly the span of its monomials, and a polynomial lies in it precisely when every nonzero coefficient has energy at most $K$.

The genuine finite Hilbert space is $\mathbb C^{I_K}$ with its usual inner product. Its coordinate ket $e_r$ is embedded as
$$
U_Ke_r=\frac{X^r}{\sqrt{w(r)}}.
$$
The reverse coordinate map reads each coefficient and multiplies it by $\sqrt{w(r)}$. These maps satisfy $V_KU_K=I$, while $U_KV_K=P_K$ is the monomial projection that discards occupations of energy greater than $K$. The embedding preserves the inner product and has exactly the budget as its range. This supplies finite dimension through an actual finite basis. It also proves that the finite vacuum is nonzero, including at budget zero.

Creation raises energy by $i+1$. Annihilation lowers it by that weight and kills the whole budget when $K<i+1$. Repeated annihilation eventually vanishes because no occupation can be lowered indefinitely. The compressed creator likewise eventually vanishes because every surviving creation raises energy until it leaves the budget. Both compressed maps have the conservative power cutoff $K+1$. Ambient creation has a different behavior: its $n$th power sends the vacuum to the nonzero monomial $X_i^n$ for every $n$.

Transporting an ambient operator by $V_KAU_K$ defines its finite realization. The pairing identity yields the actual finite creator–annihilator adjoint relation. Number and energy become self-adjoint maps; the normalized kets are energy eigenvectors with eigenvalues $E(r)$.

**Why the projection remainder is part of the mathematics.** On the ambient polynomial carrier, the Leibniz rule gives $[A_i,C_j]=(i+1)\delta_{ij}I$, and creators commute with creators and annihilators with annihilators. For a projection $P$, the exact compressed identity is
$$
[PAP,PBP]=P[A,B]P-PA(I-P)BP+PB(I-P)AP.
$$
The additional terms measure excursions through the discarded part of the carrier. They cannot generally be omitted. Indeed, the trace of a commutator on the nonzero finite Hilbert space is zero, whereas the trace of $(i+1)I$ is positive. Thus the finite creator and annihilator cannot satisfy the ambient nonzero scalar CCR. Nilpotency and this obstruction are compatible consequences of the finite truncation.

**Finite exponentials and formal identities.** A Taylor sum is defined for every finite operator. Calling it the exact nilpotent exponential requires the explicit certificate $A^{d+1}=0$. Under that certificate, enlarging the Taylor cutoff does not change the sum, and the sum for $-A$ is its inverse. Taking the finite Hilbert adjoint commutes with the Taylor construction because its factorial coefficients are real.

Ambient exponentials use a formal parameter: an operator sequence has a finite convolution sum at each degree. Associativity is proved by reindexing those finite sums while preserving operator order. The BCH identity in §8.3 is an equality of these coefficients, with the central correction present at even degrees. It makes no assertion about analytic convergence or evaluation of the parameter, and it applies to ambient scalar-CCR operators rather than arbitrary compressed maps.

**Normal ordering and the positive contraction.** For one selected mode, a normal symbol is a finite linear combination of pairs $(a,b)$, evaluated as $C_i^aD_i^b$. The evaluation is linear; multiplying represented operators can produce contractions. Every Boolean word in that mode's creator and derivative has such a normal expansion. This verifies the single-mode word statement; a general multivariate normal-symbol dictionary remains a further extension of the opening reference claim in §8.4.

Writing $N_n=\sum_{j=0}^n\binom nj C_i^jD_i^{n-j}$, the basic commutator $[D_i,C_i]=I$ gives
$$
(D_i+C_i)N_{n+1}=N_{n+2}+(n+1)N_n.
$$
This recurrence, together with the factorial coefficient recurrence, proves the full operator Wick expansion (8.9). On the vacuum, all terms containing a positive derivative power vanish, so $N_n1=X_i^n$. The operator expansion then yields the coefficientwise generating identity for $P_n$. Independently, the Appell derivative and the vacuum recurrence give $P_{n+1}=X_iP_n+nP_{n-1}$. The positive sign is essential: $P_2=X_i^2+1$, while the separately defined Hermite convention gives $X_i^2-1$.

**The later fermion comparison retains its parameters.** This chapter constructs the abstract oscillator target without a fermionic twist parameter. That choice does not prove that a later physical observable is independent of the twist. The actual twisted fermion operators, transport and holonomy remain supplied by Chapter 6's extension. Subsequent density and current constructions must prove cancellation on their own bilinears and on their stated budgets before identifying them with these oscillator operators. Sector-dependent zero modes remain explicit in the later vertex construction.
