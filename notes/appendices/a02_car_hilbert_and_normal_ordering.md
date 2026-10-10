# Appendix A02 proposal: CAR carriers, adjoints, and normal ordering

## 1. Carrier Conventions & The Two-Tiered CAR Hierarchy

A bare function space $X \to \mathbb{C}$ is algebraically convenient but does not automatically carry the sum-of-squares Euclidean norm. Its usual product norm and the Euclidean norm should not be conflated by installing incompatible instances.

In Lean 4 (`Bosonize.A02`), we cleanly separate purely algebraic relations from Hilbert-space inner products by establishing a two-tiered algebraic hierarchy:

### Tier 1: Abstract Algebraic CAR (`Bosonize.A02.AlgebraicCAR`)
Let $V$ be any complex vector space (`[AddCommGroup V] [Module ℂ V]`), and $\iota$ a finite index set with decidable equality (`[DecidableEq ι]`).
An algebraic CAR system consists of two families of endomorphisms $c^{\phantom{\dagger}}, c^\dagger : \iota \to \mathrm{End}_{\mathbb{C}}(V)$ satisfying:

1. $\{c_i, c_j\} = 0$
2. $\{c_i^\dagger, c_j^\dagger\} = 0$
3. $\{c_i^{\phantom{\dagger}}, c_j^\dagger\} = \delta_{ij} I_V$
where $\{A, B\} := AB + BA$.

*Purely Algebraic Consequences (`A02.AlgebraicCAR`):*
Without any inner product or metric structure, the algebraic relations alone formally imply:

- **Bilinear Commutator Identity (`car_bilinear_commutator`):**
  $$
  [c_a^\dagger c_b^{\phantom{\dagger}}, c_c^\dagger c_d^{\phantom{\dagger}}] = \delta_{bc} c_a^\dagger c_d^{\phantom{\dagger}} - \delta_{ad} c_c^\dagger c_b^{\phantom{\dagger}} \tag{A02.1}
  $$
- **Number-Creation/Annihilation Commutators (`car_number_creation_commutator`, `car_number_annihilation_commutator`):**
  $$
  [n_i, c_j^\dagger] = \delta_{ij} c_j^\dagger, \qquad [n_i, c_j^{\phantom{\dagger}}] = -\delta_{ij} c_j^{\phantom{\dagger}} \tag{A02.2}
  $$
- **Number Idempotence and Commutativity (`car_number_idempotent`, `car_number_commute`):**
  $$
  n_i^2 = n_i, \qquad [n_i, n_j] = 0 \tag{A02.3}
  $$

### Tier 2: Hilbert Space CAR (`Bosonize.A02.CAR`)
When $V$ is a finite-dimensional complex Euclidean space (`[NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]`), the structure `CAR ι V` extends `AlgebraicCAR ι V` by bundling the true Hilbert adjoint condition:
$$
\forall i \in \iota, \quad c_i^\dagger = (c_i^{\phantom{\dagger}})^\dagger \tag{A02.4}
$$
*Why this distinction is foundational:* An algebraic CAR pair can be conjugated by an arbitrary invertible non-unitary operator $S \in \mathrm{GL}(V)$; the transformed operators $S c_i S^{-1}$ and $S c_i^\dagger S^{-1}$ still satisfy all three anticommutation relations (Tier 1), but they completely lose Hilbert adjointness ($S c_i^\dagger S^{-1} \ne (S c_i^{\phantom{\dagger}} S^{-1})^\dagger$). Adjoint compatibility is therefore an independent geometric property.

---

## 2. Concrete Occupation Space and Basis Extension

**The Concrete Carrier:**
For any finite set $\iota$, the fermionic Fock space is defined over the power set (the finite subsets $\mathcal{P}(\iota) \equiv \mathrm{Finset} \ \iota$):
$$
\mathrm{FockSpace}(\iota) := \ell^2(\mathrm{Finset} \ \iota) \equiv \mathrm{EuclideanSpace} \ \mathbb{C} \ (\mathrm{Finset} \ \iota) \tag{A02.5}
$$
The standard orthonormal basis vectors are denoted $\mathrm{ket}(S) \equiv |S\rangle$ for each subset $S \subseteq \iota$.

- Dimension (`fock_finrank`): $\dim_{\mathbb{C}}(\mathrm{FockSpace}(\iota)) = 2^{|\iota|}$.
- Inner product (`fock_inner`): $\langle u \mid v \rangle = \sum_{S \subseteq \iota} \overline{u(S)} v(S)$.
- Basis orthonormality (`ket_inner`): $\langle \mathrm{ket}(S) \mid \mathrm{ket}(T) \rangle = \delta_{S, T}$.

**Constructing Operators via Basis Extension (`extendBasis`):**
Linear maps on $\mathrm{FockSpace}(\iota)$ are constructed by specifying their action on basis vectors using `Module.Basis.constr`:
$$
\mathrm{extendBasis}(F) := \left( v = \sum_S v(S) |S\rangle \right) \mapsto \sum_S v(S) F(S) \tag{A02.6}
$$
Evaluating on basis vectors satisfies `extendBasis(F)(ket S) = F(S)` identically (`extend_basis_ket`).

---

## 3. Required CAR Lemma Chain & Additive Mechanics

**Lemma 1 & 2 (Atomic Additive Counts, avoiding Nat underflow):**
Define the preceding occupied count $\sigma(i, S) := \#\{j \in S \mid j < i\}$. In Lean (`Ch04CARFock.lean`), the count is formalized additively using `Finset.filter`:

- For $j \notin S$: $\sigma(i, S \cup \{j\}) = \sigma(i, S) + \begin{cases} 1 & \text{if } j < i \\ 0 & \text{otherwise} \end{cases}$ (`preceding_count_insert`)
- For $j \in S$: $\sigma(i, S) = \sigma(i, S \setminus \{j\}) + \begin{cases} 1 & \text{if } j < i \\ 0 & \text{otherwise} \end{cases}$ (`preceding_count_erase`)
- Boundary values: $\sigma(i, S \cup \{i\}) = \sigma(i, S)$ and $\sigma(i, S \setminus \{i\}) = \sigma(i, S)$.
*Significance:* By phrasing the erasure count as $\sigma(i, S) = \sigma(i, S \setminus \{j\}) + [j < i]$ rather than with subtraction, we eliminate natural number underflow (`0 - 1 = 0` in $\mathbb{N}$) and allow purely additive cancellation.

**Lemma 3 (Permutation Sign Algebra):**
Let $\epsilon(i, S) := (-1)^{\sigma(i, S)} \in \mathbb{C}$ (`fermionSign`). For any distinct modes $i \ne j$:

1. `sign_insert_insert`: $\epsilon(j, S) \epsilon(i, S \cup \{j\}) = - \epsilon(i, S) \epsilon(j, S \cup \{i\})$ ($i, j \notin S$)
2. `sign_erase_erase`: $\epsilon(j, S) \epsilon(i, S \setminus \{j\}) = - \epsilon(i, S) \epsilon(j, S \setminus \{i\})$ ($i, j \in S$)
3. `sign_insert_erase`: $\epsilon(j, S) \epsilon(i, S \setminus \{j\}) = - \epsilon(i, S) \epsilon(j, S \cup \{i\})$ ($i \notin S, j \in S$)
*Proof:* In each case, whether $j < i$ or $i < j$, the total exponent of $(-1)$ on one side contains exactly one more preceding element than the other, introducing $(-1)^1 = -1$.

**Lemma 4 (Basis Action and CAR Anticommutation):**
Using `extendBasis`, define:
$$
c_i^{\phantom{\dagger}} |S\rangle := \begin{cases} \epsilon(i, S) |S \setminus \{i\}\rangle & \text{if } i \in S \\ 0 & \text{if } i \notin S \end{cases}, \qquad
c_i^\dagger |S\rangle := \begin{cases} \epsilon(i, S) |S \cup \{i\}\rangle & \text{if } i \notin S \\ 0 & \text{if } i \in S \end{cases}
$$
Applying both sides to any basis vector $|S\rangle$ and using the sign lemmas proves:
$$
\{c_i^{\phantom{\dagger}}, c_j^{\phantom{\dagger}}\} = 0, \qquad \{c_i^\dagger, c_j^\dagger\} = 0, \qquad \{c_i^{\phantom{\dagger}}, c_j^\dagger\} = \delta_{ij} I \tag{A02.7}
$$

**Lemma 5 (Adjointness via Basis Pairings):**
To establish $c_i^\dagger = (c_i^{\phantom{\dagger}})^\dagger$, evaluate the inner product pairing on arbitrary basis pairs $|S\rangle, |T\rangle$:
$$
\langle \mathrm{ket}(S) \mid c_i^{\phantom{\dagger}} \mathrm{ket}(T) \rangle = \langle c_i^\dagger \mathrm{ket}(S) \mid \mathrm{ket}(T) \rangle \tag{A02.8}
$$
Lean lifts this basis pairing to all vectors $u, v \in \mathrm{FockSpace}(\iota)$ via `A02.adjoint_of_basis_pairing` and `LinearMap.eq_adjoint_iff`, constructively providing the `adjoint_compat` field and proving `concrete_car_exists`.

**Lemma 6 (Number Observables and Sorted Parity Operator):**

- Number operator: $n_i := c_i^\dagger c_i^{\phantom{\dagger}}$. On basis states: $n_i |S\rangle = \begin{cases} 1 |S\rangle & \text{if } i \in S \\ 0 & \text{if } i \notin S \end{cases}$.
- Commutativity & Hermiticity: $[n_i, n_j] = 0$ and $n_i^\dagger = n_i$.
- **Global Parity Operator $\Gamma$:** Because $\mathrm{End}_{\mathbb{C}}(V)$ is non-commutative, the operator product over all modes must be defined with an explicit linear sort order (`Finset.sort (· ≤ ·) Finset.univ`):
  $$
  \Gamma := \prod_{i \in \mathrm{sort}(\le, \iota)} (I - 2 n_i) \tag{A02.9}
  $$
  On basis states: $\Gamma |S\rangle = (-1)^{|S|} |S\rangle$.
  Properties proved in Lean:
  $$
  \Gamma^2 = I, \qquad \Gamma^\dagger = \Gamma, \qquad \Gamma c_i^{\phantom{\dagger}} = - c_i^{\phantom{\dagger}} \Gamma, \qquad \Gamma c_i^\dagger = - c_i^\dagger \Gamma \tag{A02.10}
  $$

**Lemma 7:** Derive bilinear commutators from CAR. Reuse them in chapter 9 rather than giving duplicate implementations.

*Lean 4 Proof Strategy:*
Prove the CAR bilinear identity $[c_p^\dagger c_k^{\phantom{\dagger}},c_q^\dagger c_l^{\phantom{\dagger}}]=\delta_{kq}c_p^\dagger c_l^{\phantom{\dagger}}-\delta_{pl}c_q^\dagger c_k^{\phantom{\dagger}}$ by explicit distributivity and CAR. Reuse it to show dΓ preserves Lie brackets. A symmetric collection of swaps is not a terminating normal-order procedure.

> [!WARNING]
> **Proof-review correction (2026-10-09):** The previous four-factor formula, preserved in the checkpoint history, was withdrawn as a generic identity. Setting A=C=1 gives 3[B,D] on its right, instead of [B,D]. Prove and reuse the CAR bilinear identity $[c_p^\dagger c_k^{\phantom{\dagger}},c_q^\dagger c_l^{\phantom{\dagger}}]=\delta_{kq}c_p^\dagger c_l^{\phantom{\dagger}}-\delta_{pl}c_q^\dagger c_k^{\phantom{\dagger}}$ directly. An automatic swap rule also needs a fixed ordering and termination argument; symmetric CAR rewrites are not an unconditional `simp` procedure.

Products of operators in `Module.End` are noncommutative. A `Finset.prod` or `Multiset.prod` is not available merely because the particular number operators commute. Use a fixed ordered product and prove order independence, or use an API that takes explicit pairwise commutativity. The same issue occurs for partition-state products.

For species, choose an explicit lexicographic order/type synonym. Do not rely on a bare Cartesian product to silently select the required total order and phase convention.

## Local algebras and grading

Use `StarSubalgebra.adjoin` when the ambient operator algebra has a genuine adjoint star, or prove that the ordinary algebra generated by creators and annihilators is star closed. The odd part is a linear subspace, not a unital subalgebra. The even part is a subalgebra; parity decomposition uses division by two and Γ² = I.

**Lemma 8 (Graded-word lemma):** Prove a graded-word lemma, extend to the span of words of a fixed parity, and then identify these spans with the ±1 eigenspaces of parity.

*Lean 4 Proof Strategy:*
Define a grading `Z_2` on the free algebra of creators/annihilators. Show length `k` words have parity `k mod 2`. Since the operators map between parity eigenspaces of `Γ`, prove `Γ O Γ = (-1)^{parity(O)} O` for homogeneous words `O`. By linearity, extend this to the span of words of fixed parity, confirming the even/odd decomposition of the full algebra without needing component-wise adjoin induction.

For global irreducibility, construct occupation projectors and matrix units with a fixed ordered creation/annihilation string. Its nonzero sign may need to be divided out; it is not automatically +1.

## Polynomial adjoints without square-root bases

**Theorem 1:** On polynomial monomials X^r, define an algebraic Hermitian form with orthogonal monomials. For ordinary oscillators use weight `∏ r_m!`; then D_m and multiplication by X_m are adjoint. For the unnormalized currents used later, choose weight
$$
 w(r)=\prod_m m^{r_m}r_m!.
$$
Then `m D_m` is adjoint to multiplication by X_m.

*Lean 4 Proof Strategy:*
Define the Hermitian monomial pairing by finite support sums with conjugation in the first argument, positive mode weights, and linearity in the second. Prove the weight/factorial recurrence and the creator/derivative pairing identity on monomials, then extend through the finite sums. Hilbert adjoints are applied only after restricting to an appropriate finite carrier.

This matches the Haldane Gram matrix. In this convention D_m itself is not adjoint to X_m; the dagger notation must refer to the selected form and current normalization. One cannot declare both adjoint conventions on the same carrier without changing the form.

All pairings are finite sums over support. Their restrictions to finite weight slices are ordinary finite inner products. This avoids normalized monomials X^r/√w(r) and their square-root bookkeeping. No Hilbert completion is required for these finite algebraic pairings.

## Normal ordering needs a symbol carrier

Mechanical reordering while ignoring contractions is not a well-defined linear operation on the already represented operator algebra. The equal operators $aa^\dagger$ and $a^\dagger a+I$ would be sent to different results by that rule.

**Definition 2:** Use a symbol space with separate creator and annihilator labels, for example a commutative polynomial space on `Mode ⊕ Mode`, to describe normal-ordered expressions. Define a linear evaluation map sending a monomial `(r,s)` to a fixed ordered product $(a^\dagger)^r a^s$. This evaluation is not an algebra homomorphism from the commutative symbol ring into the noncommutative operator algebra.

*Lean 4 Proof Strategy:*
Define `NormalSymbol := MvPolynomial (Mode ⊕ Mode) ℂ`. Specify evaluation on each monomial as a fixed ordered creator product followed by a fixed ordered annihilator product, then extend linearly using the monomial basis. This is not the universal algebra-hom evaluation into noncommuting images; `eval (P * Q)` need not equal `eval P * eval Q`.

**Theorem 2:** For Wick's theorem on raw words, start with a free associative word algebra and define a rewrite/expansion into normal-ordered symbols, including contractions. Prove termination by word length/inversion count and prove evaluation preservation.

*Lean 4 Proof Strategy:*
Use the checked `FreeAlgebra ℂ (Mode ⊕ Mode)` for raw words. Define separate fermionic and bosonic contractions, with a fixed word order and well-founded measure (word length, then inversion count). Prove evaluation preservation before deriving Wick expansions.

**Theorem 3:** Use integer combinatorial contraction coefficients and cast them into ℂ afterward. Prove the Hermite recurrence for `(D+X)^n 1` directly; a generating-function exponential is unnecessary for this finite polynomial theorem.

*Lean 4 Proof Strategy:*
Define polynomials `H_n(X) = (D + X)^n 1` inductively: `H_0 = 1`, `H_{n+1} = (D + X) H_n = X H_n + D H_n`. Prove the recurrence relation `H_{n+1} = X H_n + n H_{n-1}` by induction on `n`. The induction step relies on the derivation rule `D(X H_n) = H_n + X D H_n`. Keep coefficients in `ℤ` during the induction, then `algebraMap ℤ ℂ` to avoid characteristic zero issues or floating-point artifacts.


## Sea-Wick words and the raw interaction

Use the sea quasiparticle convention of Chapter 17: qₖ=cₖ for empty k>0 and qₖ=cₖ† for occupied k≤0. Normal ordering is a linear operation on raw words: stably put q† before q, with the fermionic permutation sign, omitting contractions inside the colon. Word evaluation and its CAR expansion are separate maps. In particular normal ordering is not an operation on arbitrary evaluated endomorphisms independent of syntax.

Prove $:c_a^\dagger c_b^{\phantom{\dagger}}:=c_a^\dagger c_b^{\phantom{\dagger}}-\delta_{ab}s_aI$, then the quartic identity of Lemma 17.4a, including coincident indices. Its summation produces the exact one-body correction Q_M,ν. Bilinear vacuum subtraction alone is insufficient for quartic words. This supplies explicit syntax and reduction obligations rather than an unspecified quartic colon.
