# Appendix A02 proposal: CAR carriers, adjoints, and normal ordering

## One carrier convention

A bare function space `X → ℂ` is algebraically convenient but does not automatically carry the sum-of-squares Euclidean norm. Its usual product norm and the Euclidean norm should not be conflated by installing incompatible instances.

Choose either `EuclideanSpace ℂ (Finset ι)` for the finite Hilbert carrier, with a transport to the algebraic function basis, or matrices indexed by `Finset ι` for the operator proofs, with a later Euclidean interpretation. Prove the transport once. The installed `PiL2` module defines `EuclideanSpace` and its finite-sum inner product. Matrix conjugate transpose provides a particularly direct finite adjoint API.

**Definition 1:** Creation operators should be constructed from the occupation basis, using `Module.Basis.constr`, or from their matrix coefficients. Record evaluation laws and a basis-extensionality lemma before proving CAR. Do not define a general Hilbert adjoint on unbundled arbitrary linear maps in an infinite-dimensional carrier.

*Lean 4 Proof Strategy:*
Use `Matrix.toLin` or `Module.Basis.constr` over `Finset ι` to bundle operators with their matrix representations. Define the adjoint via `Matrix.conjTranspose`. The occupation basis can be encoded as functions `ι → ZMod 2` or subsets `Finset ι` for fermions. Provide a `@[simp]` lemma for evaluating the creation operator on a basis vector.

## Required CAR lemma chain

**Lemma 1:** Inserting/erasing mode j changes the preceding-mode count only when j < i.

*Lean 4 Proof Strategy:*
Define the count of preceding modes for a state `s : Finset ι` up to mode `i` as `(s.filter (· < i)).card`. Prove that `insert j s` increases this count by 1 if and only if `j < i` and `j ∉ s`. Use `Finset.card_insert_of_not_mem` and `Finset.filter_insert`, using case splitting on `j < i`.

**Lemma 2:** State the erasure count in an addition form when using natural numbers, avoiding truncated subtraction until its nonnegativity is proved.

*Lean 4 Proof Strategy:*
Instead of writing `new_count = old_count - 1`, state it as `old_count = new_count + 1` whenever `j ∈ s`. This avoids `Nat` subtraction underflow issues. Use `Nat.add_right_cancel` and `Nat.add_assoc` to algebraically manipulate the counts without ever needing `Nat.sub`.

**Lemma 3:** Signs have square one; the insert/erase operations at distinct modes commute as set operations but flip the relevant combined sign.

*Lean 4 Proof Strategy:*
Model the fermionic sign as `(-1) ^ count` inside a `Ring` or `Field`. Prove `(-1)^2 = 1` and `(-1)^(a+b) = (-1)^a * (-1)^b`. For `i ≠ j`, show that inserting/erasing `i` and `j` in either order results in counts that differ by exactly 1, meaning the total sign gets a factor of `(-1)^1 = -1`. Use `Finset.insert_comm` for the underlying set operation.

**Lemma 4:** Prove all three CAR identities, not merely assume a representation structure for the concrete Fock operators. The abstract CAR definition must bundle the adjoint compatibility field $c_i^\dagger = \mathrm{adjoint}(c_i)$ on a finite-dimensional Euclidean carrier; purely algebraic CAR pairs can be conjugated by nonunitary maps and lose adjointness.

*Lean 4 Proof Strategy:*
The CAR identities are `{a_i, a_j} = 0`, `{a_i^\dagger, a_j^\dagger} = 0`, and `{a_i, a_j^\dagger} = \delta_{ij}`. Apply both sides to an arbitrary basis element `|s\rangle`. By Lemma 3, `a_i a_j |s\rangle = - a_j a_i |s\rangle` for `i ≠ j`. For `i = j`, `{a_i, a_i^\dagger} = a_i a_i^\dagger + a_i^\dagger a_i` evaluates to `1 |s\rangle` because any state is either occupied or empty at `i`. Conclude by `Module.Basis.ext`.

**Lemma 5:** Prove adjointness on basis pairs, lift by finite sums, and instantiate the abstract CAR representation.

*Lean 4 Proof Strategy:*
Prove `\langle s | a_i^\dagger | s' \rangle = \langle a_i s | s' \rangle` for basis vectors `s, s'`. Use `EuclideanSpace.inner` from `PiL2` for the inner product. Then, use the linearity of the inner product and `LinearMap.ext` to lift this adjointness property to arbitrary states, represented as finite linear combinations of basis vectors. Combine this with Lemma 4 to build an explicit instance of `CAR (FockSpace ι) ι`.

**Lemma 6:** Derive number operators as coordinate indicators, pairwise commutativity, and parity Γ² = I and Γ† = Γ.

*Lean 4 Proof Strategy:*
Define `N_i = a_i^\dagger a_i`. Show `N_i |s\rangle = (if i ∈ s then 1 else 0) |s\rangle`. Commutativity `[N_i, N_j] = 0` follows because they are diagonal operators. Define parity `Γ = \prod_i (I - 2 N_i)`. Show `Γ^2 = I` since `(1 - 2x)^2 = 1` for `x ∈ {0, 1}`. Show `Γ^\dagger = Γ` since it's a real diagonal matrix.

**Lemma 7:** Derive bilinear commutators from CAR. Reuse them in chapter 9 rather than giving duplicate implementations.

*Lean 4 Proof Strategy:*
Prove the CAR bilinear identity `[c_p† c_k, c_q† c_l] = δ_kq c_p† c_l − δ_pl c_q† c_k` by explicit distributivity and CAR. Reuse it to show dΓ preserves Lie brackets. A symmetric collection of swaps is not a terminating normal-order procedure.

> [!WARNING]
> **Proof-review correction (2026-10-09):** The previous four-factor formula, preserved in the checkpoint history, was withdrawn as a generic identity. Setting A=C=1 gives 3[B,D] on its right, instead of [B,D]. Prove and reuse the CAR bilinear identity `[c_p† c_k, c_q† c_l] = δ_kq c_p† c_l − δ_pl c_q† c_k` directly. An automatic swap rule also needs a fixed ordering and termination argument; symmetric CAR rewrites are not an unconditional `simp` procedure.

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
\[
 w(r)=\prod_m m^{r_m}r_m!.
\]
Then `m D_m` is adjoint to multiplication by X_m.

*Lean 4 Proof Strategy:*
Define the Hermitian monomial pairing by finite support sums with conjugation in the first argument, positive mode weights, and linearity in the second. Prove the weight/factorial recurrence and the creator/derivative pairing identity on monomials, then extend through the finite sums. Hilbert adjoints are applied only after restricting to an appropriate finite carrier.

This matches the Haldane Gram matrix. In this convention D_m itself is not adjoint to X_m; the dagger notation must refer to the selected form and current normalization. One cannot declare both adjoint conventions on the same carrier without changing the form.

All pairings are finite sums over support. Their restrictions to finite weight slices are ordinary finite inner products. This avoids normalized monomials X^r/√w(r) and their square-root bookkeeping. No Hilbert completion is required for these finite algebraic pairings.

## Normal ordering needs a symbol carrier

Mechanical reordering while ignoring contractions is not a well-defined linear operation on the already represented operator algebra. The equal operators `a a†` and `a† a + I` would be sent to different results by that rule.

**Definition 2:** Use a symbol space with separate creator and annihilator labels, for example a commutative polynomial space on `Mode ⊕ Mode`, to describe normal-ordered expressions. Define a linear evaluation map sending a monomial `(r,s)` to a fixed ordered product `(a†)^r a^s`. This evaluation is not an algebra homomorphism from the commutative symbol ring into the noncommutative operator algebra.

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

Prove `:c_a†c_b:=c_a†c_b−δ_ab s_a I`, then the quartic identity of Lemma 17.4a, including coincident indices. Its summation produces the exact one-body correction Q_M,ν. Bilinear vacuum subtraction alone is insufficient for quartic words. This supplies explicit syntax and reduction obligations rather than an unspecified quartic colon.
