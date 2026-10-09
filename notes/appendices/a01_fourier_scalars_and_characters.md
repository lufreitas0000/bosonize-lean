# Appendix A01 proposal: Fourier scalars, characters, and normalization

## Scope and decision

Adopt the chapter 3 suggestion's separation of finite character algebra from Hilbert-space normalization. Square roots are not needed for orthogonality or inversion. A positive square root of the one integer L is needed for a unitary transform with the same counting inner product on both spaces. This is a small scalar obligation to isolate, not a reason to change physical CAR normalization.

The proposed `[CommRing R]` layer with only `IsPrimitiveRoot ζ L` is too general. In R = Z/15, L = 2, ζ = 4 has exact order two and L is a unit, but 1 + ζ = 5 ≠ 0. Thus even invertibility of L does not repair character orthogonality over every commutative ring. A saved Lean probe verifies this counterexample. Mathlib's `IsPrimitiveRoot.geom_sum_eq_zero` has an `IsDomain` assumption.

## Suggested contracts

Use L > 0 (or `[NeZero L]`) throughout. For a practical generic layer, use a field K, a primitive root ζ, and `(L : K) ≠ 0` when forming the inverse. If retaining a domain ring layer, prove the two compositions equal scalar multiplication by L and postpone invertibility until L is a unit. For the maximal ring generalization, use a unit-valued character and explicitly require principal-root/orthogonality conditions. Do not claim that exact order implies those conditions in a ring with zero divisors.

Negative powers require a division structure or a unit-valued root. `ζ ^ (n : ℤ)` is not an operation available on an arbitrary `CommRing`. Over a ring, lift ζ to Rˣ using its finite positive order and take integer powers there; alternatively use nonnegative residue exponents. A field layer is simpler for this project's immediate needs.

**Definition:** Define χ(k,x) = ζ^(k*x), with the spatial and momentum indices first regarded as residues. If defining it via integer representatives, prove representative independence before any addition lemma:

1. ζ^L = 1 and ζ ≠ 0 (field) / ζ is a unit (ring).
2. χ(k,x+tL) = χ(k,x), and χ(k+tL,x) = χ(k,x).
3. χ(k,x+y) = χ(k,x)χ(k,y).
4. χ(k+p,x) = χ(k,x)χ(p,x), using transported band addition.
5. χ(-k,x) = χ(k,x)⁻¹.
6. In ℂ, conjugate(χ(k,x)) = χ(-k,x), using unit modulus.

*Lean 4 Proof Strategy:*
- **Auxiliary Lemmas:** `zeta_pow_L`, `chi_well_defined`, `chi_add`, `chi_neg`, `chi_conj`.
- **Strategy:** Formalize `χ` as a map `ZMod L → ZMod L → K`. If defined using integers `ℤ`, prove well-definedness (representative independence) by showing `ζ^(k * (x + t * L)) = ζ^(k * x) * (ζ^L)^(k * t) = ζ^(k * x) * 1 = ζ^(k * x)` (using `IsPrimitiveRoot`). Properties 3-5 follow algebraically from ring exponentiation rules (`pow_add`, etc.). For property 6, over `ℂ`, use `starRingEnd ℂ` and the fact that primitive roots of unity have modulus 1, so their complex conjugate equals their inverse.

Prefer an `AddChar` or equivalent bundled character internally. Expose evaluation formulas on `Ch01.Band L` for downstream use; use `Ch01.band_projection_bijective` to transport finite sums. Do not install a new competing group instance on the already frozen band type merely to write the pairing.

## Unscaled and normalized transforms

**Definition:** Define the positive-sign synthesis map T and negative-sign analysis map S:

\[
 Sf(k)=\sum_x f(x)\chi(-k,x),\qquad
 Tg(x)=\sum_k g(k)\chi(k,x).
\]

*Lean 4 Proof Strategy:*
- **Strategy:** Define `S` and `T` as `LinearMap K (Band L → K) (Band L → K)`. Use `Finset.sum` over `Finset.univ` since `Band L` is a `Fintype`. The formulas can be written explicitly using scalar multiplication and evaluation of the character `χ`.

**Lemma:** For a nontrivial exponent m, prove the geometric-sum identity `(ζ^m−1) Σ_x ζ^(mx) = (ζ^m)^L−1 = 0`; the domain/field assumption cancels the nonzero factor. This covers non-coprime m too. Merely applying a primitive-root theorem to ζ^m with order L would fail when gcd(m,L)>1. Establish the diagonal branch by summing ones.

*Lean 4 Proof Strategy:*
- **Auxiliary Lemmas:** `geom_sum_mul_sub_one`.
- **Strategy:** Apply Mathlib's `geom_sum_mul_sub_one`: `(∑ i ∈ range L, (ζ^m)^i) * (ζ^m - 1) = (ζ^m)^L - 1 = (ζ^L)^m - 1 = 1^m - 1 = 0`. Since `K` is a domain (or field), this implies either `ζ^m - 1 = 0` (meaning `L ∣ m` and the sum is just `∑_x 1 = L`) or `∑_x ζ^(mx) = 0`. This establishes character orthogonality.

**Theorem:** Once both orthogonality identities are proved, finite-sum rearrangement gives

\[
 TS=L I,\qquad ST=L I.
\]

*Lean 4 Proof Strategy:*
- **Auxiliary Lemmas:** `Finset.sum_comm`, `Finset.sum_mul`.
- **Strategy:** Expand `T (S f) x`. Using `Finset.sum_comm`, swap the sums over `k` and `y`. Rearrange to `∑ y, f(y) * (∑ k, χ(k, x - y))`. Apply the previous geometric sum lemma to the inner sum: it is `L` if `x = y` (diagonal branch) and `0` otherwise. This simplifies to `L * f(x)`. This gives `T ∘ S = L • id`. By symmetry, `S ∘ T = L • id`.

T is an unscaled synthesis map, not the inverse of S until the factor L is removed. When L is invertible, S is a linear equivalence with inverse L⁻¹T. This asymmetric normalization is entirely valid for algebraic inversion. The suggestion's blanket claim that it breaks the star involution is too strong: it simply does not give a unitary change of CAR generators with both spaces using the original counting inner product.

**Definition and Lemma:** For the physical layer, define a real scalar a = 1/√L, view it in ℂ, and prove once:

\[
 a>0,\quad \bar a=a,\quad L a^2=1.
\]

*Lean 4 Proof Strategy:*
- **Auxiliary Lemmas:** `Real.sqrt_pos`.
- **Strategy:** Define `a : ℝ := 1 / Real.sqrt (L : ℝ)`. Use `Real.sqrt_pos` and the hypothesis `L > 0` to prove `a > 0`. Map `a` into `ℂ` using coercion. Complex conjugation is the identity on coerced reals (`RCLike.conj_coe`), giving `conj a = a`. The relation `L * a^2 = 1` follows from `Real.mul_inv_cancel` and `Real.sq_sqrt`.

**Theorem:** Then U = aS and U⁻¹ = aT. The conjugate-transpose kernel proves U† = aT, and the two unscaled composition identities give unitarity.

*Lean 4 Proof Strategy:*
- **Auxiliary Lemmas:** `LinearMap.adjoint`, inner product spaces properties.
- **Strategy:** Define `U = a • S` and `U_inv = a • T`. Their product yields `a^2 * (T ∘ S) = a^2 * L * I = I`. To compute `U†`, first compute `S†` on `EuclideanSpace ℂ (Band L)`. Expand `⟨S f, g⟩`, swap sums, and use `conj (χ(-k, y)) = χ(k, y)` to identify it as `⟨f, T g⟩`. Hence `S† = T`. Thus `U† = conj(a) * S† = a * T = U⁻¹`. Unitarity is captured by constructing a `LinearIsometryEquiv`.

Use a `LinearIsometryEquiv` on `EuclideanSpace ℂ _` when Hilbert APIs are needed; a `LinearEquiv` alone asserts invertibility, not preservation of the inner product. Alternatively prove matrix conjugate-transpose identities first and transport to Euclidean spaces.

For any coefficient b used in the physical annihilator sum, the CAR coefficient is `|b|² L`. Canonical CAR therefore requires `|b|² L = 1`. Avoiding √L by putting 1/L into both physical transforms would give coefficient 1/L, not 1.

A field need not be quadratically closed to contain a square root of this one scalar L. When necessary, extend by a chosen root of t²−L or parameterize a normalization satisfying the scalar law. ℂ already supplies the positive real root; constructing an abstract extension is probably unnecessary overhead here.

## Reuse before reimplementation

Installed Mathlib already defines `ZMod.dft` over complex vector spaces, with the negative-sign unscaled forward transform and the positive-sign inverse scaled by 1/L. Its API includes `dft_apply`, `invDFT_apply`, and `dft_dft` (the latter includes index reflection).

For the immediate complex implementation, the lowest-maintenance approach is to transport this DFT to the band, then add the scalar a to obtain U. Prove a bridge between `ZMod.stdAddChar` and the notes' chosen exponential root. If arbitrary primitive roots or coefficient fields are a real downstream requirement, keep the generic layer as a separate small construction. Arbitrary primitive roots correspond to relabelings; they do not automatically give the same trigonometric formula with k unchanged.

This is a three-layer dependency order within the two-tier idea: characters → unscaled linear equivalence → normalized complex isometry. It avoids duplicating a large inverse proof while exposing the algebraic facts the project needs.

## Dispersion and corner cases

**Lemma:** The primary exact Laplacian eigenvalue is

\[
 (\zeta^k-1)(1-\zeta^{-k})=\zeta^k+\zeta^{-k}-2.
\]

*Lean 4 Proof Strategy:*
- **Strategy:** Over a `CommRing K`, use algebraic expansion. Distribute the terms: `ζ^k * 1 - ζ^k * ζ^{-k} - 1 + ζ^{-k}`. Because `ζ^k * ζ^{-k} = ζ^0 = 1`, the expression simplifies directly to `ζ^k + ζ^{-k} - 2` via `mul_sub`, `sub_mul`, and integer power addition.

Reject the suggestion's `−(ζ^(k/2)−ζ^(−k/2))²`: fractional exponents are unspecified, and its sign is wrong. If w² = ζ^k, the correct expression is `(w−w⁻¹)²`, without the leading minus. Prefer the primary expression; no new root is needed.

**Lemma:** Only after selecting ζ = exp(2πi/L) should a separate evaluation lemma identify it with `−4 sin²(πk/L)`. The root-of-unity algebra does not need trigonometric functions.

*Lean 4 Proof Strategy:*
- **Strategy:** Substitute `ζ = Complex.exp (2 * π * I / L)`. The expression `ζ^k + ζ^{-k} - 2` evaluates to `2 * Complex.cos (2 * π * k / L) - 2` via Euler's formula (`Complex.exp_add_exp_neg`). Apply the double angle identity `cos (2 * θ) = 1 - 2 * sin^2(θ)` with `θ = π * k / L`. This algebraically yields `-4 * sin^2(π * k / L)`. Use Mathlib's `Complex.cos_double`.

Handle L = 1 explicitly: all characters are trivial, sums are one-term sums, and the nontrivial-character branch is empty. Handle the even Nyquist mode through the frozen band-negation theorem. Establish finite-sum transport, kernel signs, scalar casts, and matrix index orientation before freezing chapter 3.

## Evidence

Local API checked in `Mathlib/Analysis/Fourier/ZMod.lean` and `Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean`. The official [DFT documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/ZMod.html) and [primitive-root documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.html) confirm these interfaces. Local installed source and compiler probes control version-specific claims.
