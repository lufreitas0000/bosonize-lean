# Appendix A01 proposal: Fourier scalars, characters, and normalization

## Scope and decision

Adopt the chapter 3 suggestion's separation of finite character algebra from Hilbert-space normalization. Square roots are not needed for orthogonality or inversion. A positive square root of the one integer L is needed for a unitary transform with the same counting inner product on both spaces. This is a small scalar obligation to isolate, not a reason to change physical CAR normalization.

The proposed `[CommRing R]` layer with only `IsPrimitiveRoot ζ L` is too general. In R = Z/15, L = 2, ζ = 4 has exact order two and L is a unit, but 1 + ζ = 5 ≠ 0. Thus even invertibility of L does not repair character orthogonality over every commutative ring. A saved Lean probe verifies this counterexample. Mathlib's `IsPrimitiveRoot.geom_sum_eq_zero` has an `IsDomain` assumption.

## Suggested contracts

Use L > 0 (or `[NeZero L]`) throughout. For a practical generic layer, use a field K, a primitive root ζ, and `(L : K) ≠ 0` when forming the inverse. If retaining a domain ring layer, prove the two compositions equal scalar multiplication by L and postpone invertibility until L is a unit. For the maximal ring generalization, use a unit-valued character and explicitly require principal-root/orthogonality conditions. Do not claim that exact order implies those conditions in a ring with zero divisors.

Negative powers require a division structure or a unit-valued root. `ζ ^ (n : ℤ)` is not an operation available on an arbitrary `CommRing`. Over a ring, lift ζ to Rˣ using its finite positive order and take integer powers there; alternatively use nonnegative residue exponents. A field layer is simpler for this project's immediate needs.

Define χ(k,x) = ζ^(k*x), with the spatial and momentum indices first regarded as residues. If defining it via integer representatives, prove representative independence before any addition lemma:

1. ζ^L = 1 and ζ ≠ 0 (field) / ζ is a unit (ring).
2. χ(k,x+tL) = χ(k,x), and χ(k+tL,x) = χ(k,x).
3. χ(k,x+y) = χ(k,x)χ(k,y).
4. χ(k+p,x) = χ(k,x)χ(p,x), using transported band addition.
5. χ(-k,x) = χ(k,x)⁻¹.
6. In ℂ, conjugate(χ(k,x)) = χ(-k,x), using unit modulus.

Prefer an `AddChar` or equivalent bundled character internally. Expose evaluation formulas on `Ch01.Band L` for downstream use; use `Ch01.band_projection_bijective` to transport finite sums. Do not install a new competing group instance on the already frozen band type merely to write the pairing.

## Unscaled and normalized transforms

Define the positive-sign synthesis map T and negative-sign analysis map S:

\[
 Sf(k)=\sum_x f(x)\chi(-k,x),\qquad
 Tg(x)=\sum_k g(k)\chi(k,x).
\]

For a nontrivial exponent m, prove the geometric-sum identity `(ζ^m−1) Σ_x ζ^(mx) = (ζ^m)^L−1 = 0`; the domain/field assumption cancels the nonzero factor. This covers non-coprime m too. Merely applying a primitive-root theorem to ζ^m with order L would fail when gcd(m,L)>1. Establish the diagonal branch by summing ones.

Once both orthogonality identities are proved, finite-sum rearrangement gives

\[
 TS=L I,\qquad ST=L I.
\]

T is an unscaled synthesis map, not the inverse of S until the factor L is removed. When L is invertible, S is a linear equivalence with inverse L⁻¹T. This asymmetric normalization is entirely valid for algebraic inversion. The suggestion's blanket claim that it breaks the star involution is too strong: it simply does not give a unitary change of CAR generators with both spaces using the original counting inner product.

For the physical layer, define a real scalar a = 1/√L, view it in ℂ, and prove once:

\[
 a>0,\quad \bar a=a,\quad L a^2=1.
\]

Then U = aS and U⁻¹ = aT. The conjugate-transpose kernel proves U† = aT, and the two unscaled composition identities give unitarity. Use a `LinearIsometryEquiv` on `EuclideanSpace ℂ _` when Hilbert APIs are needed; a `LinearEquiv` alone asserts invertibility, not preservation of the inner product. Alternatively prove matrix conjugate-transpose identities first and transport to Euclidean spaces.

For any coefficient b used in the physical annihilator sum, the CAR coefficient is `|b|² L`. Canonical CAR therefore requires `|b|² L = 1`. Avoiding √L by putting 1/L into both physical transforms would give coefficient 1/L, not 1.

A field need not be quadratically closed to contain a square root of this one scalar L. When necessary, extend by a chosen root of t²−L or parameterize a normalization satisfying the scalar law. ℂ already supplies the positive real root; constructing an abstract extension is probably unnecessary overhead here.

## Reuse before reimplementation

Installed Mathlib already defines `ZMod.dft` over complex vector spaces, with the negative-sign unscaled forward transform and the positive-sign inverse scaled by 1/L. Its API includes `dft_apply`, `invDFT_apply`, and `dft_dft` (the latter includes index reflection).

For the immediate complex implementation, the lowest-maintenance approach is to transport this DFT to the band, then add the scalar a to obtain U. Prove a bridge between `ZMod.stdAddChar` and the notes' chosen exponential root. If arbitrary primitive roots or coefficient fields are a real downstream requirement, keep the generic layer as a separate small construction. Arbitrary primitive roots correspond to relabelings; they do not automatically give the same trigonometric formula with k unchanged.

This is a three-layer dependency order within the two-tier idea: characters → unscaled linear equivalence → normalized complex isometry. It avoids duplicating a large inverse proof while exposing the algebraic facts the project needs.

## Dispersion and corner cases

The primary exact Laplacian eigenvalue is

\[
 (\zeta^k-1)(1-\zeta^{-k})=\zeta^k+\zeta^{-k}-2.
\]

Reject the suggestion's `−(ζ^(k/2)−ζ^(−k/2))²`: fractional exponents are unspecified, and its sign is wrong. If w² = ζ^k, the correct expression is `(w−w⁻¹)²`, without the leading minus. Prefer the primary expression; no new root is needed.

Only after selecting ζ = exp(2πi/L) should a separate evaluation lemma identify it with `−4 sin²(πk/L)`. The root-of-unity algebra does not need trigonometric functions.

Handle L = 1 explicitly: all characters are trivial, sums are one-term sums, and the nontrivial-character branch is empty. Handle the even Nyquist mode through the frozen band-negation theorem. Establish finite-sum transport, kernel signs, scalar casts, and matrix index orientation before freezing chapter 3.

## Evidence

Local API checked in `Mathlib/Analysis/Fourier/ZMod.lean` and `Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean`. The official [DFT documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/ZMod.html) and [primitive-root documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.html) confirm these interfaces. Local installed source and compiler probes control version-specific claims.
