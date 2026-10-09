# Chapter 3 Fourier draft — revised construction guide

Revision: 2026-10-09. This is an architectural suggestion, not a compiled Lean module or an approved frozen interface. Read [Chapter 3](../../notes/md/ch03_fourier.md), [A01](../../notes/appendices/a01_fourier_scalars_and_characters.md), and the [proof revision guide](../../note/proof_suggestions_revision_2026-10-09.md). Reuse `Bosonize.Ch01` and `Bosonize.Ch02` from Core.

The two-step construction is appropriate: prove character algebra and unscaled inversion first, then normalize once in the complex Hilbert layer. A field needs the chosen square root of L for unitary normalization; quadratic closure is unnecessary. Algebraic invertibility alone does not imply unitarity for the counting inner products.

## Characters and carrier contracts

Use `[NeZero L]` and a coefficient field K with `(L : K) ≠ 0` and `IsPrimitiveRoot ζ L`. Positivity of L supplies the modular finite-type instance through `NeZero`; nonzero scalar L separately permits inversion. A more general ring version needs explicit cancellation and scalar-invertibility assumptions and should only be added if required downstream.

Keep `Ch01.Lattice L = ZMod L` for positions and `Ch01.Band L` for signed integer momentum labels. Define a bundled additive character on residues and expose its band evaluation. Integer powers of the nonzero root express negative integer labels. Prove representative independence, multiplication under addition, inverse under negation, and the complex conjugation identity. Transport sums through `Ch01.band_projection_bijective`; do not install a competing band group instance.

Proposed helper responsibilities:

- `character_representative_independent`: shifts by multiples of L leave evaluations unchanged.
- `character_band_neg`: transported negation has the same character as integer negation, including Nyquist.
- `sum_band_eq_sum_lattice`: transport the finite sum through the frozen equivalence.
- `character_nontrivial`: nonzero residue frequency gives a character different from 1.
- `character_orthogonality`: diagonal sum L, off-diagonal sum zero.

These are proposed project helpers, not existing Mathlib names. The installed `AddChar.sum_eq_zero_of_ne_one` is available for the nontrivial-character sum. Its hypotheses must be supplied. `IsPrimitiveRoot.geom_sum_eq_zero` concerns a root at its actual order: ζ^m can have smaller order than L when gcd(m,L)>1. A direct geometric telescoping proof with cancellation is an alternative.

## Unscaled inversion

Define maps with their actual source and target:

```text
S : (Ch01.Lattice L → K) →ₗ[K] (Ch01.Band L → K)
T : (Ch01.Band L → K) →ₗ[K] (Ch01.Lattice L → K)
S f k = ∑ x, f x * χ(-k,x)
T g x = ∑ k, g k * χ(k,x)
```

Expand finite sums, exchange their order, and apply both orthogonality identities to prove `T.comp S = (L : K) • id` and `S.comp T = (L : K) • id`. Bundle S with inverse `(L : K)⁻¹ • T` as a linear equivalence. T alone is not the inverse.

For the canonical complex root, first evaluate reuse of the installed `ZMod.dft` and its `.symm` inverse (whose evaluation lemma is `ZMod.invDFT_apply`), then transport their kernels to the band. Their forward transform is unscaled and inverse includes 1/L. Prove the character/sign bridge explicitly. This can avoid duplicating the inversion proof. If arbitrary primitive roots are needed, retain a separate generic construction; they do not all give the same trigonometric formula with unchanged frequency labels.

## Complex normalization and adjoints

Define `a : ℝ := (Real.sqrt (L : ℝ))⁻¹`, prove `a>0` and `L*a^2=1`, and cast a to ℂ. This scalar package is the only square-root layer. The canonical complex primitive-root theorem checked in the installed library is `Complex.isPrimitiveRoot_exp L hL`, where `hL : L ≠ 0`.

Use `EuclideanSpace ℂ (Ch01.Lattice L)` and `EuclideanSpace ℂ (Ch01.Band L)` for counting inner products. Ordinary function spaces have a different default norm. Transport the function maps first: `WithLp.linearEquiv 2 ℂ (I → ℂ)` goes from `EuclideanSpace ℂ I` to functions, so set `S₂=eₖ.symm ∘ S ∘ eₓ` and `T₂=eₓ.symm ∘ T ∘ eₖ`. Transport the frozen Chapter 2 shifts by the same conjugation. Prove the kernel adjoint identity for S₂/T₂, then set `U=a • S₂` and `U⁻¹=a • T₂`. In Phase A define U as a linear map and stub its isometry statement; bundle the final `LinearIsometryEquiv` once its proof fields can be supplied without placeholders. Canonical position CAR requires `|a|²*L=1`; 1/L in both physical transforms would produce the wrong CAR coefficient.

## Difference diagonalization

Apply the frozen shifts on `ZMod L` to the character and derive the eigenvalues by character laws:

```text
forward difference: ζ^k − 1
backward difference: 1 − ζ^(-k)
laplacian: (ζ^k − 1)*(1 − ζ^(-k)) = ζ^k + ζ^(-k) − 2
```

Use integer band representatives for k. The retired fractional-power square expression was ambiguous and had the wrong sign. No additional root is needed. Only after selecting ζ=exp(2πi/L) derive the separate evaluation `−4*sin²(πk/L)`.

## Phase A acceptance

Before freezing, elaborate all definitions without placeholders, check the exact signatures/imports/local instances, and record source/target types in the companion notebook. Include L=1 and the even Nyquist case in the contracts, although the half-filled physical chapters later assume L=2h with h>0. Lemma stubs and all helper additions require the ordinary Phase A review; this guide does not authorize Lean edits.
