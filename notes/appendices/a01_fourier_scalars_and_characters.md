## Scope and decision

Adopt the chapter 3 suggestion's separation of finite character algebra from Hilbert-space normalization. Square roots are not needed for orthogonality or inversion. A positive square root of the one integer L is needed for a unitary transform with the same counting inner product on both spaces. This is a small scalar obligation to isolate, not a reason to change physical CAR normalization.

The proposed `[CommRing R]` layer with only `IsPrimitiveRoot ζ L` is too general. In $R = \mathbb{Z}/15\mathbb{Z}$, with $L = 2$, $\zeta = 4$ has exact multiplicative order two ($4^2 = 16 \equiv 1 \pmod{15}$) and $L = 2$ is a unit ($2 \times 8 = 16 \equiv 1 \pmod{15}$), but $1 + \zeta = 5 \not\equiv 0 \pmod{15}$. Thus even invertibility of $L$ does not repair character orthogonality over every commutative ring with zero divisors. A saved Lean probe verifies this counterexample. Mathlib's `IsPrimitiveRoot.geom_sum_eq_zero` has an `IsDomain` assumption.

## Suggested contracts & The Three-Tier Architecture

Use $L > 0$ (or `[NeZero L]`) throughout. For a practical generic layer, use a field $K$, a primitive root $\zeta$, and $(L : K) \neq 0$ when forming the inverse.

### The Formal Three-Tiered Character Hierarchy
In Lean 4 (`Bosonize.A01`), to avoid forcing an artificial group structure onto the centered momentum band $\Lambda^*$, characters are structured across three levels:

1. **Tier 1 (Integer Pairing on $\mathbb{Z} \times \mathbb{Z}$):**
   $$
   \chi_{\mathbb{Z}}(\zeta, k, x) := \zeta^{kx} \quad (k, x \in \mathbb{Z}) \tag{A01.1}
   $$
   This is well-defined for all signed integers since $\zeta \ne 0$ in $K$, so negative exponents use field inversion $\zeta^{-1}$.

2. **Tier 2 (Residue Character on $\mathbb{Z}/L\mathbb{Z} \times \mathbb{Z}/L\mathbb{Z}$):**
   $$
   \chi_{\mathrm{res}}(L, \zeta, k, x) := \chi_{\mathbb{Z}}(\zeta, k.\mathrm{val}, x.\mathrm{val}) \tag{A01.2}
   $$
   where $k.\mathrm{val}, x.\mathrm{val} \in \{0, \dots, L-1\}$ are the canonical unsigned residues.

3. **Tier 3 (Band Character on $\Lambda^* \times \Lambda$):**
   $$
   \chi_{\mathrm{band}}(L, \zeta, k, x) := \chi_{\mathbb{Z}}(\zeta, k.\mathrm{val}, x.\mathrm{val}) = \chi_{\mathrm{res}}(L, \zeta, \pi(k), x) \tag{A01.3}
   $$
   where $k \in \Lambda^*$ is the signed band integer representative and $x \in \mathbb{Z}/L\mathbb{Z}$.

**Representative Independence Lemma (`character_representative_independent`):**
For any $s, t \in \mathbb{Z}$:
$$
\chi_{\mathbb{Z}}(\zeta, k + sL, x + tL) = \zeta^{(k+sL)(x+tL)} = \zeta^{kx} (\zeta^L)^{kt + sx + stL} = \zeta^{kx} \cdot 1 = \zeta^{kx} = \chi_{\mathbb{Z}}(\zeta, k, x) \tag{A01.4}
$$
This fundamental lemma guarantees that all evaluations agree across integers, standard residues, and transported band elements.

**Character Homomorphism Laws:**

1. $\zeta^L = 1$ and $\zeta \neq 0$ (field $K$).
2. Representative independence: $\chi(k, x + tL) = \chi(k, x)$ and $\chi(k + tL, x) = \chi(k, x)$ for all $t \in \mathbb{Z}$.
3. Spatial homomorphism: $\chi(k, x + y) = \chi(k, x)\chi(k, y)$.
4. Transported band addition: $\chi(k \oplus p, x) = \chi(k, x)\chi(p, x)$. (Since $k \oplus p = k + p - wL$ with $w \in \{-1,0,1\}$, representative independence gives $\chi(k \oplus p, x) = \chi(k + p, x) = \chi(k, x)\chi(p, x)$).
5. Inversion / negation: $\chi(-k, x) = \chi(k, x)^{-1} = \chi(\ominus k, x)$, where $-k \in \mathbb{Z}$ is ordinary integer negation and $\ominus k$ is transported band negation.
6. Band subtraction: $\chi(k \ominus k', x) = \chi(k - k', x) = \chi(k, x)\chi(k', x)^{-1}$, even when integer $k - k'$ leaves the centered band.
7. In $\mathbb{C}$, $\overline{\chi(k,x)} = \chi(-k,x)$, since primitive roots of unity satisfy $|\zeta| = 1$ and thus $\zeta^* = \zeta^{-1}$.

## Unscaled and normalized transforms

**Definition:** Define the positive-sign synthesis map T and negative-sign analysis map S:

$$
 Sf(k)=\sum_x f(x)\chi(-k,x),\qquad
 Tg(x)=\sum_k g(k)\chi(k,x).
$$

*Lean 4 Proof Strategy:*

- **Strategy:** Define `S : (Ch01.Lattice L → K) →ₗ[K] (Ch01.Band L → K)` and `T : (Ch01.Band L → K) →ₗ[K] (Ch01.Lattice L → K)` with finite sums. The maps have different source/target carriers; use the frozen bijection only to transport sums, not to silently identify their types.

**Lemma:** For a nontrivial exponent m, prove the geometric-sum identity $(\zeta^m-1)\sum_x\zeta^{mx}=(\zeta^m)^L-1=0$; the domain/field assumption cancels the nonzero factor. This covers non-coprime m too. Merely applying a primitive-root theorem to ζ^m with order L would fail when gcd(m,L)>1. Establish the diagonal branch by summing ones.

*Lean 4 Proof Strategy:*

- **Checked API:** `AddChar.sum_eq_zero_of_ne_one`; prove nontriviality for each nonzero frequency difference before applying it.
- **Strategy:** Either use the bundled-character sum theorem, or prove the finite geometric telescoping identity directly and cancel ζ^m−1. Do not assume ζ^m has order L for non-coprime m. Any alternative library geometric-sum name must be checked before use.

**Theorem:** Once both orthogonality identities are proved, finite-sum rearrangement gives

$$
 TS=L I,\qquad ST=L I.
$$

*Lean 4 Proof Strategy:*

- **Auxiliary Lemmas:** `Finset.sum_comm`, `Finset.sum_mul`.
- **Strategy:** Expand `T (S f) x`. Using `Finset.sum_comm`, swap the sums over `k` and `y`. Rearrange to `∑ y, f(y) * (∑ k, χ(k, x - y))`. Apply the previous geometric sum lemma to the inner sum: it is `L` if `x = y` (diagonal branch) and `0` otherwise. This simplifies to `L * f(x)`. This gives `T ∘ S = L • id`. By symmetry, `S ∘ T = L • id`.

T is an unscaled synthesis map, not the inverse of S until the factor L is removed. When L is invertible, S is a linear equivalence with inverse L⁻¹T. This asymmetric normalization is entirely valid for algebraic inversion. The suggestion's blanket claim that it breaks the star involution is too strong: it simply does not give a unitary change of CAR generators with both spaces using the original counting inner product.

**Definition and Lemma:** For the physical layer, define a real scalar a = 1/√L, view it in ℂ, and prove once:

$$
 a>0,\quad \bar a=a,\quad L a^2=1.
$$

*Lean 4 Proof Strategy:*

- **Auxiliary Lemmas:** `Real.sqrt_pos`.
- **Strategy:** Define `a : ℝ := (Real.sqrt (L : ℝ))⁻¹`. Prove sqrt positivity/nonzero and its squared identity, then the scalar normalization. Cast the finished identities to ℂ and simplify conjugation of real casts with the installed simp lemmas. Avoid guessed names for cast/conjugation/cancellation results.

**Hilbert carrier transport:** For each finite index type I, `WithLp.linearEquiv 2 ℂ (I → ℂ)` maps `EuclideanSpace ℂ I` to ordinary functions. Write these equivalences as eₓ and eₖ. Set S₂ = eₖ⁻¹ ∘ S ∘ eₓ and T₂ = eₓ⁻¹ ∘ T ∘ eₖ. Transport the frozen Chapter 2 operators in the same way. This algebraic transport is not an isometry for the default function norm; the counting inner product is on the Euclidean carrier.

**Theorem:** Then U = aS₂ and U⁻¹ = aT₂. The conjugate-transpose kernel proves U† = aT₂, and the two unscaled composition identities give unitarity.

*Lean 4 Proof Strategy:*

- **Auxiliary Lemmas:** `LinearMap.adjoint`, inner product spaces properties.
- **Strategy:** Define `U = a • S₂` and `U_inv = a • T₂`. Their product yields `a^2 • (T₂ ∘ S₂) = (a^2 * L) • I = I`. To compute $U^\dagger$, first compute $S_2^\dagger$ between `EuclideanSpace ℂ (Ch01.Band L)` and `EuclideanSpace ℂ (Ch01.Lattice L)`. Expand the counting-inner-product finite sum for `⟨S₂ f, g⟩`, swap sums, and use `conj (χ(-k, y)) = χ(k, y)` to identify it as `⟨f, T₂ g⟩`. Hence $S_2^\dagger=T_2$. Thus $U^\dagger=\overline a\,S_2^\dagger=aT_2=U^{-1}$. Unitarity is captured by constructing a `LinearIsometryEquiv`.

Use a `LinearIsometryEquiv` on `EuclideanSpace ℂ _` when Hilbert APIs are needed; a `LinearEquiv` alone asserts invertibility, not preservation of the inner product. Alternatively prove matrix conjugate-transpose identities first and transport to Euclidean spaces.

For any coefficient b used in the physical annihilator sum, the CAR coefficient is $|b|^2 L$. Canonical CAR therefore requires $|b|^2 L=1$. Avoiding √L by putting 1/L into both physical transforms would give coefficient 1/L, not 1.

A field need not be quadratically closed to contain a square root of this one scalar L. When necessary, extend by a chosen root of t²−L or parameterize a normalization satisfying the scalar law. ℂ already supplies the positive real root; constructing an abstract extension is probably unnecessary overhead here.

## Reuse before reimplementation

Installed Mathlib already defines `ZMod.dft` over complex vector spaces, with the negative-sign unscaled forward transform and the positive-sign inverse scaled by 1/L. Its API includes `dft_apply`, `invDFT_apply`, and `dft_dft` (the latter includes index reflection).

For the immediate complex implementation, the lowest-maintenance approach is to transport this DFT to the band, then add the scalar a to obtain U. Prove a bridge between `ZMod.stdAddChar` and the notes' chosen exponential root. If arbitrary primitive roots or coefficient fields are a real downstream requirement, keep the generic layer as a separate small construction. Arbitrary primitive roots correspond to relabelings; they do not automatically give the same trigonometric formula with k unchanged.

This is a three-layer dependency order within the two-tier idea: characters → unscaled linear equivalence → normalized complex isometry. It avoids duplicating a large inverse proof while exposing the algebraic facts the project needs.

## Dispersion and corner cases

**Lemma:** The primary exact Laplacian eigenvalue is

$$
 (\zeta^k-1)(1-\zeta^{-k})=\zeta^k+\zeta^{-k}-2.
$$

*Lean 4 Proof Strategy:*

- **Strategy:** Under the chosen field contract and `ζ ≠ 0`, use algebraic expansion. Distribute the terms: `ζ^k * 1 - ζ^k * ζ^{-k} - 1 + ζ^{-k}`. Because `ζ^k * ζ^{-k} = ζ^0 = 1`, the expression simplifies directly to `ζ^k + ζ^{-k} - 2` via `mul_sub`, `sub_mul`, and integer power addition.

Reject the suggestion's $-(\zeta^{k/2}-\zeta^{-k/2})^2$: fractional exponents are unspecified, and its sign is wrong. If w² = ζ^k, the correct expression is $(w-w^{-1})^2$, without the leading minus. Prefer the primary expression; no new root is needed.

**Lemma:** Only after selecting ζ = exp(2πi/L) should a separate evaluation lemma identify it with $-4\sin^2(\pi k/L)$. The root-of-unity algebra does not need trigonometric functions.

*Lean 4 Proof Strategy:*

- **Checked strategy:** Rewrite integer powers of the canonical exponential using `Complex.exp_int_mul`. Combine opposite exponentials with `Complex.exp_mul_I`, `Complex.cos_neg`, and `Complex.sin_neg`; then apply `Complex.cos_two_mul_eq_one_sub` (or the real counterpart), handling scalar casts and the nonzero denominator explicitly. These names were checked against the installed Mathlib with the compiler. This proves the canonical-root evaluation; arbitrary primitive roots may relabel the frequency.

Handle L = 1 explicitly: all characters are trivial, sums are one-term sums, and the nontrivial-character branch is empty. Handle the even Nyquist mode through the frozen band-negation theorem. Establish finite-sum transport, kernel signs, scalar casts, and matrix index orientation before freezing chapter 3.

## Evidence

Local API checked in `Mathlib/Analysis/Fourier/ZMod.lean` and `Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean`. The official [DFT documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/ZMod.html) and [primitive-root documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.html) confirm these interfaces. Local installed source and compiler probes control version-specific claims.
