
### Chapter 2: Umbral Calculus Core

We establish the formal algebraic foundations of the discrete calculus. Let $R$ be a commutative ring and $S \in \{\mathbb{Z}, \Lambda\}$ be a domain. We study the $R$-module and $R$-algebra of functions $R^S$.

**Definition 2.1 (Umbral Operators).** We define the linear endomorphisms in the space of operators $\mathrm{End}_R(R^S)$ for functions $f \in R^S$: The Shift operator $E$:

$$
(E f)(x) := f(x+1) \tag{2.1}
$$

 The Identity operator $I$:

$$
(I f)(x) := f(x) \tag{2.2}
$$

 The Forward Difference operator $\Delta$:

$$
\Delta := E - I \tag{2.3}
$$

$$
(\Delta f)(x) = f(x+1) - f(x) \tag{2.4}
$$

 The Backward Difference operator $\nabla$:

$$
\nabla := I - E^{-1} \tag{2.5}
$$

$$
(\nabla f)(x) = f(x) - f(x-1) \tag{2.6}
$$

 The discrete Laplacian operator $\Delta\nabla$:

$$
\Delta\nabla = E + E^{-1} - 2I \tag{2.7}
$$

*Lean 4 Proof Strategy:*
Formalize `R^S` as the `R`-module `S → R` (or `S →₀ R` for finitely supported functions). 
Define the operator algebra as `Module.End R (S → R)`.
Define `E` using `LinearMap.mk` mapping `f ↦ (fun x ↦ f (x + 1))`. Define `I` as `LinearMap.id`.
Define `Δ` and `∇` as differences of operators: `Δ = E - I` and `∇ = I - E⁻¹` (where `E⁻¹` is defined via shift by `-1`).
*Auxiliary Lemmas:* Prove that `E` is an automorphism with inverse `E⁻¹`, and establish basic commutativity of `E`, `I`, `E⁻¹`.

**Lemma 2.2 (Discrete Leibniz Rule).** For any functions $f, g \in R^S$, the exact discrete Leibniz rule holds without approximation:

$$
\Delta(fg) = (\Delta f)g + (Ef)(\Delta g) \tag{2.8}
$$

$$
\Delta(fg) = f(\Delta g) + (\Delta f)(Eg) \tag{2.9}
$$

*Lean 4 Proof Strategy:*
Formalize pointwise multiplication making `S → R` a `Pi.algebra`.
Proceed by expanding definitions at a generic point `x : S`. 
For instance, evaluate `Δ(fg)(x) = f(x+1)g(x+1) - f(x)g(x)`.
*Auxiliary Lemmas:* An algebraic trick/lemma `a * b - c * d = (a - c) * b + c * (b - d)` to rewrite the differences and factor appropriately, matching the RHS evaluations.

**Lemma 2.3 (Summation by Parts).** On the periodic lattice $\Lambda$, the forward and backward differences are negative adjoints:

$$
\sum_{x \in \Lambda} f(x) \Delta g(x) = - \sum_{x \in \Lambda} (\nabla f)(x) g(x) \tag{2.10}
$$

*Lean 4 Proof Strategy:*
Formalize the periodic domain $\Lambda$ as a finite type (e.g., `ZMod N`) and use `Finset.sum` over `Finset.univ`.
*Auxiliary Lemmas:* 
1. Reindexing lemma (translation invariance of the finite sum on `ZMod N`): `∑ f(x+1) = ∑ f(x)`.
2. Expand the definitions: `∑ f(x) (g(x+1) - g(x)) = ∑ f(x)g(x+1) - ∑ f(x)g(x)`. Reindex the first sum to `∑ f(x-1)g(x)` and recombine to form `- ∑ (f(x) - f(x-1)) g(x) = - ∑ (∇ f)(x) g(x)`.

**Lemma 2.4 (Newton Expansion).** The shift operator $E^n$ is expanded exactly via the binomial theorem:

$$
E^n = \sum_{k=0}^n \binom{n}{k} \Delta^k \tag{2.11}
$$

*Lean 4 Proof Strategy:*
Since `E`, `Δ`, and `I` live in the `R`-algebra `Module.End R (S → R)`, this is an application of the algebraic Binomial Theorem.
Rewrite `E = Δ + I`. 
*Auxiliary Lemmas:* Prove `Commute Δ I` (which is trivial since `I` is the identity). Use Mathlib's `Commute.add_pow` along with `I^k = I` to conclude the proof directly without induction on `n`.

**Definition 2.5 (Umbral Map and Heisenberg Pair).** Let $X^{\underline{n}} = X(X-1)\cdots(X-n+1)$ be the falling factorial polynomial. We define the umbral map $\Phi: R[X] \to R[X]$ linearly on the basis:

$$
\Phi(X^n) = X^{\underline{n}} \tag{2.12}
$$

 On the integer domain $\mathbb{Z} \to R$, we define the position multiplier operator $\beta$:

$$
(\beta f)(x) := x f(x-1) \tag{2.13}
$$

*Lean 4 Proof Strategy:*
Define `X^{\underline{n}}` recursively or using product over `Fin n`.
Define `Φ` as a linear map (`R[X] →ₗ[R] R[X]`) using `Polynomial.basisMonomials` to specify the action on the basis `X^n`.
Define `β` as an endomorphism on `ℤ → R`. Note that `x` acts by scalar multiplication: `x • f(x-1)` or coerced to `R` via `algebraMap ℤ R`.

**Lemma 2.6 (Umbral Commutation).** Let $D = \frac{d}{dX}$ be the formal polynomial derivative. Explicitly distinguishing the polynomial forward difference operator $\Delta_{\mathrm{poly}} : R[X] \to R[X]$, defined by $(\Delta_{\mathrm{poly}} p)(X) := p(X+1) - p(X)$, from the function-space operator $\Delta \in \mathrm{End}_R(R^S)$, the umbral map intertwines the continuous and discrete derivatives:

$$
\Phi \circ D = \Delta_{\mathrm{poly}} \circ \Phi \tag{2.14}
$$

 On the integer lattice $\mathbb{Z}$, the function-space operators form an exact Heisenberg pair:

$$
\Delta \beta - \beta \Delta = I \tag{2.15}
$$

 *(Note: A trace argument forbids any exact finite-dimensional matrix realization of this pair on a nonzero carrier over a field of characteristic 0, necessitating the use of infinite-dimensional function/polynomial spaces).*

*Lean 4 Proof Strategy:*
For `Φ ∘ D = Δ_poly ∘ Φ`: Prove equality of linear maps by checking on the monomial basis `X^n`.
*Auxiliary Lemmas:* 
1. `D (X^n) = n X^{n-1}`.
2. `Δ_poly (X^{\underline{n}}) = n X^{\underline{n-1}}`.
Extend by linearity using `LinearMap.ext_ring` or equivalent. Note that `Δ_poly` is typed as a linear map on `Polynomial R`, distinct from the function-space operator on `S → R`.
For the Heisenberg relation `Δ β - β Δ = I`: Expand both sides acting on an arbitrary function `f` at point `x`.
`((Δ ∘ β) f)(x) - ((β ∘ Δ) f)(x) = βf(x+1) - βf(x) - x(Δf)(x-1)`.
Substitute definitions: `(x+1)f(x) - x f(x-1) - x (f(x) - f(x-1))`. Distribute and simplify to get `f(x)`, which is `(I f)(x)`.
