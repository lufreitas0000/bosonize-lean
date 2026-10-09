### Chapter 3: Finite Fourier Transform

To ensure the exact algebraic nature of the bosonization mapping, we separate the finite character algebra from the Hilbert-space unitary normalization. This follows the formal strategy defined in [Appendix A01](../appendices/a01_fourier_scalars_and_characters.md).

**Definition 3.1 (Primitive Root of Unity).** Let $K$ be a field, and $\zeta \in K$ a primitive $L$-th root of unity. To avoid zero divisors obstructing orthogonality, we strictly require $(L : K) \neq 0$.

$$
\zeta^L = 1 \tag{3.1}
$$
$$
\forall m \in \{1, \dots, L-1\}, \quad \zeta^m \neq 1 \tag{3.2}
$$

Analytically, we will later instantiate this with $\zeta = e^{2\pi i / L}$ in $\mathbb{C}$.

*Lean 4 Proof Strategy:*
Use Mathlib's `IsPrimitiveRoot ζ L` from `RingTheory.RootsOfUnity.Basic`. The condition $(L : K) \neq 0$ should be formalized using `NeZero (L : K)` or by requiring `CharZero K` if we restrict to characteristic zero fields. For the complex instantiation, use `Complex.exp` and prove it satisfies `IsPrimitiveRoot` using existing Mathlib lemmas like `Complex.isPrimitiveRoot_exp_of_ne_zero`.

**Definition 3.2 (Algebraic Character and Unscaled DFT).** For any momentum $k \in \Lambda^*$ and position $x \in \Lambda$, the algebraic character is defined as:

$$
\chi(k,x) = \zeta^{kx} \tag{3.3}
$$

We define the unscaled negative-sign analysis map $S$ and positive-sign synthesis map $T$:

$$
Sf(k) = \sum_{x \in \Lambda} f(x)\chi(-k,x) \tag{3.4}
$$
$$
Tg(x) = \sum_{k \in \Lambda^*} g(k)\chi(k,x) \tag{3.5}
$$

*Lean 4 Proof Strategy:*
Formalize $\Lambda$ and $\Lambda^*$ as `Fin L`. Define $\chi(k,x)$ as `ζ ^ (k * x)`. Define $S$ and $T$ as linear maps (or linear equivalences) on `Fin L → K`. Use `Finset.sum` over `Finset.univ` for the summation. To ensure the type system cooperates, cast the indices $k$ and $x$ to $\mathbb{N}$ when used in the exponent of $\zeta$, e.g., `ζ ^ (k.val * x.val)`.

**Lemma 3.3 (Orthogonality & Unscaled Inversion).** By summing the geometric series over the valid field, the characters are orthogonal:

$$
\sum_{x \in \Lambda} \chi(k-k', x) = L \delta_{kk'} \tag{3.6}
$$

This leads directly to the unscaled inversion identities without requiring square roots:

$$
TS = L \cdot I, \qquad ST = L \cdot I \tag{3.7}
$$

*Lean 4 Proof Strategy:*
Formalize orthogonality using `geom_sum` and `IsPrimitiveRoot.sum_zpow_eq`. The necessary auxiliary lemma is the geometric series sum for roots of unity: if $k \neq k'$, $\zeta^{k-k'}$ is a root of unity $\neq 1$, so its powers sum to $0$. Use `IsPrimitiveRoot.sum_pow_eq` which states exactly this. For the unscaled inversion, compose $T$ and $S$ and swap the sums using `Finset.sum_comm`. Then apply the orthogonality identity to collapse the inner sum to $L \delta_{kk'}$, proving $TS = L \cdot I$.

**Definition 3.4 (Unitary Physical Normalization).** For the physical fermionic layers defined over $\mathbb{C}$, we isolate the normalization into a single real scalar $a = 1/\sqrt{L}$ satisfying $L a^2 = 1$. The unitary DFT operator $U$ and its exact inverse are defined as:

$$
U = a S, \qquad U^{-1} = U^\dagger = a T \tag{3.8}
$$

Applying this unitary normalization preserves the counting canonical anticommutation relations (CAR) without introducing mixed scalar scalings.

*Lean 4 Proof Strategy:*
This definition should be made specific to $K = \mathbb{C}$ or an extension field where $a = 1/\sqrt{L}$ exists. In Lean 4, use `Real.sqrt L` or `(L : ℂ) ^ (-1/2)`. Define $U$ as a scaled version of $S$. Define the adjoint $U^\dagger$ using the standard inner product on `Fin L → ℂ` (using `starRingEnd ℂ` for complex conjugation). We will need to prove that $T$ corresponds to the adjoint of $S$ up to conjugation of the characters. Specifically, prove $S^\dagger = T$ under complex conjugation, then use $L a^2 = 1$ to prove $U U^\dagger = I$.

**Lemma 3.5 (Diagonalization of Difference Operators).** The umbral difference operators act strictly diagonally on the characters:

$$
\Delta \chi(k, \cdot) = (\zeta^k - 1)\chi(k, \cdot) \tag{3.9}
$$
$$
\nabla \chi(k, \cdot) = (1 - \zeta^{-k})\chi(k, \cdot) \tag{3.10}
$$

The exact algebraic discrete Laplacian eigenvalue is:

$$
\Delta\nabla \chi(k, \cdot) = (\zeta^k + \zeta^{-k} - 2)\chi(k, \cdot) \tag{3.11}
$$

Only upon evaluation in $\mathbb{C}$ with $\zeta = e^{2\pi i / L}$ does this algebraically reduce to the physical dispersion $-4\sin^2\left(\frac{\pi k}{L}\right)$.

*Lean 4 Proof Strategy:*
Formalize $\Delta f(x) = f(x+1) - f(x)$ and $\nabla f(x) = f(x) - f(x-1)$ using `Fin L` with modular arithmetic. Apply these to $\chi(k, x) = \zeta^{kx}$. The proof uses basic exponent laws `ζ ^ (k * (x + 1)) = ζ ^ (k * x) * ζ ^ k`, factoring out $\zeta^{kx}$. For the reduction to the physical dispersion, introduce an auxiliary lemma converting $\zeta^k + \zeta^{-k} - 2$ in $\mathbb{C}$ to sines using Euler's formula (`Complex.exp_mul_I`) and half-angle trigonometric identities available in Mathlib's `Real.sin` API.
