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
Use `IsPrimitiveRoot ζ L`, a field/domain for cancellation, `[NeZero L]`, and `(L : K) ≠ 0` for inversion. For the canonical complex root, the installed theorem is `Complex.isPrimitiveRoot_exp L hL`, with `hL : L ≠ 0`. Confirm its exponential formula before defining the bridge to the character.

**Definition 3.2 (Algebraic Character and Unscaled DFT).** For any momentum $k \in \Lambda^*$ and position $x \in \Lambda = \mathbb{Z}/L\mathbb{Z}$, the algebraic character $\chi(k,x)$ is defined via integer representatives $\tilde{k}, \tilde{x} \in \mathbb{Z}$ (or as a canonical residue pairing on $\mathbb{Z}/L\mathbb{Z} \times \mathbb{Z}/L\mathbb{Z}$):

$$
\chi(k,x) := \zeta^{\tilde{k}\tilde{x}} \tag{3.3}
$$

Because $\zeta^L = 1$, this pairing is strictly representative-independent: $\zeta^{(\tilde{k} + sL)(\tilde{x} + tL)} = \zeta^{\tilde{k}\tilde{x}}$ for all $s, t \in \mathbb{Z}$.
We define the unscaled negative-sign analysis map $S$ and positive-sign synthesis map $T$:

$$
Sf(k) = \sum_{x \in \Lambda} f(x)\chi(-k,x) \tag{3.4}
$$
$$
Tg(x) = \sum_{k \in \Lambda^*} g(k)\chi(k,x) \tag{3.5}
$$

Here, $\chi(-k,x) = \chi(k,x)^{-1}$ uses the integer negation $-k \in \mathbb{Z}$, which agrees with the transported band negation $\ominus k$ via representative independence ($\chi(\ominus k, x) = \chi(-k, x)$) even when $-k \notin \Lambda^*$.

*Lean 4 Proof Strategy:*
Formalize $\chi$ either as an `AddChar (ZMod L) K` pairing `χ : ZMod L → ZMod L → K`, or via `ZMod.val` / integer representatives with an explicit auxiliary lemma `chi_representative_independent : ∀ s t, ζ ^ ((k + s*L) * (x + t*L)) = ζ ^ (k * x)`. Define $S$ and $T$ as linear maps on functions `Λ → K` and `Λ* → K`. Transport between `ZMod L` and `Λ*` using the frozen bijection `π` and `r` from Chapter 1.

**Lemma 3.3 (Orthogonality & Unscaled Inversion).** By summing the geometric series over the field $K$, the characters are orthogonal:

$$
\sum_{x \in \Lambda} \chi(k-k', x) = L \delta_{kk'} \tag{3.6}
$$

Here $\chi(k-k', x) = \chi(k, x)\chi(k', x)^{-1}$ uses the integer difference $k-k' \in \mathbb{Z}$, which identically matches transported band subtraction $k \ominus k' := k \oplus (\ominus k)$ under the character evaluation $\chi(k \ominus k', x) = \chi(k - k', x)$.

This leads directly to the unscaled inversion identities without requiring square roots:

$$
TS = L \cdot I, \qquad ST = L \cdot I \tag{3.7}
$$

*Lean 4 Proof Strategy:*
Bundle the nontrivial spatial character and use the checked `AddChar.sum_eq_zero_of_ne_one` after proving it is not the trivial character. The diagonal sum is L. Alternatively prove a geometric telescoping identity and cancel the nonzero factor; ζ^m need not have order L when gcd(m,L)>1. Expand both compositions with `Finset.sum_comm` and transport sums through the frozen band equivalence.

**Definition 3.4 (Unitary Physical Normalization).** For the physical fermionic layers defined over $\mathbb{C}$, we isolate the normalization into a single real scalar $a = 1/\sqrt{L}$ satisfying $L a^2 = 1$. The unitary DFT operator $U$ and its exact inverse are defined as:

$$
U = a S, \qquad U^{-1} = U^\dagger = a T \tag{3.8}
$$

Applying this unitary normalization preserves the counting canonical anticommutation relations (CAR) without introducing mixed scalar scalings.

*Lean 4 Proof Strategy:*
In the complex Hilbert layer define `a : ℝ := (Real.sqrt (L : ℝ))⁻¹`, prove positivity and `L*a^2=1` once, then cast a to ℂ. Use `EuclideanSpace ℂ (Ch01.Lattice L)` and `EuclideanSpace ℂ (Ch01.Band L)` for the counting inner products. Prove the adjoint kernel identity before bundling `a • S` as a linear isometry equivalence. Keep generic unscaled inversion free of square roots.

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
Use `ZMod L` for the periodic domain and the frozen function-space shifts. Apply additive-character laws rather than treating `Fin L` as an additive group. The algebraic eigenvalue is primary; derive its sine form only for the canonical complex root, with the chosen integer band representative.
