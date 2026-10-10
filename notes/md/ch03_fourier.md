### Chapter 3: Finite Fourier Transform

To ensure the exact algebraic nature of the bosonization mapping, we separate the finite character algebra from the Hilbert-space unitary normalization. This follows the formal strategy defined in [Appendix A01](../appendices/a01_fourier_scalars_and_characters.md) and proved in `Bosonize.Ch03`.

#### 3.1 Generic Algebraic Setting: Field $K$ and Primitive Roots

**Definition 3.1 (Primitive Root of Unity).** Let $K$ be a field, and $\zeta \in K$ a primitive $L$-th root of unity (Lean typeclass `IsPrimitiveRoot ζ L`).

- Field structure supplies zero-divisor cancellation: $(1 - \zeta^m) \sum_x \zeta^{mx} = 0 \implies \sum_x \zeta^{mx} = 0$ for $m \not\equiv 0 \pmod L$.

- Inverting the transform algebraically requires only that the integer size of the lattice is invertible in the field: $(L : K) \neq 0$.

- In particular, square roots are **not** needed for character orthogonality or algebraic inversion.

$$
\zeta^L = 1 \tag{3.1}
$$
$$
\forall m \in \{1, \dots, L-1\}, \quad \zeta^m \neq 1 \tag{3.2}
$$

*Canonical Complex Instantiation:*
For physical field theory, $K = \mathbb{C}$ and $\zeta$ is instantiated with the canonical root (`A01.canonicalRoot`):
$$
\zeta_{\mathrm{can}} := \exp\left(\frac{2\pi i}{L}\right) \in \mathbb{C}
$$
Lean verifies that $\zeta_{\mathrm{can}}$ is a primitive $L$-th root via Mathlib's `Complex.isPrimitiveRoot_exp L hL`.

---

#### 3.2 The Unscaled Transforms: Analysis and Synthesis

**Definition 3.2 (Analysis and Synthesis Linear Maps).**
Because the spatial domain $\Lambda = \mathbb{Z}/L\mathbb{Z}$ and the momentum band $\Lambda^*$ are distinct types in the formal architecture, the transforms are distinct $K$-linear maps between distinct function carriers:

- **Negative-Sign Analysis Map $S$ (`Ch03.analysis`):**
  $$
  S : ( \Lambda \to K ) \to ( \Lambda^* \to K ), \qquad Sf(k) := \sum_{x \in \Lambda} f(x) \chi_{\mathbb{Z}}(\zeta, -k.\mathrm{val}, x.\mathrm{val}) \tag{3.4}
  $$

- **Positive-Sign Synthesis Map $T$ (`Ch03.synthesis`):**
  $$
  T : ( \Lambda^* \to K ) \to ( \Lambda \to K ), \qquad Tg(x) := \sum_{k \in \Lambda^*} g(k) \chi_{\mathrm{band}}(L, \zeta, k, x) \tag{3.5}
  $$

*Note on Negative Signs:* $\chi(-k, x) = \chi(k, x)^{-1}$. By representative independence, evaluating at $-k.\mathrm{val} \in \mathbb{Z}$ agrees identically with evaluating at the transported band negation $\ominus k \in \Lambda^*$, even when $-k \notin \Lambda^*$.

---

#### 3.3 Orthogonality and Unscaled Inversion

**Lemma 3.3 (Dual Character Orthogonalities).**
The characters satisfy two complementary orthogonality relations:

1. **Spatial Orthogonality (`character_orthogonality`):**
   $$
   \sum_{x \in \Lambda} \chi_{\mathbb{Z}}(\zeta, k.\mathrm{val} - p.\mathrm{val}, x.\mathrm{val}) = L \cdot \delta_{k, p} \quad (\forall k, p \in \Lambda^*) \tag{3.6}
   $$

2. **Momentum (Dual) Orthogonality (`dual_character_orthogonality`):**
   $$
   \sum_{k \in \Lambda^*} \chi_{\mathbb{Z}}(\zeta, k.\mathrm{val}, x.\mathrm{val} - y.\mathrm{val}) = L \cdot \delta_{x, y} \quad (\forall x, y \in \Lambda) \tag{3.6a}
   $$

*Lean 4 Proof Mechanism:*
In Lean, spatial sums are evaluated using `AddChar.sum_eq_zero_of_ne_one`. Dual momentum sums are reduced to residue sums by transporting through the frozen bijection `A01.bandEquiv : Band L ≃ Lattice L` via `(bandEquiv L).sum_comp`.

**Theorem 3.3b (Unscaled Composition Identities & Algebraic Inversion).**
Applying Fubini sum interchange (`Finset.sum_comm`) and the orthogonality relations proves:
$$
T \circ S = L \cdot \mathrm{id}_{\Lambda \to K}, \qquad S \circ T = L \cdot \mathrm{id}_{\Lambda^* \to K} \tag{3.7}
$$
Whenever $(L : K) \ne 0$, the exact two-sided algebraic inverse of $S$ is (`inverseAnalysis`):
$$
S^{-1} = L^{-1} T \tag{3.7a}
$$
This establishes that $S$ is a linear equivalence (`Bijective S`) over any field where $L \ne 0$, without invoking $\sqrt{L}$.

---

#### 3.4 Unitary Normalization on Complex Euclidean Space

When constructing fermionic Fock spaces, physical creation and annihilation operators require the counting inner product $\langle f, g \rangle = \sum_x \overline{f(x)} g(x)$. To make the Fourier transform a Hilbert isometry that preserves CAR without spurious $\sqrt{L}$ factors in anticommutators, we introduce the unitary scaling.

**Definition 3.4 (Unitary Fourier Isometry).**

1. **The Counting Carriers:**
   $$
   \mathcal{H}_{\mathrm{pos}} := \ell^2(\Lambda) \equiv \mathrm{EuclideanSpace} \ \mathbb{C} \ \Lambda, \qquad \mathcal{H}_{\mathrm{mom}} := \ell^2(\Lambda^*) \equiv \mathrm{EuclideanSpace} \ \mathbb{C} \ \Lambda^*
   $$
   The function spaces are algebraically identified with Euclidean spaces via `WithLp.linearEquiv 2 ℂ`.

2. **The Real Normalization Scalar:**
   $$
   a := \frac{1}{\sqrt{L}} \in \mathbb{R}_{>0}, \qquad L a^2 = 1 \tag{3.8a}
   $$

3. **The Unitary Operator $U$ and its Inverse $U^{-1}$ (`unitaryFourier`):**
   $$
   U := a S_2 : \mathcal{H}_{\mathrm{pos}} \to \mathcal{H}_{\mathrm{mom}}, \qquad U^{-1} := a T_2 : \mathcal{H}_{\mathrm{mom}} \to \mathcal{H}_{\mathrm{pos}} \tag{3.8}
   $$

**Lemma 3.4b (Hilbert Adjoint and Isometry Properties).**

1. **Adjoint Identity (`analysisEuclidean_adjoint`):**
   $$
   S_2^\dagger = T_2
   $$
   *Proof:* In the counting inner product, $\langle S_2 f, g \rangle = \sum_{k} \overline{(S f)(k)} g(k) = \sum_{k} \sum_x \overline{f(x) \chi(-k, x)} g(k)$. Using $\overline{\chi(-k, x)} = \chi(k, x)$ and swapping sums yields $\sum_x \overline{f(x)} (T g)(x) = \langle f, T_2 g \rangle$.

2. **Unitarity (`unitary_adjoint`, `unitary_inner`):**
   $$
   U^\dagger = \overline{a} S_2^\dagger = a T_2 = U^{-1}
   $$
   $$
   \langle U f, U g \rangle = \langle f, U^\dagger U g \rangle = \langle f, g \rangle
   $$
   Hence $U$ is an exact linear isometry (`Isometry U`) and surjective (`Surjective U`).

---

#### 3.5 Diagonalization of Difference Operators & Exact Dispersion

**Lemma 3.5 (Diagonal Action on Characters).**
The umbral difference operators act as multiplication operators on the Fourier characters:
$$
\Delta \chi_{\mathrm{band}}(k, \cdot) = (\zeta^k - 1) \chi_{\mathrm{band}}(k, \cdot) \tag{3.9}
$$
$$
\nabla \chi_{\mathrm{band}}(k, \cdot) = (1 - \zeta^{-k}) \chi_{\mathrm{band}}(k, \cdot) \tag{3.10}
$$
Composing both operators yields the algebraic discrete Laplacian eigenvalue (`laplacian_eigenvalue_factor`):
$$
\Delta\nabla \chi_{\mathrm{band}}(k, \cdot) = (\zeta^k - 1)(1 - \zeta^{-k}) \chi_{\mathrm{band}}(k, \cdot) = (\zeta^k + \zeta^{-k} - 2) \chi_{\mathrm{band}}(k, \cdot) \tag{3.11}
$$

**Theorem 3.5b (Exact Dispersion in $\mathbb{C}$).**
Under the canonical root $\zeta = e^{2\pi i / L}$, the algebraic eigenvalue evaluates to the standard lattice dispersion (`canonical_laplacian_dispersion`):
$$
\zeta^k + \zeta^{-k} - 2 = -4 \sin^2\left(\frac{\pi k}{L}\right) \tag{3.12}
$$

*Lean 4 Proof:*
Using Euler's identity $\exp(i\theta) + \exp(-i\theta) = 2 \cos\theta$ with $\theta = 2\pi k / L$:
$$
\zeta^k + \zeta^{-k} - 2 = 2 \cos\left(\frac{2\pi k}{L}\right) - 2 = 2 \left( 1 - 2 \sin^2\left(\frac{\pi k}{L}\right) \right) - 2 = -4 \sin^2\left(\frac{\pi k}{L}\right)
$$
Mathlib verifies this using `Complex.cos_two_mul_eq_one_sub` and casts between $\mathbb{R}$ and $\mathbb{C}$. In the long-wavelength continuum limit $k \ll L$, $-4 \sin^2(\pi k / L) \approx -(2\pi k / L)^2 = -p^2$, recovering the continuum Laplacian $\partial_x^2$.
