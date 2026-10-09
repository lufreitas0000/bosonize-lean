# Architectural Directives for Chapter 3: Finite Fourier Transform (`Ch03Fourier.lean`)

### 1. Two-Tier Fourier Implementation (Preserving Physical Unitarity)
To preserve the canonical anticommutation relations (CAR) $\{c_x, c_y^\dagger\} = \delta_{xy}$ and number operator invariance in Chapters 4 and 5 without causing algebraic friction with square roots:
- Implement a two-tier Fourier transform:
  1. `unscaledDFT` and `unscaledInverseDFT`: Defined over any `[CommRing R]` with `(ζ : R)` and `(hζ : IsPrimitiveRoot ζ L)`.
     Evaluate sums directly without prefactors:
     `S(f)(k) = ∑ x, f(x) * ζ ^ (-k.val * x.val)`
     `S_inv(g)(x) = ∑ k, g(k) * ζ ^ (k.val * x.val)`
     Prove exact algebraic inversion over the ring: `S_inv (S f) = (L : R) • f`.
  2. `dft` and `dftInverse`: Specialized to `ℂ`. Scale by `(1 / Real.sqrt L : ℂ)`.
     Prove unitarity `U * Uᴴ = I` and `Uᴴ * U = I` as simple scalar corollaries of the unscaled inversion theorem and `Real.mul_self_sqrt`.
- DO NOT use asymmetric scalings (such as 1/L and 1), as this breaks the *-algebra involution and fermion anticommutation relations in subsequent chapters.

### 2. Root of Unity and Exponentiation Conventions
- Type plane wave evaluations as integer powers: `ζ ^ (k.val * (x.val : ℤ))` using Mathlib's `zpow`.
- Establish a foundational lemma:
  `lemma planeWave_representative_invariance (hζ : IsPrimitiveRoot ζ L) (k : Band L) (x : ℤ) :`
  proving that shifting `x` by multiples of `L` preserves the power via `hζ.zpow_eq_one_iff_dvd`.

### 3. Proof Flow for Orthogonality and Inversion
- Character sums must be proven on `ZMod L` first using Mathlib's `IsPrimitiveRoot.geom_sum_eq_zero`.
- Transfer the sum over `Band L` to a sum over `ZMod L` via `Ch01.band_projection_bijective`.
- Prove inversion by reordering finite sums via `Finset.sum_comm` and factoring constants with `Finset.mul_sum` / `Finset.sum_mul`.


---



Based on the specifications in `ch03_fourier.md`, the mathematical reference notes (specifically Chapters 3, 5, and 16), and the verified foundation in `Ch01LatticeBand` and `Ch02UmbralCalculus`, here is the proposed architecture for **Chapter 3: Finite Fourier Transform**.

To maintain the project's design philosophy—avoiding transcendental approximations and topological limits in favor of exact algebraic identities—we separate the interface into:

1. **Generic Algebraic Layer:** Formulated over any commutative ring $K$ equipped with a primitive root of unity $\zeta$ (`IsPrimitiveRoot ζ L`).
2. **Unitary $\ell^2$ / Complex Layer:** Formulated over $\mathbb{C}$ to support division by $\sqrt{L}$ and Hilbert space adjoints.

---

### Phase 1: Roots of Unity, Pairing, and Plane Waves

**Definitions:**

* `planeWavePairing (L : ℕ) (ζ : K) (k : Ch01.Band L) (x : Ch01.Lattice L) : K`
* Evaluates $\zeta^{k \cdot x}$ algebraically using integer powers: `ζ ^ (k.val * (x.val : ℤ))`.




* `planeWave (L : ℕ) (ζ : K) (k : Ch01.Band L) : Ch01.Lattice L → K`
* The spatial function $x \mapsto e_k(x) = \zeta^{k \cdot x}$.




* `planeWaveDual (L : ℕ) (ζ : K) (x : Ch01.Lattice L) : Ch01.Band L → K`
* The momentum-space function $k \mapsto \zeta^{k \cdot x}$.





**Supporting Lemmas (Lifting & Invariance):**

* `planeWave_zpow_eq (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) (x : ℤ) :`
* Proves that evaluating at $(x : \operatorname{ZMod} L)$ yields $\zeta^{k \cdot x}$ regardless of the integer representative chosen modulo $L$ (`ZMod.val` independence).




* `planeWave_zero_momentum (x : Ch01.Lattice L) : planeWave L ζ (zeroMomentum L hL) x = 1`
* `planeWave_zero_position (k : Ch01.Band L) : planeWave L ζ k 0 = 1`
* `planeWave_add_pos (k : Ch01.Band L) (x y : Ch01.Lattice L) :`
* $e_k(x + y) = e_k(x) e_k(y)$.




* `planeWave_bandAdd (k p : Ch01.Band L) (x : Ch01.Lattice L) :`
* $e_{k \oplus p}(x) = e_k(x) e_p(x)$ (relies on `band_add_projection` from Chapter 1).




* `planeWave_neg (k : Ch01.Band L) (x : Ch01.Lattice L) :`
* $e_{\ominus k}(x) = e_k(-x) = (e_k(x))^{-1}$.




* `planeWave_conj (k : Ch01.Band L) (x : Ch01.Lattice L) :`
* Over $\mathbb{C}$, $\overline{e_k(x)} = e_k(-x) = e_{\ominus k}(x) = \zeta^{-kx}$.



---

### Phase 2: Diagonalization of Discrete Difference Operators

This phase directly connects the umbral endomorphisms of Chapter 2 (`forwardDiff`, `backwardDiff`, `laplacian`) with the plane waves of Chapter 3.

**Lemmas:**

* `shift_planeWave (k : Ch01.Band L) :`
* $(E e_k)(x) = \zeta^{k.\text{val}} e_k(x)$.




* `inverseShift_planeWave (k : Ch01.Band L) :`
* $(E^{-1} e_k)(x) = \zeta^{-k.\text{val}} e_k(x)$.




* `forwardDiff_planeWave (k : Ch01.Band L) :`
* $\Delta e_k = (\zeta^{k.\text{val}} - 1) \cdot e_k$ (Equation 3.6).




* `backwardDiff_planeWave (k : Ch01.Band L) :`
* $\nabla e_k = (1 - \zeta^{-k.\text{val}}) \cdot e_k$ (Equation 3.7).




* `laplacian_planeWave_algebraic (k : Ch01.Band L) :`
* $\Delta\nabla e_k = (\zeta^{k.\text{val}} + \zeta^{-k.\text{val}} - 2) \cdot e_k = -(\zeta^{k.\text{val}/2} - \zeta^{-k.\text{val}/2})^2 \cdot e_k$.




* `laplacian_planeWave_trig (k : Ch01.Band L) :`
* Over $\mathbb{C}$, specializing $\zeta = e^{2\pi i / L}$ yields the continuous dispersion form $-4 \sin^2\left(\frac{\pi k.\text{val}}{L}\right) \cdot e_k$ (Equation 3.8).
(Note: Stated as an auxiliary evaluation over `Complex`, keeping the algebraic form primary).





---

### Phase 3: Orthogonality Relations

**Bridge Lemmas (Reindexing via Chapter 1 Bijection):**

* `sum_band_eq_sum_lattice (f : Ch01.Band L → K) :`
* $\sum_{k : \operatorname{Band} L} f(k) = \sum_{y : \operatorname{Lattice} L} f(\operatorname{representative} L\, hL\, y)$
* Proved using `Equiv.ofBijective` from `band_projection_bijective`.





**Lemmas:**

* `sum_primitiveRoot_pow_eq_zero (hζ : IsPrimitiveRoot ζ L) (hL : 0 < L) {m : ℤ} (hm : ¬ (L : ℤ) ∣ m) :`
* $\sum_{x \in \operatorname{ZMod} L} \zeta^{m \cdot x} = 0$.
* Standard character sum theorem in Mathlib (`IsPrimitiveRoot.geom_sum_eq_zero`).


* `spatial_orthogonality (hζ : IsPrimitiveRoot ζ L) (hL : 0 < L) (k p : Ch01.Band L) :`
* $\sum_{x : \operatorname{Lattice} L} \zeta^{(k.\text{val} - p.\text{val}) \cdot x.\text{val}} = \text{if } k = p \text{ then } (L : K) \text{ else } 0$ (Equation 3.9).




* `momentum_orthogonality (hζ : IsPrimitiveRoot ζ L) (hL : 0 < L) (x y : Ch01.Lattice L) :`
* $\sum_{k : \operatorname{Band} L} \zeta^{k.\text{val} \cdot (x.\text{val} - y.\text{val})} = \text{if } x = y \text{ then } (L : K) \text{ else } 0$ (Equation 3.10).


* Proved by transporting the sum over `Band L` to `ZMod L` via the bridge lemma, and evaluating the character sum on `ZMod L`.



---

### Phase 4: Discrete Fourier Transform (DFT) and Inversion

**Definitions:**

* `dftForward (L : ℕ) (ζ : ℂ) (f : Ch01.Lattice L → ℂ) : Ch01.Band L → ℂ`
* $\hat{f}(k) = \frac{1}{\sqrt{L}} \sum_{x : \operatorname{Lattice} L} f(x) \zeta^{-k \cdot x}$ (Equation 3.5).




* `dftInverse (L : ℕ) (ζ : ℂ) (g : Ch01.Band L → ℂ) : Ch01.Lattice L → ℂ`
* $\check{g}(x) = \frac{1}{\sqrt{L}} \sum_{k : \operatorname{Band} L} g(k) \zeta^{k \cdot x}$ (Equation 3.13).




* `dftOperator (L : ℕ) (hL : 0 < L) (hζ : IsPrimitiveRoot ζ L) : (Ch01.Lattice L → ℂ) ≃ₗ[ℂ] (Ch01.Band L → ℂ)`
* Bundles the forward DFT and inverse DFT into a complete complex linear equivalence (`LinearEquiv`).





**Lemmas:**

* `dft_inversion (hζ : IsPrimitiveRoot ζ L) (hL : 0 < L) (f : Ch01.Lattice L → ℂ) :`
* `dftInverse L ζ (dftForward L ζ f) = f`.




* `dft_inversion_dual (hζ : IsPrimitiveRoot ζ L) (hL : 0 < L) (g : Ch01.Band L → ℂ) :`
* `dftForward L ζ (dftInverse L ζ g) = g`.




* `dft_adjoint_eq_inverse (hζ : IsPrimitiveRoot ζ L) (hL : 0 < L) :`
* Proves that with respect to the canonical $\ell^2$ inner product, $U^\dagger = \text{dftInverse}$.




* `dft_unitary_left (hζ : IsPrimitiveRoot ζ L) (hL : 0 < L) :`
* $U^\dagger U = I$ (Equation 3.12).




* `dft_unitary_right (hζ : IsPrimitiveRoot ζ L) (hL : 0 < L) :`
* $U U^\dagger = I$ (Equation 3.11).




* `plancherel_identity (hζ : IsPrimitiveRoot ζ L) (hL : 0 < L) (f : Ch01.Lattice L → ℂ) :`
* $\sum_{x : \operatorname{Lattice} L} \vert{}f(x)\vert{}^2 = \sum_{k : \operatorname{Band} L} \vert{}\hat{f}(k)\vert{}^2$.



---

### Potential Friction Points & Design Recommendations

1. **Square Root Scalings:**
* In generic algebra, dividing by $\sqrt{L}$ requires a quadratically closed field. Defining `unscaledDftForward` ($\sum f(x) \zeta^{-kx}$) and `unscaledDftInverse` first allows the orthogonality and inversion cancellation to be proved over general rings $K$ where $(L : K)$ is invertible, before introducing $\sqrt{L}$ in $\mathbb{C}$.


2. **Double Sum Commutation:**
* Proving Fourier inversion (`dftInverse (dftForward f) = f`) requires exchanging finite sums $\sum_k \sum_x \mapsto \sum_x \sum_k$. `Finset.sum_comm` will handle this smoothly since both `Lattice L` and `Band L` are verified finite types (`[Fintype]`).




3. **Integer Powers vs Modular Exponentiation:**
* Do not define $e_k(x)$ as taking powers in `ZMod L`. Define it as integer exponentiation (`zpow`) of $\zeta$. Use the lemma `IsPrimitiveRoot.zpow_eq_one_iff_dvd` to verify that $\zeta^{a} = \zeta^b$ whenever $a \equiv b \pmod L$.


