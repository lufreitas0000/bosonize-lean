# BOSONIZE-LEAN: Mathematical Reference Notes

## Part IV: Phase 4 Free Dynamics & Dual Fields

### Chapter 16: The Field-Theoretic Hamiltonian and Lattice Error

In Phase 2 (Chapter 12), we proved that the fermionic kinetic energy operator ($H_0$) is algebraically identical to the bosonic Sugawara Hamiltonian ($H_{\text{sug}} = \sum \rho_m \rho_{-m}$) on the energy budget subspace. That identity is mathematically exact and requires no limits.

However, standard 1D Luttinger Liquid theory formulates the energy in *real space* as a macroscopic "vibrating string," where the energy is stored in the spatial gradients of the dual fields:

$$
H \propto \int dx \left[ (\partial_x \phi)^2 + (\partial_x \theta)^2 \right]
$$

To port this to our finite lattice, we construct a discrete Field Hamiltonian using the exact Umbral differences ($\Delta$).
**Crucial Physical Distinction:** As we will formally prove in this chapter, the equivalence between the real-space $H_{\text{field}}$ and the momentum-space $H_{\text{sug}}$ is **not an exact algebraic identity**. The discrete spatial derivative introduces a lattice dispersion error. We will formally define this error as an operator and prove that it corresponds exactly to a higher-derivative "irrelevant" perturbation in the Wilsonian Renormalization Group (RG) sense.

**Note on Normal Ordering and Squaring (**$:\!A^2\!: \text{ vs } (A)^2$**):**
A critical point in quantum field theory is that the squaring operation and the bosonic normal-ordering operation do not commute.
* Writing $:\! \phi(x)^2 \!:$ means expanding the field operator into creation and annihilation parts and mechanically moving all creators to the left.
* Writing $(:\!\phi(x)\!:)^2$ or normal-ordering the squared gradient $:\!(\Delta \phi(x))^2\!:$ treats the entire composite gradient as an observable and normal-orders the resulting bilinear mode expansion.
In our lattice field Hamiltonian $H_{\text{field}}$, we always apply the bosonic normal-ordering operator *externally* to the summed squared differences ($:\!(\dots)^2\!:$). This ensures that the vacuum expectation value vanishes identically ($\langle \Omega \mid H_{\text{field}} \mid \Omega \rangle = 0$), preventing zero-point energy divergences.

#### 16.1 Definitions

We construct the real-space Hamiltonian purely out of the dual phase and density fields defined in Chapter 15.

**Definition 16.1 (The Discrete Field Hamiltonian).**
We define the real-space field Hamiltonian $H_{\text{field}}$ as the spatial sum over the lattice $\Lambda$ of the normal-ordered squared Umbral gradients of the dual fields:

$$
H_{\text{field}} := \sum_{x \in \Lambda} :\! \left( (\Delta \phi)(x) \right)^2 + \left( (\Delta \theta)(x) \right)^2 \!: \tag{16.1}
$$

#### 16.2 Chiral Separation and Spatial Collapse

**Physical Intuition (Orthogonality of the Lattice):**
When we square the gradients, we generate cross-terms combining different modes, like $\rho_m \rho_n \zeta^{(m+n)x}$. However, summing a complex exponential over the entire periodic lattice acts as a perfect geometric filter. The sum over $x$ is exactly zero unless $m = -n$. This mathematical collapse acts as a physical mode-isolator, guaranteeing that macroscopic real-space energy decouples perfectly into independent momentum modes.

**Lemma 16.2 (Chiral Decomposition).**
Because the dual fields are symmetric and antisymmetric combinations of the Left ($L$) and Right ($R$) moving chiral fields ($\phi = \varphi_R + \varphi_L$ and $\theta = \varphi_R - \varphi_L$), the cross-terms identically cancel when the squares are added. The field Hamiltonian strictly decouples into independent chiral halves:

$$
(\Delta \phi(x))^2 + (\Delta \theta(x))^2 = 2 \left[ (\Delta \varphi_R(x))^2 + (\Delta \varphi_L(x))^2 \right] \tag{16.2}
$$

**Lemma 16.3 (Spatial Collapse via DFT).**
By substituting the Umbral gradient expansion of the chiral field (Theorem 15.5) into the summation, the spatial orthogonality constraint $\sum_{x \in \Lambda} \zeta^{(m-n)x} = L \delta_{mn}$ algebraically collapses the double momentum sum into a single sum over matching pairs of creation and annihilation modes:

$$
\sum_{x \in \Lambda} :\!(\Delta \varphi_\nu(x))^2\!: = L \sum_{m=1}^{h-1} \left( \frac{(\zeta^m - 1)(\zeta^{-m} - 1)}{m^2} \right) \rho_{m, \nu} \rho_{-m, \nu} \tag{16.3}
$$

#### 16.3 The Lattice Dispersion Theorem

We now establish the exact algebraic relationship between the real-space string energy and the momentum-space Sugawara modes.

**Definition 16.4 (Lattice Dispersion Weight).**
Let $\varepsilon(m)$ be the exact, mode-dependent geometric weighting factor produced by the discrete Umbral derivative:

$$
\varepsilon(m) := \frac{L}{m^2} (\zeta^m - 1)(\zeta^{-m} - 1) = \frac{4L}{m^2} \sin^2\left(\frac{\pi m}{L}\right) \tag{16.4}
$$

**Theorem 16.5 (The Exact Weighted Lattice Energy).**
On the energy budget subspace $\mathcal{B}_{K, \vec{N}_{max}}$, the macroscopic real-space field Hamiltonian $H_{\text{field}}$ evaluates exactly to a weighted Sugawara-like sum:

$$
\forall \psi \in \mathcal{B}_{K, \vec{N}_{max}}, \quad H_{\text{field}} \psi = 2 \sum_{\nu \in \{R, L\}} \sum_{m=1}^{h-1} \varepsilon(m) \rho_{m, \nu} \rho_{-m, \nu} \psi \tag{16.5}
$$

#### 16.4 The Continuum Limit and the Error Operator

**Physical Intuition (The RG Flow of the Lattice):**
If $H_{\text{field}}$ were to exactly equal the standard continuous Sugawara Hamiltonian (up to a global geometric constant $g_0$), then the weight $\varepsilon(m)$ would have to be completely independent of $m$.
For small momenta ($m \ll L$), the sine function linearizes ($\sin(x) \approx x$), and the weight approaches a constant: $\varepsilon(m) \approx \frac{4\pi^2}{L} =: g_0$.
However, for higher modes, the lattice puts a curve in the acoustic phonon dispersion. This means that even on the strictly bounded budget space, **the discrete spatial gradients do not perfectly reconstruct the free fermion energy.** There is a residual error operator.

**Definition 16.6 (The Field Error Operator).**
We define the global scaling constant $g_0 := \frac{4\pi^2}{L}$. The algebraic error operator $E_{\text{error}}$, which measures the exact discrepancy between the spatial field energy and the Sugawara momentum energy, is defined as:

$$
E_{\text{error}} := H_{\text{field}} - g_0 H_{\text{sug}} = 2 \sum_{\nu \in \{R, L\}} \sum_{m=1}^{h-1} \left( \varepsilon(m) - g_0 \right) \rho_{m, \nu} \rho_{-m, \nu} \tag{16.6}
$$

**Theorem 16.7 (RG Irrelevance of the Lattice Error).**
The error operator is generally non-zero on the budget space (it strictly vanishes only on the vacuum state $\vert\Omega\rangle$). By Taylor expanding the sine-squared weight factor, the leading term of the operator's mode-coefficient evaluates to:

$$
\varepsilon(m) - g_0 = \frac{4L}{m^2} \left[ \left(\frac{\pi m}{L}\right)^2 - \frac{1}{3}\left(\frac{\pi m}{L}\right)^4 + \dots \right] - \frac{4\pi^2}{L} \propto - \frac{m^2}{L^3} \tag{16.7}
$$

Because the error coefficient scales proportionally to $m^2$, translating this back into spatial derivatives via Fourier transform implies that the lattice error corresponds precisely to adding a higher-derivative perturbation:

$$
E_{\text{error}} \propto \int dx \left[ (\partial^2_x \phi)^2 + (\partial^2_x \theta)^2 \right] \tag{16.8}
$$

In the formal language of Wilsonian Renormalization Group (RG) flow, higher spatial derivatives possess higher scaling dimensions and are strictly **irrelevant operators**. In the true continuum/IR limit ($L \to \infty$ with momentum $m$ fixed), the error operator strictly vanishes ($E_{\text{error}} \to 0$), successfully recovering the pure continuous Luttinger Liquid.

#### 16.5 Technical Notes for the Lean 4 Formalization (Chapter 16)

1. **Handling the Spatial Summation (`Finset.sum_comm`):**
   * The proof of Lemma 16.3 should be structured in Lean as two distinct lemmas: first, expanding the square of the sum; second, pulling the spatial sum $\sum_x$ inward using `Finset.sum_comm`.
   * Invoke the exact orthogonality lemma (from Chapter 3) to rewrite $\sum_x \zeta^{(m-n)x}$ as `L * ite (m = n) 1 0`.
   * Finally, `Finset.sum_ite` will algebraically collapse the double sum $\sum_m \sum_n$ into the single sum $\sum_m$.

2. **Purely Algebraic Weight Definition (**$\varepsilon(m)$**):**
   * Do not use `Real.sin` or `Complex.sin` in the definition of $\varepsilon(m)$ or $E_{\text{error}}$, as Lean's algebraic ring API handles these poorly.
   * Define $\varepsilon(m)$ strictly using the algebraic form `(ζ^m - 1) * (ζ^-m - 1) / m^2 * L` over the cyclotomic extension field.
   * Define $g_0$ dynamically as the first term of the discrete polynomial expansion of the cyclotomic algebraic evaluation, allowing you to mathematically state $E_{\text{error}}$ strictly within algebraic bounds.

3. **Submodule Bounds and the Error Operator:**
   * It is highly recommended to state the action of $E_{\text{error}}$ using the `BudgetSpace` subtype wrapper to guarantee that modes where $m \ge K$ are mapped exactly to the zero vector, keeping the sums formally finite.
