### Chapter 16: The Field-Theoretic Hamiltonian and Lattice Error

In Chapter 12, we proved that the fermionic kinetic energy operator ($\hat{P}$) is algebraically identical to the bosonic Sugawara Hamiltonian ($H_{\text{sug}}^{(M)} = \sum \rho_m \rho_{-m}$) on the energy budget subspace.

We construct a discrete Field Hamiltonian using exact Umbral differences ($\Delta$). The exact algebraic normalization adheres strictly to the corrections in [Appendix A06](../appendices/a06_chiral_fields_and_lattice_kernels.md).

#### 16.1 Definitions

**Definition 16.1 (The Discrete Field Hamiltonian).**
We define the real-space field Hamiltonian $H_{\text{field}}$ as the spatial sum over the lattice $\Lambda$ of the normal-ordered squared Umbral gradients of the dual fields:

$$
H_{\text{field}} := \sum_{x \in \Lambda} :\! \left( (\Delta \phi)(x) \right)^2 + \left( (\Delta \theta)(x) \right)^2 \!: \tag{16.1}
$$

Normal ordering applies *externally* to the squared field difference to prevent vacuum divergences.

*Lean 4 Proof Strategy:*
We will define `H_field` as a function from the lattice `Λ` to operators on the Hilbert space. The normal ordering `:\! ... \!:` will need to be formalized as an operator (`normal_order`) that reorders a polynomial in $\rho$ operators such that lowering operators ($m < 0$) are placed to the right of raising operators ($m > 0$). The definition itself will be a straightforward `Finset.sum` over $x \in \Lambda$.

#### 16.2 Chiral Separation and Spatial Collapse

**Lemma 16.2 (Chiral Decomposition).**
Because the dual fields are symmetric and antisymmetric combinations of the orientations ($\phi = \varphi_{+1} + \varphi_{-1}$ and $\theta = \varphi_{+1} - \varphi_{-1}$), the cross-terms cancel:

$$
(\Delta \phi(x))^2 + (\Delta \theta(x))^2 = 2 \left[ (\Delta \varphi_{+1}(x))^2 + (\Delta \varphi_{-1}(x))^2 \right] \tag{16.2}
$$

*Lean 4 Proof Strategy:*
This is an algebraic identity. We will first need an auxiliary lemma establishing the linearity of the Umbral gradient $\Delta$, giving $\Delta \phi = \Delta \varphi_{+1} + \Delta \varphi_{-1}$ and $\Delta \theta = \Delta \varphi_{+1} - \Delta \varphi_{-1}$. After substituting these into the LHS, the proof can be completed using Lean's `ring` or `linear_combination` tactics, since the operators evaluated at the same spatial point commute.

**Lemma 16.3 (Spatial Collapse via DFT).**
Substituting the Umbral gradient expansion of the chiral field (Lemma 15.5) and applying the spatial orthogonality constraint $\sum_{x} \zeta^{(m-n)x} = L \delta_{mn}$, both mixed terms in the square contribute, yielding an exact factor of $2L$:

$$
\sum_{x \in \Lambda} :\!(\Delta \varphi_\eta(x))^2\!: = 2L \sum_{m=1}^{h-1} \left( \frac{(\zeta^m - 1)(\zeta^{-m} - 1)}{m^2} \right) \rho_{m, \eta} \rho_{-m, \eta} \tag{16.3}
$$

*Lean 4 Proof Strategy:*
We will formalize the DFT of the chiral field from Lemma 15.5. The proof will proceed by substituting the expansion into the squared term, distributing the sum, and swapping the spatial sum with the momentum sums. We then apply the spatial orthogonality constraint (an auxiliary lemma: `sum_zeta_pow_eq_L_delta`). The $2L$ factor arises from the cross terms in the expansion when $n = -m$. The proof will rely on `Finset.sum` manipulation lemmas (`sum_mul`, `mul_sum`, `sum_comm`).

#### 16.3 The Lattice Dispersion Theorem

**Definition 16.4 (Lattice Dispersion Weight).**
Let $\varepsilon(m)$ be the exact algebraic weighting factor:

$$
\varepsilon(m) := \frac{L}{m^2} (\zeta^m - 1)(\zeta^{-m} - 1) = \frac{4L}{m^2} \sin^2\left(\frac{\pi m}{L}\right) \tag{16.4}
$$

The algebraic form $(\zeta^m - 1)(\zeta^{-m} - 1)$ strictly avoids transcendental functions within the cyclotomic field.

*Lean 4 Proof Strategy:*
The dispersion weight $\varepsilon(m)$ will be defined as an element of the cyclotomic field `K`. We will define `ε (m : ℕ) : K := (L / m^2) * (ζ^m - 1) * (ζ⁻ᵐ - 1)`. We must ensure $m \neq 0$ to avoid division by zero, which is guaranteed by the domain $1 \le m \le h-1$. The equality involving $\sin^2$ is purely descriptive in the algebraic cyclotomic setup and won't be part of the algebraic definition, but can be formalized as a separate equivalence lemma over `ℂ` if needed.

**Theorem 16.5 (The Exact Weighted Lattice Energy).**
Combining the factors of 2 from the decomposition and the DFT collapse, $H_{\text{field}}$ evaluates exactly to:

$$
\forall \psi \in \mathcal{B}_{K, \vec{N}_{max}}, \quad H_{\text{field}} \psi = 4 \sum_{\eta \in \{+1, -1\}} \sum_{m=1}^{h-1} \varepsilon(m) \rho_{m, \eta} \rho_{-m, \eta} \psi \tag{16.5}
$$

*Lean 4 Proof Strategy:*
This theorem chains Definition 16.1, Lemma 16.2, and Lemma 16.3. The proof strategy will start by applying `Lemma 16.2` to `H_field` inside the sum, then distributing the sum over the two chiral sectors, and applying `Lemma 16.3` to each. Finally, we rewrite using `Definition 16.4` to collect the algebraic terms into $\varepsilon(m)$ and factor out the constant 4.

#### 16.4 The Error Operator

If $H_{\text{field}}$ were to equal exactly a scaled $H_{\text{sug}}$, the weight $\varepsilon(m)$ would have to be completely independent of $m$. We define an algebraic reference constant (e.g., $g_0 := \varepsilon(1)$ within the cyclotomic field, or $g_0 := 4\pi^2/L$ if working strictly over $\mathbb{C}$).

**Definition 16.6 (The Field Error Operator).**
The exact algebraic error operator is:

$$
E_{\text{error}} := H_{\text{field}} - 4 g_0 H_{\text{sug}} = 4 \sum_{\eta} \sum_{m=1}^{h-1} \left( \varepsilon(m) - g_0 \right) \rho_{m, \eta} \rho_{-m, \eta} \tag{16.6}
$$

*Lean 4 Proof Strategy:*
This will be defined as an operator on the Hilbert space. Assuming $g_0$ is defined as `ε(1)` and `H_sug` is already defined, `E_error` is straightforwardly defined as `H_field - 4 * g_0 * H_sug`. A small equality lemma will show that this definition equals the expanded sum form by substituting Theorem 16.5 and the definition of `H_sug`.

**Theorem 16.7 (Ground State Annihilation).**
The error operator strictly annihilates the joint sector ground state $\vert\vec{N}\rangle_0$ in every admissible charge sector, because every lowering mode $\rho_{-m}$ destroys the ground state. It is dynamically non-zero strictly on excited states.

*Lean 4 Proof Strategy:*
The proof will proceed by applying $E_{\text{error}}$ to the state $|\vec{N}\rangle_0$. We rewrite $E_{\text{error}}$ into its sum form. For each term in the sum ($m > 0$), we have the combination $\rho_{m, \eta} \rho_{-m, \eta}$ acting on the ground state. By an auxiliary lemma `rho_lower_ground_state_eq_zero` (stating that lowering operators for $m>0$ annihilate the ground state), the inner term vanishes. The entire sum thus evaluates to 0.

**Physical Intuition (RG Irrelevance):**
By Taylor expanding the sine-squared weight factor over $\mathbb{C}$:
$$
\varepsilon(m) - g_0 \propto - \frac{m^2}{L^3} \tag{16.7}
$$
Because the error coefficient scales proportionally to $m^2$, translating this back into spatial derivatives via Fourier transform implies that the exact lattice error corresponds precisely to adding a higher spatial derivative perturbation:
$$
E_{\text{error}} \propto \int dx \left[ (\partial^2_x \phi)^2 + (\partial^2_x \theta)^2 \right] \tag{16.8}
$$
In the formal language of Wilsonian Renormalization Group (RG) flow, higher spatial derivatives possess higher scaling dimensions and are strictly **irrelevant operators**, proving the robustness of the Luttinger Liquid limit.
