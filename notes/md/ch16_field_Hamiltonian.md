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

#### 16.2 Chiral Separation and Spatial Collapse

**Lemma 16.2 (Chiral Decomposition).**
Because the dual fields are symmetric and antisymmetric combinations of the orientations ($\phi = \varphi_{+1} + \varphi_{-1}$ and $\theta = \varphi_{+1} - \varphi_{-1}$), the cross-terms cancel:

$$
(\Delta \phi(x))^2 + (\Delta \theta(x))^2 = 2 \left[ (\Delta \varphi_{+1}(x))^2 + (\Delta \varphi_{-1}(x))^2 \right] \tag{16.2}
$$

**Lemma 16.3 (Spatial Collapse via DFT).**
Substituting the Umbral gradient expansion of the chiral field (Lemma 15.5) and applying the spatial orthogonality constraint $\sum_{x} \zeta^{(m-n)x} = L \delta_{mn}$, both mixed terms in the square contribute, yielding an exact factor of $2L$:

$$
\sum_{x \in \Lambda} :\!(\Delta \varphi_\eta(x))^2\!: = 2L \sum_{m=1}^{h-1} \left( \frac{(\zeta^m - 1)(\zeta^{-m} - 1)}{m^2} \right) \rho_{m, \eta} \rho_{-m, \eta} \tag{16.3}
$$

#### 16.3 The Lattice Dispersion Theorem

**Definition 16.4 (Lattice Dispersion Weight).**
Let $\varepsilon(m)$ be the exact algebraic weighting factor:

$$
\varepsilon(m) := \frac{L}{m^2} (\zeta^m - 1)(\zeta^{-m} - 1) = \frac{4L}{m^2} \sin^2\left(\frac{\pi m}{L}\right) \tag{16.4}
$$

The algebraic form $(\zeta^m - 1)(\zeta^{-m} - 1)$ strictly avoids transcendental functions within the cyclotomic field.

**Theorem 16.5 (The Exact Weighted Lattice Energy).**
Combining the factors of 2 from the decomposition and the DFT collapse, $H_{\text{field}}$ evaluates exactly to:

$$
\forall \psi \in \mathcal{B}_{K, \vec{N}_{max}}, \quad H_{\text{field}} \psi = 4 \sum_{\eta \in \{+1, -1\}} \sum_{m=1}^{h-1} \varepsilon(m) \rho_{m, \eta} \rho_{-m, \eta} \psi \tag{16.5}
$$

#### 16.4 The Error Operator

If $H_{\text{field}}$ were to equal exactly a scaled $H_{\text{sug}}$, the weight $\varepsilon(m)$ would have to be completely independent of $m$. We define an algebraic reference constant (e.g., $g_0 := \varepsilon(1)$ within the cyclotomic field, or $g_0 := 4\pi^2/L$ if working strictly over $\mathbb{C}$).

**Definition 16.6 (The Field Error Operator).**
The exact algebraic error operator is:

$$
E_{\text{error}} := H_{\text{field}} - 4 g_0 H_{\text{sug}} = 4 \sum_{\eta} \sum_{m=1}^{h-1} \left( \varepsilon(m) - g_0 \right) \rho_{m, \eta} \rho_{-m, \eta} \tag{16.6}
$$

**Theorem 16.7 (Ground State Annihilation).**
The error operator strictly annihilates the joint sector ground state $\vert\vec{N}\rangle_0$ in every admissible charge sector, because every lowering mode $\rho_{-m}$ destroys the ground state. It is dynamically non-zero strictly on excited states.

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
