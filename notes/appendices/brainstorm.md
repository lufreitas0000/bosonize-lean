## Brain-storm for future projects


The ground-up re-derivation of the Dirac/QED3 duality provides the exact mathematical blueprint for structuring the Lean 4 formalization. To formalize the Mross et al. mapping, the project must be orchestrated into orthogonal submodules, treating the 2+1D problem as a stack of 1D systems coupled by strict algebraic rules.

Here is the analytical breakdown of the difficulties, foundational setup, and strategies for formalizing the dynamics and lattice symmetries.

### I. Foundational Setup: Translating the Coupled-Wire Duality

The Mross et al. duality relies on an array of 1D chiral wires indexed by $y$, inter-wire hopping, and a staggered Chern-Simons gauge field.

* **Difficulty 1: The Non-Local Dual Transformation Matrix**
The dual fields are defined via $\tilde{\phi}_y = \sum_{y'} D_{y,y'} \phi_{y'}$ where $D_{y,y'} = (1 - \delta_{y,y'}) \text{sgn}(y - y')(-1)^{y'}$. In a finite lattice, the sign function and the summation boundaries introduce exact edge effects that are usually swept under the rug in continuum literature.


* **Strategy:** The lattice geometry for $y$ must be strictly bounded. The matrix $D$ must be formalized as a `LinearEquiv` (or an explicit matrix with a proven inverse $D^2 = I$) acting on the vector space of 1D fields. The $(-1)^y$ chirality indicator must be implemented using the signed indicator convention (rather than a generic label) to algebraically control the anti-commutation across wires.




* **Difficulty 2: Discrete Gauge Invariance and Anomalies**
The staggered Chern-Simons term $\Delta A_{0,y}(A_{1,y+1} + A_{1,y})$ is used to cancel the chiral anomaly of the individual wires. In Lean, "anomalies" cannot be hand-waved via continuous path integral Jacobians.


* **Strategy:** Formalize gauge transformations strictly as unitary operators $U = \exp(i \sum \alpha_y(x) \hat{n}_y(x))$. The "anomaly" must be proven as a non-zero commutator between the discrete gauge generator and the boundary terms of the Umbral difference operators ($\Delta_x$). The cancellation theorem requires proving that the sum of the wire commutators and the staggered Chern-Simons commutators identically evaluates to zero on the budget subspace.


* **Foundational Roadmap (Submodule Orchestration):**
1. **Module A (1D Baseline):** Import the existing 1+1D `Bosonize-Lean` kinematics.
2. **Module B (Y-Index Tensor Space):** Define the multi-wire Hilbert space as $\bigotimes_y \mathcal{H}_y$.
3. **Module C (Discrete Gauge Fields):** Define $A_\mu$ as link variables $U_{x,y} = \exp(i A_{x,y})$ acting on the lattice edges.
4. **Module D (The Duality Map):** Define the exact operator $D_{y,y'}$ and prove it acts as an `AlgEquiv` on the multi-wire Kac-Moody algebra.



### II. Dynamics, Imaginary Time, and Discretization

Addressing dynamics and imaginary time ($\tau$) on a strict lattice introduces severe structural mismatches if space is discrete and time is continuous.

* **The Holomorphic Mismatch:**
In continuum CFT, $z = \tau + ix$ relies on the symmetric scaling of space and time. If $x \in \mathbb{Z}/L\mathbb{Z}$ and $\tau \in \mathbb{R}$, defining $\partial_z = \frac{1}{2}(\partial_\tau - i\Delta_x)$ creates an operator that does not satisfy the continuous Cauchy-Riemann equations nor the exact chain rule. The functional analysis overhead (`MeasureTheory`, continuous semigroups) destroys the purely algebraic solvability.
* **Strategy 1: Fully Discrete Spacetime (Transfer Matrices)**
Treat time on equal footing with space. Discretize $\tau \to \tau_n \in \mathbb{Z}$. The Hamiltonian $H$ is replaced by the Transfer Matrix $T = \exp(-\Delta \tau H)$. Time evolution is defined algebraically as repeated application of $T$.
* **Strategy 2: The Suzuki-Trotter Limit**
If continuous time is strictly required, define the time evolution operator as formal power series (truncated on an energy budget) and evaluate equal-time commutators. For non-equal times, the Heisenberg equations of motion $i\partial_t O = [O, H]$ can be formalized as algebraic differential equations, but evaluating their integrated solutions requires leaving algebraic domains.

### III. Lattice CFT, Symmetries, and RG Flow

Standard bosonization literature relies heavily on Renormalization Group (RG) flow and Virasoro algebras.

* **Difficulty 1: Virasoro on the Lattice**
The Virasoro algebra does not exist exactly on a finite lattice. The Koo-Saleur formula defines discrete generators $L_n = \frac{L}{2\pi} \sum_x e^{inx} (H_x + i P_x)$, but their commutator contains error terms: $[L_n, L_m] = (n-m)L_{n+m} + \frac{c}{12}n^3 \delta_{n,-m} + O(1/L)$.
* **Strategy:** Do not attempt to prove exact CFT symmetries. Instead, state the Koo-Saleur commutators as exact equalities *including* the explicit error operators. The algebraic focus must remain on the Kac-Moody currents ($\rho_m$), which *are* exact on the lattice budget space, rather than the stress-energy tensor.


* **Difficulty 2: Formalizing RG Flow**
Continuous RG flow equations like $dg/dl \propto g^2$ rely on integrating out infinitesimal momentum shells, which is mathematically ill-defined on a rigid integer lattice $\Lambda^*$.
* **Strategy:** Replace continuous RG with discrete **Block Decimation** or **Entanglement Renormalization** (e.g., MERA). Define an exact algebraic map that traces out the highest-energy modes in the budget space $\mathcal{B}_K \to \mathcal{B}_{K-1}$ and maps the operators to effective operators.


* **Useful Exact Lattice Symmetries:**
To compute without thermodynamic limits, the focus must shift to exact discrete symmetries.
1. **Topological T-Duality:** As seen in the 1+1D project, $g \leftrightarrow 1/g$ can be proven as an exact `AlgEquiv` for the entire Hamiltonian matrix.
2. **Kramers-Wannier Duality:** Translates directly to the 2+1D lattice gauge theory as a mapping between the link variables $A_\mu$ and plaquette fluxes.
3. **Particle-Hole Symmetry (C):** For the half-filled Landau level mapping, $\mathcal{C}$ acts locally on the dual Dirac fermions ($\mathcal{C}\tilde{\Psi}\mathcal{C}^{-1} = i\sigma^y \tilde{\Psi}$). This can be formalized as an exact involution on the finite lattice operators.


---

To extend the formalization into dynamics and two-dimensional conformal field theory without invoking thermodynamic limits or continuous topology, the algebraic framework must transition from a 1D spatial Hamiltonian to a 2D discrete Euclidean spacetime.

### 1. Fully Discrete Spacetime and Transfer Matrices

In a fully discrete 1+1D formulation, time $\tau$ is discretized as an integer index $\tau_n \in \mathbb{Z}$. The Hamiltonian $H$ is abandoned as the primary dynamical generator. Instead, dynamics are governed by the Transfer Matrix $T$.

* **Algebraic Definition:** The transfer matrix $T \in \mathrm{End}_{\mathbb{C}}(\mathcal{H})$ acts on the spatial Hilbert space to advance the system by one discrete time step: $\psi(\tau + 1) = T \psi(\tau)$.
* **Local Plaquette Weights:** Rather than evaluating $\exp(-a H)$, $T$ is constructed as a finite product of local vertex or plaquette operators acting on adjacent sites. This keeps the operator strictly within the finite-dimensional algebra.
* **The Yang-Baxter Equation:** Continuous integrability (Bethe Ansatz) is replaced by the Yang-Baxter equation. Commutativity of transfer matrices $[T(u), T(v)] = 0$ for different spectral parameters $u, v$ provides the exact algebraic conservation laws on the lattice, substituting the continuous Noether currents.

### 2. Discrete Complex Analysis and Umbral Cauchy-Riemann

Discrete complex analysis allows the formalization of holomorphic fields purely through finite differences. To implement this, the 1D spatial lattice $\Lambda$ must be expanded to a 2D Euclidean grid $\Lambda \times \Lambda_\tau$.

* **Discrete Cauchy-Riemann Equations:** Let $f: \Lambda \times \Lambda_\tau \to \mathbb{C}$ be a field evaluated on the vertices. Using the forward difference operators $\Delta_x$ and $\Delta_\tau$, a function is defined as discrete holomorphic (or pre-holomorphic) if it satisfies a linear difference equation matching the grid geometry. On a square lattice, the standard definition is:

$$\Delta_x f(x, \tau) + i \Delta_\tau f(x, \tau) = 0$$


* **Discrete Contour Integration:** Integration is replaced by a formal sum over directed edges forming a path $P$. A discrete form $w = f dx + g d\tau$ integrated over a closed fundamental plaquette sums the values on its four edges.
* **Discrete Cauchy Theorem:** If $f$ satisfies the discrete Cauchy-Riemann equations, the sum of the directed differences around any closed boundary of plaquettes evaluates identically to zero. In Lean, this is proven via the telescoping sum properties of $\Delta$, completely bypassing analytic limits and Stokes' Theorem.
* **Dirac Operator on the Lattice:** For fermions, the discrete Cauchy-Riemann equation directly matches the massless Kogut-Susskind (staggered) Dirac equation. The holomorphic and anti-holomorphic components of the CFT factorize algebraically as the left-moving and right-moving chiral modes on the null-diagonals of the lattice.

### 3. CFT Structures Applicable on the Lattice

While the full continuous Virasoro algebra does not exist on a finite lattice, its foundational algebraic and statistical consequences survive as exact identities.

* **Temperley-Lieb Algebra:** The algebraic constraints governing boundary conditions and loop models in CFT map directly to the Temperley-Lieb algebra. This algebra is exactly finite-dimensional and can be encoded in Lean as a set of generators satisfying $e_i^2 = \sqrt{Q} e_i$ and $e_i e_{i\pm1} e_i = e_i$.
* **Koo-Saleur Generators:** The discrete Fourier transforms of the local energy density $h_x$ and momentum density $p_x$ define lattice Virasoro generators $L_n = \frac{L}{2\pi} \sum_x \zeta^{-nx} (h_x + i p_x)$. While they do not close exactly, their commutation relations evaluate to the Virasoro algebra plus an exact, calculable error operator $\mathcal{E}_L$ that scales as $1/L$.
* **Exact Finite-Size Scaling:** Conformal dimensions ($\Delta, \bar{\Delta}$) are traditionally extracted from the continuous $1/L$ scaling of the energy spectrum. In the lattice formalization, these dimensions are redefined as the exact algebraic roots of the eigenvalues of the Transfer Matrix $T$.
* **Modular Covariance:** The partition function $Z$ is defined as the exact algebraic trace of the transfer matrix: $Z = \mathrm{Tr}(T^L)$. Modular transformations (exchanging space and time) reduce to evaluating the trace by slicing the 2D lattice vertically instead of horizontally, yielding an exact matrix identity.

### 4. Expansion Strategy for the Lean 4 Project

To incorporate these 2D structures into the existing formalization without introducing analytical limits, we must establish the following isolated submodules.

* **2D Spacetime Grid:** Define the geometry as the Cartesian product of two finite cyclic groups $\Lambda_x \times \Lambda_\tau$.
* **Algebraic Fields:** Define variables not as functions of time, but as elements of the ring of functions $R^{\Lambda_x \times \Lambda_\tau}$.
* **Difference Dirac Equation:** Formulate the discrete Cauchy-Riemann equation as a linear map in $\mathrm{End}_{\mathbb{C}}(R^{\Lambda_x \times \Lambda_\tau})$ and define the holomorphic fields exactly as the kernel of this map.
* **Transfer Matrix Spectral Theory:** Define $T$ and use the Perron-Frobenius theorem (applicable to finite matrices) to isolate the maximal eigenvalue (the vacuum state) and the exact spectral gaps (the conformal weights), replacing continuous Hamiltonian diagonalization.


---


### I. Deconstructing Difficulty 2: Continuous vs. Discrete RG

In continuum field theory, the Wilsonian Renormalization Group (RG) defines a scale parameter $\ell = \ln(\Lambda_0 / \Lambda)$ and integrates out an infinitesimal momentum shell $k \in [\Lambda - d\Lambda, \Lambda]$. This generates a differential flow equation for coupling constants:


$$\frac{dg_i}{d\ell} = \beta_i(\{g_j\}) = (2 - \Delta_i) g_i - \pi \sum_{j,k} C_{jk}^i g_j g_k + \dots$$


where $\Delta_i$ is the scaling dimension and $C_{jk}^i$ are Operator Product Expansion (OPE) coefficients.

#### Why this breaks algebraically on the lattice

1. **Discrete Momentum Density:** On our periodic lattice $\Lambda = \mathbb{Z}/L\mathbb{Z}$, momentum space is the discrete band $\Lambda^* = \{-h+1, \dots, h\}$. The mode spacing is strictly quantized at $\Delta k = 2\pi/L$. There is no continuous parameter $\ell$, nor an infinitesimal shell $dk$.


2. **Analysis Overhead in Lean 4:** Formalizing a continuous flow $\frac{dg}{d\ell}$ requires importing Mathlib’s topology, Fréchet derivatives, differential equations, and Picard-Lindelöf existence theorems. This introduces analytical baggage and breaks the design goal of keeping the formal core purely algebraic.
3. **The UV Cutoff is Many-Body, Not Single-Particle:** The physical cutoff in our theory is not a hard momentum cutoff $\Lambda_0$, but the many-body **energy budget** $K$ acting on the filtration $\mathcal{B}_K$.



---

### II. The Algebraic Strategy: Discrete Mode Decimation

Instead of an infinitesimal differential flow, RG on a filtered polynomial Fock space is a **discrete algebraic projection** between observable endomorphism algebras:


$$\mathcal{R}_K : \mathrm{End}_{\mathbb{C}}(\mathcal{B}_K) \longrightarrow \mathrm{End}_{\mathbb{C}}(\mathcal{B}_{K-1})$$

#### The Construction

Recall from Chapter 8 and Chapter 11 that the bosonic Fock space over mode budget $K$ is modeled by multivariate polynomials in the variables $\{X_1, \dots, X_K\}$:


$$\mathcal{F}_{\le K} = \mathrm{span}_{\mathbb{C}} \left\{ \prod_{m=1}^K X_m^{r_m} \mathrel{\Bigg\vert{}} \sum_{m=1}^K m \cdot r_m \le K \right\}$$


Any excitation involving the highest available mode $X_K$ has energy at least $K$. Therefore, within the budget $\mathcal{F}_{\le K}$, the mode $K$ can only appear at most once, and only when all other modes $X_1, \dots, X_{K-1}$ are in their vacuum state:


$$\mathcal{F}_{\le K} = \mathcal{F}_{\le K-1} \oplus \mathbb{C} \cdot X_K$$

We define the single-step **Discrete Decimation Map** as the partial trace (vacuum expectation value) with respect to the highest mode:


$$\mathbb{E}_K : \mathrm{End}_{\mathbb{C}}(\mathcal{F}_{\le K}) \longrightarrow \mathrm{End}_{\mathbb{C}}(\mathcal{F}_{\le K-1})$$


Operationally, for any operator $A \in \mathrm{End}_{\mathbb{C}}(\mathcal{F}_{\le K})$, $\mathbb{E}_K(A)$ evaluates the matrix elements by setting $a_K \vert 0 \rangle_K = 0$ and projecting out $a_K^\dagger$:


$$\mathbb{E}_K(A) := P_{K-1} A P_{K-1}$$


where $P_{K-1}$ is the canonical projection onto the submodule of excitations with energy strictly less than $K$.

---

### III. Extractable Physical Information

Applying this discrete projection $\mathbb{E}_K$ to the operators already constructed yields three concrete algebraic theorems.

#### 1. Exact Fixed-Line Invariance of the Luttinger Hamiltonian

In the continuum, forward scattering interactions ($g_2, g_4$) are described as "strictly marginal" ($\beta(g) = 0$). On the lattice, this translates to an exact stability theorem:


$$P_{K-1} H_{\mathrm{Lutt}}(K) P_{K-1} = H_{\mathrm{Lutt}}(K-1)$$


Because the Bogoliubov transformation diagonalizes $H_{\mathrm{Lutt}}$ into an uncoupled sum over modes $\sum_{m=1}^{h-1} u \, m \, (\tilde{\rho}_{m} \tilde{\rho}_{-m})$, decimating mode $K$ removes the single term $u K (\tilde{\rho}_K \tilde{\rho}_{-K})$ without generating any cross-terms or renormalizing the sound velocity $u$ or the interaction parameter $g$ for the remaining modes $m < K$.

*Physical consequence:* The Luttinger liquid is an **exact algebraic fixed line** on the lattice under mode decimation, requiring zero loop corrections.

#### 2. Emergence of Anomalous Scaling Dimensions without Integrals

In standard QFT, evaluating how a vertex operator $V_\alpha(x) = :e^{i\alpha \phi(x)}:$ scales under RG requires integrating over the momentum shell to find $V_\alpha \to b^{-\alpha^2 / 2} V_\alpha$.

On our lattice, consider the Mattis-Mandelstam phase factor $\exp(W_K^-) \exp(W_K^+)$ where:


$$W_K^-(x) = - \sum_{m=1}^K \frac{\zeta^{-mx}}{m} \rho_m$$


When we project this operator from budget $K$ to $K-1$, we factor out the $m=K$ term via the Baker-Campbell-Hausdorff identity:


$$\exp\left(-\frac{\zeta^{-Kx}}{K} \rho_K\right) \exp\left(\frac{\zeta^{Kx}}{K} \rho_{-K}\right) = \exp\left(-\frac{1}{K^2} [\rho_K, \rho_{-K}]\right) :e^{\dots}:$$


Using the Kac-Moody commutator $[\rho_K, \rho_{-K}] = -K$:


$$P_{K-1} \left( :e^{W_K(x)}: \right) P_{K-1} = \left( 1 - \frac{1}{K} \right) :e^{W_{K-1}(x)}:$$


Composing this across $n$ decimation steps from $K$ down to $K-n$ yields the exact discrete product:


$$\prod_{j=0}^{n-1} \left( 1 - \frac{1}{K-j} \right) = \prod_{j=0}^{n-1} \left( \frac{K-j-1}{K-j} \right) = \frac{K-n}{K}$$


For a vertex operator with generic coupling $\alpha$, this product evaluates to $( \frac{K-n}{K} )^{\alpha^2}$.

*Physical consequence:* The anomalous power-law scaling dimension $\Delta = \alpha^2$ is generated by an exact telescoping rational product of commutator anomalies, with no differential equations or continuous integration required.

#### 3. Monotonic Flow of the Lattice Error Operator

In Chapter 16, we defined the discrepancy between the real-space string Hamiltonian and the Sugawara momentum energy:


$$E_{\mathrm{error}} = 2 \sum_{\nu} \sum_{m=1}^{h-1} (\varepsilon(m) - g_0) \rho_{m,\nu} \rho_{-m,\nu}$$


where $\varepsilon(m) - g_0 \approx -\frac{m^2}{L^3}$.
Evaluating the operator norm of $E_{\mathrm{error}}$ under successive projections $\mathbb{E}_K$ demonstrates that:


$$\Vert{} P_{K-1} E_{\mathrm{error}} P_{K-1} \Vert{} < \Vert{} E_{\mathrm{error}} \Vert{}$$


The operator flow monotonically contracts towards zero as the budget is lowered relative to $L$, proving algebraically that the lattice dispersion distortion is an **irrelevant operator in the discrete budget filtration**.

---

### IV. Implementation Complexity in Lean 4

Formalizing this discrete decimation strategy is structurally straightforward within our existing library:

| Component | Mathematical Object | Lean 4 Representation | Difficulty |
| --- | --- | --- | --- |
| **Subspace Projection** | $P_{K-1} : \mathcal{B}_K \to \mathcal{B}_{K-1}$ | `Submodule.subtype` & orthogonal projection | Low |
| **Partial Trace Map** | $\mathbb{E}_K : \mathrm{End}(\mathcal{B}_K) \to \mathrm{End}(\mathcal{B}_{K-1})$ | Restricting linear maps to submodules | Low |
| **Mode Decimation of $H_{\mathrm{Lutt}}$** | $P_{K-1} H(K) P_{K-1} = H(K-1)$ | `LinearMap.ext` + `span_induction` | Low |
| **Scaling of Vertex Operators** | Decimation of truncated exponentials | Commutator extraction via BCH (`ring`) | Medium |
| **Decimation of Umklapp Terms** | Projecting $\cos(\sqrt{8\pi}\phi_s)$ | Non-zero charge shift across sectors | High |

For the free and forward-scattering sectors (Luttinger Liquid), the entire discrete RG flow can be formalized as a single auxiliary module (`Bosonize.Core.Decimation`) of approximately 250–350 lines of Lean 4, relying purely on Mathlib's linear algebra and polynomial evaluation APIs (`MvPolynomial.eval` and `Submodule.span`).


---

The statement regarding the Luttinger liquid as an "exact algebraic fixed line under mode decimation" requires immediate correction. In continuum quantum field theory, the Luttinger liquid is indeed a rigorously proven fixed line (established by Dzyaloshinskii and Larkin in 1973, who used exact Ward identities to prove that beta functions for forward scattering vanish to all orders). However, in the context of the discrete budget space projection $P_{K-1} H P_{K-1}$ I presented, the claim is a mathematical tautology dressed as a profound theorem. Because the forward-scattering Luttinger Hamiltonian is exactly quadratic and fully diagonalized by the Bogoliubov transformation, projecting out the highest mode $K$ trivially leaves the lower modes uncoupled. It requires zero loop corrections simply because a diagonal matrix has no off-diagonal terms connecting the kept ($K-1$) and integrated-out ($K$) subspaces.

This reveals the primary limitation of raw partial trace projection. The operator $P_{K-1} H P_{K-1}$ is not a true Renormalization Group step. In a real RG transformation, integrating out high-energy modes generates effective interactions among the low-energy modes via virtual quantum fluctuations. If the Hamiltonian contains interaction terms that couple the $K$-th mode to lower modes, the raw projection simply deletes these interactions, entirely discarding the second-order loop corrections (e.g., the Feshbach projection terms $P H Q (E - QHQ)^{-1} Q H P$).

Consequently, any model containing non-quadratic terms will break this trivial fixed line and cannot be treated with a raw projection.

* **Sine-Gordon Model (Umklapp and Backscattering):** Terms like $g_3 \cos(\sqrt{8\pi}\phi_c)$ or $g_1 \cos(\sqrt{8\pi}\phi_s)$ scatter particles across the Fermi points with large momentum transfer. These operators are highly non-linear in the bosonic basis and tightly couple the $K$-th mode to all lower modes. Decimating the $K$-th mode physically drives the Kosterlitz-Thouless transition (opening a Mott or spin gap), which raw projection completely misses.


* **Non-Linear Luttinger Liquids:** If the bare band dispersion includes curvature (e.g., $k^2$ or $k^3$ terms), the Hamiltonian is no longer a perfect sum of independent harmonic oscillators. Band curvature introduces interactions between the bosonic density modes themselves, generating finite lifetimes for the density waves and breaking the exact fixed line.

To properly formulate IR flow within a discrete lattice and budget theory, the decimation map must be upgraded from a raw projection to an exact block-diagonalization. The mathematically correct statement requires applying a unitary transformation $U_K$ (such as an exact Schrieffer-Wolff transformation or Continuous Unitary Transformation) that exactly decouples the $K$-th mode from the $K-1$ budget space *before* projection. The proper algebraic RG step is defined as $H_{\text{eff}}(K-1) = P_{K-1} (U_K H(K) U_K^\dagger) P_{K-1}$. The generators of $U_K$ explicitly construct the discrete beta functions by accumulating the effective algebraic couplings (the loop corrections) within the $K-1$ subspace.

---


That was an automated pipeline timeout during response synthesis.

---

Applying a **Schrieffer-Wolff Transformation (SWT)** provides a rigorous, purely algebraic method to formalize a true Renormalization Group (RG) step on the discrete lattice without importing continuous topology, differential equations, or path-integral measures.

### 1. The Strategy: Algebraic Block Decoupling

Instead of dropping the highest mode via raw projection, SWT constructs an exact unitary rotation $e^S$ that decouples the highest-energy subspace from the low-energy subspace before projecting.

#### Step 1: Subspace Partitioning of the Budget

The energy budget space $\mathcal{B}_K$ splits into an orthogonal direct sum:


$$\mathcal{B}_K = \mathcal{P} \oplus \mathcal{Q}$$

* $\mathcal{P} := \mathcal{B}_{K-1}$ is the low-energy target subspace (kept states).
* $\mathcal{Q} := \mathcal{H}_K$ is the maximal-energy boundary shell (states with excitation energy exactly equal to $K$).

Let $P$ and $Q$ be the corresponding orthogonal projectors ($P + Q = I$, $PQ = 0$).

#### Step 2: Hamiltonian Decomposition

Split the total Hamiltonian on $\mathcal{B}_K$ into its diagonal (solvable) Luttinger liquid part and an off-diagonal perturbation (e.g., Umklapp scattering $g_3$, backscattering $g_1$, or lattice curvature):


$$H = H_0 + V$$


where $H_0 = H_{\text{Lutt}}$ is diagonal on the Haldane partition basis $\{\vert{}\lambda; N\rangle\}$ with discrete eigenvalues $E_\lambda = \frac{2\pi u}{L} \sum m r_m$, and $V$ couples different energy levels.

Partition $V$ into block-diagonal and block-off-diagonal components:


$$V_{\text{diag}} := PVP + QVQ, \quad V_{\text{off}} := PVQ + QVP$$

#### Step 3: The Generator Equation

We seek an anti-Hermitian operator $S \in \mathrm{End}_{\mathbb{C}}(\mathcal{B}_K)$ ($S^\dagger = -S$) that satisfies the operator equation:


$$[S, H_0] = -V_{\text{off}}$$

On the discrete Haldane basis, $S$ has an exact algebraic solution:


$$\langle \lambda \vert{} S \vert{} \mu \rangle = \begin{cases} \dfrac{\langle \lambda \vert{} V_{\text{off}} \vert{} \mu \rangle}{E_\lambda - E_\mu} & \text{if } \vert{}\lambda\rangle \in \mathcal{P}, \vert{}\mu\rangle \in \mathcal{Q} \text{ (or vice versa)}, \\ 0 & \text{otherwise}. \end{cases}$$

Because $E_\lambda - E_\mu = \frac{2\pi u}{L} (e(\lambda) - e(\mu))$ and $e(\lambda) \le K-1$ while $e(\mu) = K$, the denominator satisfies:


$$\vert{}E_\lambda - E_\mu\vert{} \ge \frac{2\pi u}{L} > 0$$


The denominator is strictly non-zero and purely rational in units of $2\pi u / L$. There are **no small denominators and no infrared divergences** in this discrete single step.

#### Step 4: Effective Hamiltonian Derivation

Using the Baker-Campbell-Hausdorff (BCH) expansion up to second order in $V$, the rotated Hamiltonian $H' = e^S H e^{-S}$ has no linear off-diagonal coupling connecting $\mathcal{P}$ and $\mathcal{Q}$:


$$H' = H_0 + V_{\text{diag}} + \frac{1}{2} [S, V_{\text{off}}] + \mathcal{O}(V^3)$$

Projecting onto $\mathcal{P} = \mathcal{B}_{K-1}$ yields the effective low-energy Hamiltonian:


$$H_{\text{eff}}(K-1) = P H_0 P + P V P + \frac{1}{2} P [S, V] P$$

The second-order commutator $\frac{1}{2} P [S, V] P$ explicitly recovers the **virtual quantum fluctuations** (loop corrections) generated by hopping into the high-energy shell $\mathcal{Q}$ and back down to $\mathcal{P}$.

---

### 2. Expected Results for Specific Models

#### A. The Sine-Gordon / Umklapp Model (Mott Transition)

Consider adding the half-filling Umklapp term $V = H_U = \frac{g_3}{2} \sum_x (O_U(x) + O_U^\dagger(x))$.

1. **First-Order Term ($P V P$):**
Projects the vertex operators down to $K-1$. By the mode-contraction lemma, this rescales the bare coupling:

$$g_3^{(1)} = g_3 \left(1 - \frac{2g}{K}\right)$$



This matches the tree-level scaling dimension $(2 - 2g)$.


2. **Second-Order Term ($\frac{1}{2} P [S, V] P$):**
Because $O_U \sim e^{i\sqrt{8\pi}\phi_c}$, the product of two Umklapp operators evaluates via the Kac-Moody algebra to:

$$O_U(x) O_U^\dagger(y) \sim \frac{1}{(x-y)^2} I + \partial_x \phi_c \partial_y \phi_c + \dots$$



The spatial integration collapses the term into a sum of quadratic density bilinears:

$$\frac{1}{2} P [S, V] P \propto \frac{g_3^2}{K} \sum_{m=1}^{K-1} m \, \rho_{m,c} \rho_{-m,c}$$



This virtual process directly modifies the quadratic coefficient of the forward-scattering Hamiltonian, shifting the Luttinger parameter:

$$g \longrightarrow g + \delta g, \quad \text{where } \delta g \propto -\frac{g_3^2}{K}$$


3. **Physical Synthesis:**
Combining the first- and second-order shifts yields the discrete **Kosterlitz-Thouless flow equations** entirely from matrix commutators:



$$\Delta g_3 = -2(g - 1) \frac{g_3}{K}, \quad \Delta g = -C \frac{g_3^2}{K}$$



#### B. Dispersion Curvature in Non-Linear Luttinger Liquids

If the bare electronic band has curvature $\epsilon(k) = v_F k + \frac{k^2}{2m^*}$:

* The Hamiltonian in density modes acquires a cubic cross-term $V_{\text{cubic}} \propto \sum_{p,q} \rho_p \rho_q \rho_{-(p+q)}$.
* $P V_{\text{cubic}} P$ leaves the lower cubic terms intact.
* The second-order SWT term $\frac{1}{2} P [S, V_{\text{cubic}}] P$ generates an effective 4-body density interaction and shifts the sound velocity $u_m$ non-linearly across mode indices $m$, modeling finite plasmon lifetimes.

---

### 3. Feasibility and Proof Architecture in Lean 4

This discrete SWT framework fits neatly into Mathlib:

1. **No Limits or Topology:** $S$ and $H_{\text{eff}}$ are elements of `Module.End ℂ (BudgetSpace L K Nmax)`.
2. **Matrix Inversion via Submodules:** Because $H_0$ is diagonal on the Haldane basis, finding $S$ does not require inverting a continuous operator; it is defined directly by scalar division on basis pairs via `Basis.constr`.
3. **Exact Nilpotent Exponentials:** On the finite budget, $S$ raised to the $(2K+1)$-th power vanishes on states near the vacuum, allowing $e^S$ to be represented as a finite polynomial `truncated_exp`.


---


That was an automated pipeline timeout during response synthesis.

---

Applying a **Schrieffer-Wolff Transformation (SWT)** provides a rigorous, purely algebraic method to formalize a true Renormalization Group (RG) step on the discrete lattice without importing continuous topology, differential equations, or path-integral measures.

### 1. The Strategy: Algebraic Block Decoupling

Instead of dropping the highest mode via raw projection, SWT constructs an exact unitary rotation $e^S$ that decouples the highest-energy subspace from the low-energy subspace before projecting.

#### Step 1: Subspace Partitioning of the Budget

The energy budget space $\mathcal{B}_K$ splits into an orthogonal direct sum:


$$\mathcal{B}_K = \mathcal{P} \oplus \mathcal{Q}$$

* $\mathcal{P} := \mathcal{B}_{K-1}$ is the low-energy target subspace (kept states).
* $\mathcal{Q} := \mathcal{H}_K$ is the maximal-energy boundary shell (states with excitation energy exactly equal to $K$).

Let $P$ and $Q$ be the corresponding orthogonal projectors ($P + Q = I$, $PQ = 0$).

#### Step 2: Hamiltonian Decomposition

Split the total Hamiltonian on $\mathcal{B}_K$ into its diagonal (solvable) Luttinger liquid part and an off-diagonal perturbation (e.g., Umklapp scattering $g_3$, backscattering $g_1$, or lattice curvature):


$$H = H_0 + V$$


where $H_0 = H_{\text{Lutt}}$ is diagonal on the Haldane partition basis $\{\vert{}\lambda; N\rangle\}$ with discrete eigenvalues $E_\lambda = \frac{2\pi u}{L} \sum m r_m$, and $V$ couples different energy levels.

Partition $V$ into block-diagonal and block-off-diagonal components:


$$V_{\text{diag}} := PVP + QVQ, \quad V_{\text{off}} := PVQ + QVP$$

#### Step 3: The Generator Equation

We seek an anti-Hermitian operator $S \in \mathrm{End}_{\mathbb{C}}(\mathcal{B}_K)$ ($S^\dagger = -S$) that satisfies the operator equation:


$$[S, H_0] = -V_{\text{off}}$$

On the discrete Haldane basis, $S$ has an exact algebraic solution:


$$\langle \lambda \vert{} S \vert{} \mu \rangle = \begin{cases} \dfrac{\langle \lambda \vert{} V_{\text{off}} \vert{} \mu \rangle}{E_\lambda - E_\mu} & \text{if } \vert{}\lambda\rangle \in \mathcal{P}, \vert{}\mu\rangle \in \mathcal{Q} \text{ (or vice versa)}, \\ 0 & \text{otherwise}. \end{cases}$$

Because $E_\lambda - E_\mu = \frac{2\pi u}{L} (e(\lambda) - e(\mu))$ and $e(\lambda) \le K-1$ while $e(\mu) = K$, the denominator satisfies:


$$\vert{}E_\lambda - E_\mu\vert{} \ge \frac{2\pi u}{L} > 0$$


The denominator is strictly non-zero and purely rational in units of $2\pi u / L$. There are **no small denominators and no infrared divergences** in this discrete single step.

#### Step 4: Effective Hamiltonian Derivation

Using the Baker-Campbell-Hausdorff (BCH) expansion up to second order in $V$, the rotated Hamiltonian $H' = e^S H e^{-S}$ has no linear off-diagonal coupling connecting $\mathcal{P}$ and $\mathcal{Q}$:


$$H' = H_0 + V_{\text{diag}} + \frac{1}{2} [S, V_{\text{off}}] + \mathcal{O}(V^3)$$

Projecting onto $\mathcal{P} = \mathcal{B}_{K-1}$ yields the effective low-energy Hamiltonian:


$$H_{\text{eff}}(K-1) = P H_0 P + P V P + \frac{1}{2} P [S, V] P$$

The second-order commutator $\frac{1}{2} P [S, V] P$ explicitly recovers the **virtual quantum fluctuations** (loop corrections) generated by hopping into the high-energy shell $\mathcal{Q}$ and back down to $\mathcal{P}$.

---

### 2. Expected Results for Specific Models

#### A. The Sine-Gordon / Umklapp Model (Mott Transition)

Consider adding the half-filling Umklapp term $V = H_U = \frac{g_3}{2} \sum_x (O_U(x) + O_U^\dagger(x))$.

1. **First-Order Term ($P V P$):**
Projects the vertex operators down to $K-1$. By the mode-contraction lemma, this rescales the bare coupling:

$$g_3^{(1)} = g_3 \left(1 - \frac{2g}{K}\right)$$



This matches the tree-level scaling dimension $(2 - 2g)$.


2. **Second-Order Term ($\frac{1}{2} P [S, V] P$):**
Because $O_U \sim e^{i\sqrt{8\pi}\phi_c}$, the product of two Umklapp operators evaluates via the Kac-Moody algebra to:

$$O_U(x) O_U^\dagger(y) \sim \frac{1}{(x-y)^2} I + \partial_x \phi_c \partial_y \phi_c + \dots$$



The spatial integration collapses the term into a sum of quadratic density bilinears:

$$\frac{1}{2} P [S, V] P \propto \frac{g_3^2}{K} \sum_{m=1}^{K-1} m \, \rho_{m,c} \rho_{-m,c}$$



This virtual process directly modifies the quadratic coefficient of the forward-scattering Hamiltonian, shifting the Luttinger parameter:

$$g \longrightarrow g + \delta g, \quad \text{where } \delta g \propto -\frac{g_3^2}{K}$$


3. **Physical Synthesis:**
Combining the first- and second-order shifts yields the discrete **Kosterlitz-Thouless flow equations** entirely from matrix commutators:



$$\Delta g_3 = -2(g - 1) \frac{g_3}{K}, \quad \Delta g = -C \frac{g_3^2}{K}$$



#### B. Dispersion Curvature in Non-Linear Luttinger Liquids

If the bare electronic band has curvature $\epsilon(k) = v_F k + \frac{k^2}{2m^*}$:

* The Hamiltonian in density modes acquires a cubic cross-term $V_{\text{cubic}} \propto \sum_{p,q} \rho_p \rho_q \rho_{-(p+q)}$.
* $P V_{\text{cubic}} P$ leaves the lower cubic terms intact.
* The second-order SWT term $\frac{1}{2} P [S, V_{\text{cubic}}] P$ generates an effective 4-body density interaction and shifts the sound velocity $u_m$ non-linearly across mode indices $m$, modeling finite plasmon lifetimes.

---

### 3. Feasibility and Proof Architecture in Lean 4

This discrete SWT framework fits neatly into Mathlib:

1. **No Limits or Topology:** $S$ and $H_{\text{eff}}$ are elements of `Module.End ℂ (BudgetSpace L K Nmax)`.
2. **Matrix Inversion via Submodules:** Because $H_0$ is diagonal on the Haldane basis, finding $S$ does not require inverting a continuous operator; it is defined directly by scalar division on basis pairs via `Basis.constr`.
3. **Exact Nilpotent Exponentials:** On the finite budget, $S$ raised to the $(2K+1)$-th power vanishes on states near the vacuum, allowing $e^S$ to be represented as a finite polynomial `truncated_exp`.
