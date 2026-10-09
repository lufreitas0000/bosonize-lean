# BOSONIZE-LEAN: Master Table of Contents

This document serves as the structural roadmap and index for the `Bosonize-Lean` mathematical reference notes. It outlines the formalization of 1+1D lattice bosonization. The formal architecture distinguishes between three levels of mathematical statements:
1. **Proposed Finite Targets:** Intended algebraic identities on specified finite budget/CAR carriers. Only Chapters 1–2 currently have proved and frozen Core implementations; later descriptions below name intended results, not completed Lean proofs.
2. **Specified Algebraic Targets:** Weighted polynomial CCR state construction, charge tensor algebra, coefficientwise Weyl-type vertices, and explicit generator duality. The notes specify their constructions and proof obligations; these are future Lean targets, with no analytic parameter evaluation or automatic finite-CAR realization.
3. **Conditional Criteria & Physical Context:** Budget leakage requires a nonzero outside component. Continuum KT scaling and thermodynamic Mott gaps remain physical context requiring separate asymptotic constructions. See the [completion ledger](../../note/notes_review_completion_2026-10-09.md) for resolved revisions, scope exclusions and next-phase readiness; the [adaptive roadmap](../../adaptative_roadmap.md) controls cross-chapter discoveries.

---

## Part I: Foundations & Kinematics

### Chapter 1: Lattice and Band Geometry
**Description:** Defines the fundamental discrete spatial lattice and its Fourier-dual momentum band, establishing the strictly finite nature of the system with an even-length convention ($L = 2h$, $h > 0$).
*   **Main Definitions:** Spatial Lattice ($\Lambda$), Momentum Band ($\Lambda^*$), Projections and Band Arithmetic ($\oplus, \ominus$).
*   **Main Lemmas:** Band Properties (Cardinality, Bijection, Wrap Lemma, Positive Nyquist Mode).

### Chapter 2: Umbral Calculus Core
**Description:** Establishes the discrete calculus framework over rings, replacing continuous derivatives with exact finite differences ($\Delta, \nabla$) and polynomial forward difference $\Delta_{\mathrm{poly}}$.
*   **Main Definitions:** Umbral Operators (Shift $E$, Differences $\Delta, \nabla, \Delta_{\mathrm{poly}}$), Umbral Map ($\Phi$), Position Multiplier ($\beta$).
*   **Main Lemmas:** Discrete Leibniz Rule, Summation by Parts, Newton Expansion, Umbral Commutation (Heisenberg Pair), Finite-Dimensional No-Go Theorem on Non-Zero Carriers.

### Chapter 3: Finite Fourier Transform
**Description:** Implements the discrete Fourier transform using algebraic primitive roots of unity, guaranteeing exact unitary maps between position and momentum with representative-independent characters $\chi(k,x)$.
*   **Main Definitions:** Representative-Independent Characters ($\chi(k, x)$), Discrete Fourier Transform (DFT), Transported Band Operations.
*   **Main Lemmas:** Diagonalization of Difference Operators, Orthogonality, Unitarity.

### Chapter 4: CAR Representation and Fock Space
**Description:** Constructs the generic finite-dimensional fermionic Hilbert space and the Canonical Anticommutation Relation (CAR) operators on finite-dimensional Euclidean space $V$ with adjoint compatibility $c_i^\dagger = (c_i)^\dagger$.
*   **Main Definitions:** CAR Representation with Adjoint Compatibility, Fock Space ($\mathcal{F}$), Fermionic Sign Function ($\sigma$), Local/Total Observables ($n_i, \hat{N}, \Gamma$).
*   **Main Lemmas:** Dimension of Fock Space, Atomic Sign Lemma, Pure-CAR Commutator Identities, Hop Action.

### Chapter 5: Position and Momentum Fermions
**Description:** Instantiates the CAR operators over the dual momentum band ($L = 2h$) and derives spatial fermions via the exact DFT, avoiding separate Jordan-Wigner strings.
*   **Main Definitions:** Position Fermions ($c_x, c_x^\dagger$), Linearized Free Hamiltonian ($H_0$), Half-Filled Sea Configuration.
*   **Main Lemmas:** Position CAR, Inverse Fourier Transform, Invariance of Total Particle Number, Spectrum of $H_0$.

### Chapter 6: The Lattice AQFT Net
**Description:** Constructs local observable algebras directly from position fermions, proving Algebraic Quantum Field Theory (AQFT) postulates as constructive theorems.
*   **Main Definitions:** Local Algebras ($\mathfrak{A}(I)$), Parity Automorphism ($\alpha$), Even Subalgebra ($\mathfrak{A}_+(I)$), Odd Subspace.
*   **Main Lemmas:** Isotony & Additivity, Twisted Locality, Global Algebra Irreducibility, Equality $\mathfrak{A}_+(\emptyset) = \mathfrak{A}(\emptyset)$.

### Chapter 7: Vacuum, Sectors, Energy, Budget
**Description:** Introduces the "Energy Budget" regularization scheme. Truncates the state space based on excitation energy within admissible charge sectors $-h \le N \le h$, cleanly preventing mathematical divergences.
*   **Main Definitions:** Dirac Sea Vacuum ($\vert\Omega\rangle$), Admissible Charge Sectors ($-h \le N \le h$), Normal Ordering, Sector Ground Configurations ($S_N = \{k \le N\}$) and Ground States ($\vert N \rangle_0$), Diagonal Observables ($\hat{E}, \hat{N}$), Energy Budget Subspace ($B(N, K) = \bigoplus_{E=0}^K H(N, E)$), Cutoff Projections ($P_{N,K}, P_{K,N_{\max}}$).
*   **Main Lemmas:** Unique Ground Configuration, Rank Formula (Sorted Indexing $s_i, g_i = -h+1+i$), Preserved Sector Charge Shifts, Unified Margin Excursions ($2M + K + K_{\text{excursion}} + N_{\max} \le h$).

### Chapter 8: The Umbral Boson Fock Layer
**Description:** Constructs the target bosonic Hilbert space purely algebraically using multivariate polynomials with the Haldane inner product, avoiding unbounded operators and trace paradoxes.
*   **Main Definitions:** Bosonic Carrier Space ($\mathcal{F}_b = \mathbb{C}[X]$), Raw Currents ($C_m = X_m, A_m = m D_m, A_m^\dagger = C_m$), Bosonic Observables ($\hat{N}_b = \sum \frac{1}{m} C_m A_m, \hat{H}_b = \sum C_m A_m$), Weight Filtration ($\mathcal{F}_{\le K}$).
*   **Main Lemmas:** Exact CCR ($[A_m, C_n] = m \delta_{mn} I$), Nilpotent Truncated Exponentials ($\operatorname{expNil}$), Exact Formal BCH, Polynomial Vacuum Recurrence ($P_{n+1} = X P_n + n P_{n-1}$ generating $\exp(Xt+t^2/2)$).

---

## Part II: The Density Sector & Completeness

### Chapter 9: Density Modes and Kinematics
**Description:** Bridges the fermionic and bosonic spaces by defining exact, non-wrapping momentum-shift operators (densities) and proving their action strictly raises excitation energy within admissible sectors.
*   **Main Definitions:** Truncated Raw Density, Normal Ordered Density ($:\!\rho_m\!:$).
*   **Main Lemmas:** Finiteness and Linear Independence, Covariance with Particle Number and Energy, Budget Grading, Non-vacuous Action in Admissible Sectors.

### Chapter 10: Heisenberg Algebra and the Exact Schwinger Term
**Description:** Proves the core algebraic theorem of bosonization: fermionic density modes satisfy the U(1) Kac-Moody algebra on the budget subspace under explicit margin hypotheses ($2M + K + |N| \le h$).
*   **Main Definitions:** Top and Bottom Edge Domains, Boundary Commutator Operators.
*   **Main Lemmas:** Exact Diagonal Edge Formula, Regime M1 (Diagonal Buffer Zone), Regime M2 (Off-Diagonal Suppression), Kac-Moody Commutator with Unified Excursion Hypotheses.

### Chapter 11: Haldane Completeness
**Description:** Demonstrates that the low-energy fermionic Hilbert space is entirely and exactly spanned by bosonic partition states, matching integer partition counts, and assembles the whole budget basis for $B(N,K)$.
*   **Main Definitions:** Bosonic Partition States ($|\lambda; N\rangle$), Fixed-Energy Subspaces ($H(N, E)$), Whole Budget Basis ($\mathcal{B}_{\text{basis}}(N, K) = \bigcup_{E=0}^K \{|\lambda; N\rangle \mid \lambda \vdash E\}$).
*   **Main Lemmas:** Regime R1 (Unbounded Partition Counting), Word-Prefix Energy Bound from Partition Energy, Regime R2 (Hall-Gram Positive Definiteness), Haldane Completeness on Whole Budget.

### Chapter 12: Algebraic Equivalence of Energy Observables (Sugawara)
**Description:** Proves that the fermionic kinetic energy operator is algebraically identical to the bosonic Sugawara Hamiltonian ($H_{\text{sug}}^{(M)} = \sum \rho_m \rho_{-m}$) on the whole budget $B(N,K)$.
*   **Main Definitions:** Bosonic Sugawara Hamiltonian ($H_{\text{sug}}^{(M)}$), Mode Cutoff $M \ge K$.
*   **Main Lemmas:** Sugawara Energy-Basis Evaluation on Partitions, Sugawara Equivalence on Whole Budget $B(N,K)$, Shifted-Output Commutators.

---

## Part III: The Bosonization Dictionary

### Chapter 13: Klein Factors & Multi-Species Fermions
**Description:** Introduces chirality branches ($R, L$) and sector isometries $F_{\nu,\vec{N},K}$ with explicit ground-ket phases to intertwine density modes across a four-budget commuting square.
*   **Main Definitions:** Multi-Species Admissible Sectors, Sector Isometries ($F_{\nu,\vec{N},K}$), Explicit Ground Phase $P(\nu, \vec{N}) = (-1)^{\sum_{\eta < \nu}(h+N_\eta) + (h+N_\nu-1)}$.
*   **Main Lemmas:** Four-Budget Commuting Square for Density Intertwining, Cross-Species Anticommutation under Joint Admissibility.

### Chapter 14: The Projected Mattis-Mandelstam Formula
**Description:** Defines a typed finite candidate using nilpotent phases and source zero-mode order, and a valid conditional cyclic-span criterion with common residuals. Numerical-margin-only field equality remains a research candidate excluded from an unconditional interface.
*   **Main Definitions:** Projected Bosonized Fermion Operator ($P_{\text{target}} \psi_\nu(x) P_{\text{source}}$), Typed Phase Exponentials ($\operatorname{expNil}(W^\pm)$), Adjoint Order ($Z^\dagger F^\dagger \operatorname{expNil}(-W^-) \operatorname{expNil}(-W^+)$).
*   **Main Lemmas:** Full Retained Fourier-Hole Ground Expansion, Conditional Cyclic-Span Equality with Typed Common Residuals, Ground-to-Ground CAR Phase Check.

---

## Part IV: Dual Fields & Lattice Hamiltonians

### Chapter 15: Dual Fields ($\phi$ and $\theta$)
**Description:** Defines Hermitian phase and density fields with chirality orientation $\eta \in \{+1, -1\}$ and independent cutoff $M$ ($2M < L$), evaluating exact Umbral gradients and commutators on budget vectors.
*   **Main Definitions:** Chiral Fields ($\varphi_\eta(x)$), Dual Fields ($\phi(x) = \varphi_R + \varphi_L, \theta(x) = \varphi_R - \varphi_L$), Independent Cutoff $M$ with No-Aliasing ($2M < L$).
*   **Main Lemmas:** Exact Umbral Difference of Chiral Fields, Budget Action Commutator Cancellation, Delta Obstruction Scope ($M < L$).

### Chapter 16: The Field-Theoretic Hamiltonian and Lattice Error
**Description:** Evaluates the spatial collapse of normal-ordered squared Umbral gradients into weighted dispersion $\varepsilon(m)$, defines total Sugawara $H_{\text{sug}}^{(M)}$, and characterizes the error operator kernel and excited witnesses.
*   **Main Definitions:** Discrete Field Hamiltonian ($H_{\text{field}}^{(M)}$), Lattice Dispersion Weight ($\varepsilon(m)$), Total Two-Branch Sugawara Hamiltonian ($H_{\text{sug}}^{(M)}$), Field Error Operator ($E_{\text{error}}^{(M)}$).
*   **Main Lemmas:** Exact Spatial Collapse via DFT, Weighted Lattice Energy Theorem, Annihilation of States in $\ker(\varepsilon - g_0)$, Non-Zero Excited Witness at Mode $m \ge 2$, Separate Physical Status for Continuum/RG Heuristics.

---

## Part V: Interactions & Luttinger Liquid Models

### Chapter 17: Forward Scattering & The Luttinger Hamiltonian
**Description:** Separates raw opposite-transfer hopping from the chosen pairing model and defines its intra-branch current interaction directly. Full sea-Wick ordering gives the exact finite one-body correction Q_M between raw and current interactions. Retains explicit chemical potential and energy-shell SW coefficient identities.
*   **Main Definitions:** Raw Transfer Interactions, Chosen Current/Pairing Hamiltonian, Full Sea-Wick Word Ordering and Q_M Correction, Zero-Mode Shifts.
*   **Main Lemmas:** Exact Reduction of Forward Scattering, Bosonized Luttinger Hamiltonian ($H_{\text{Lutt}}$), Energy-Shell Schrieffer-Wolff Decomposition Modulo $t^3$.

### Chapter 18: The Bogoliubov Transformation
**Description:** Diagonalizes the pairing Hamiltonian on budget vectors, bundles parameters into `LuttingerParams` ($u, c, s, g, g^{-1}$), reconciles the $\frac{2\pi}{L} 2us^2 \sum m I$ vacuum shift, and clarifies finite-vacuum vs CCR-vacuum semantics.
*   **Main Definitions:** Bogoliubov Transformation on Raw Currents, Parameter Record `LuttingerParams` ($u, c, s, g = (c-s)^2, g^{-1} = (c+s)^2$), Vacuum Energy Shift ($\Delta E_{\text{vac}}$).
*   **Main Lemmas:** Kac-Moody Preservation on Budget, Exact Diagonalization Theorem, Vacuum Obstruction in Nonvacuous Current-Action Regime, Energy-Shell SW Decomposition.

---

## Part VI: Observables, Correlators, Duality & Spin

### Chapter 19: Exact Correlation Functions
**Description:** Constructs the abstract quasi-free state from the weighted polynomial vacuum and inverse Bogoliubov pullback, separated from finite-Fock density matrices. Evaluates the ordered density kernel with both s² and c² contractions.
*   **Main Definitions:** Abstract Quasi-Free CCR State Functional ($\omega_{\tilde{\Omega}}$), Spatial Density Operator ($\rho_R(x)$), Parameter Relation $c^2 + s^2 = \frac{g + g^{-1}}{2}$.
*   **Main Lemmas:** Mode Contraction Theorems (Both $s^2$ and $c^2$ Contractions), Ordered Real-Space Correlator ($D_c(x,y)$), Symmetric vs Ordered Form.

### Chapter 20: Projected Order Parameters, Formal Vertex Correlators, and Model Duality
**Description:** Defines exact projected CDW/pairing products with residuals, coefficientwise Weyl-type vertices in the constructed charge/CCR model, and an explicit generator duality with adjoint/ζ^x transport. Analytic exponentials, finite-CAR correlator comparisons, and topological interpretation remain separate extensions.
*   **Main Definitions:** Projected Order Parameters ($P O_{CDW} P, P O_{SC} P$), Finite Logarithmic Kernel ($D_1(x,y)$), Parameterized Model Duality Map ($\mathcal{D}$).
*   **Main Targets:** Typed Products with Residuals, Constructed Polynomial/Charge State, Exact Formal Gaussian Correlators, Hamiltonian and Charge-Indexed State Transport.

### Chapter 21: Gaps & Spin-1/2 Generalizations
**Description:** Formalizes spin-charge separation on the parity-constrained sublattice ($Q_c \equiv Q_s \pmod 2$), constructs the spin-singlet Cooper pair with two distinct species-charge Klein factors ($K_1, K_2$), and formulates the conditional budget leakage criterion for Umklapp scattering.
*   **Main Definitions:** Raw Charge and Spin Currents ($R^c, R^s$), Parity Sublattice ($Q_c \equiv Q_s \pmod 2$), Spin-Singlet Cooper Pair with Dual Klein Factors ($K_1, K_2$), Umklapp Operator ($O_U(x)$).
*   **Main Lemmas:** Spin-Charge Commutativity on Frozen Margins, Single-Species Shift $\Delta \vec{N} = (+1, +1, -1, -1)$, Conditional Budget Leakage Criterion, Separate Physical Status for KT Flow and Mott Gap.
