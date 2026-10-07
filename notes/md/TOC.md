# BOSONIZE-LEAN: Master Table of Contents

This document serves as the structural roadmap and index for the `Bosonize-Lean` mathematical reference notes. It outlines the formalization of 1+1D lattice bosonization, ensuring all claims are exact identities on finite-dimensional or algebraic spaces without relying on analytical limits.

---

## Part I: Phase 1 Foundations

### Chapter 1: Lattice and Band Geometry
**Description:** Defines the fundamental discrete spatial manifold and its Fourier-dual momentum space, establishing the strictly finite nature of the system.
*   **Main Definitions:** Spatial Lattice ($\Lambda$), Momentum Band ($\Lambda^*$), Projections and Band Arithmetic ($\oplus, \ominus$).
*   **Main Lemmas:** Band Properties (Cardinality, Bijection, Wrap Lemma, Nyquist Mode).

### Chapter 2: Umbral Calculus Core
**Description:** Establishes the discrete calculus framework over rings, replacing continuous derivatives with exact finite differences to prevent topological paradoxes.
*   **Main Definitions:** Umbral Operators (Shift $E$, Differences $\Delta, \nabla$), Umbral Map ($\Phi$), Position Multiplier ($\beta$).
*   **Main Lemmas:** Discrete Leibniz Rule, Summation by Parts, Newton Expansion, Umbral Commutation (Heisenberg Pair), Finite-Dimensional No-Go Theorem.

### Chapter 3: Finite Fourier Transform
**Description:** Implements the discrete Fourier transform using algebraic primitive roots of unity, guaranteeing exact unitary maps between position and momentum.
*   **Main Definitions:** Primitive Root of Unity ($\zeta$), Plane Waves ($e_k$), Discrete Fourier Transform (DFT).
*   **Main Lemmas:** Diagonalization of Difference Operators, Orthogonality, Unitarity.

### Chapter 4: CAR Representation and Fock Space
**Description:** Constructs the generic finite-dimensional fermionic Hilbert space and the Canonical Anticommutation Relation (CAR) operators using exact sign-counting functions.
*   **Main Definitions:** CAR Representation, Fock Space ($\mathcal{F}$), Fermionic Sign Function ($\sigma$), Local/Total Observables ($n_i, \hat{N}, \Gamma$).
*   **Main Lemmas:** Dimension of Fock Space, Atomic Sign Lemma, Pure-CAR Commutator Identities, Hop Action.

### Chapter 5: Position and Momentum Fermions
**Description:** Instantiates the CAR operators over the dual momentum band and derives spatial fermions via the exact DFT, avoiding separate Jordan-Wigner strings.
*   **Main Definitions:** Position Fermions ($c_x, c_x^\dagger$), Linearized Free Hamiltonian ($H_0$).
*   **Main Lemmas:** Position CAR, Inverse Fourier Transform, Invariance of Total Particle Number, Spectrum of $H_0$.

### Chapter 6: The Lattice AQFT Net
**Description:** Constructs local observable algebras directly from position fermions, proving Algebraic Quantum Field Theory (AQFT) postulates as constructive theorems rather than assuming them as axioms.
*   **Main Definitions:** Local Algebras ($\mathfrak{A}(I)$), Parity Automorphism ($\alpha$), Even/Odd Grading.
*   **Main Lemmas:** Isotony & Additivity, Twisted Locality, Global Algebra Irreducibility.

### Chapter 7: Vacuum, Sectors, Energy, Budget
**Description:** Introduces the "Energy Budget" regularization scheme. Replaces the infinite Dirac sea by truncating the state space based on excitation energy, cleanly preventing mathematical divergences.
*   **Main Definitions:** Dirac Vacuum ($\vert\Omega\rangle$), Charge Sector ($N(S)$), Normal Ordering, Sector Ground States ($\vert N \rangle_0$), Excitation Energy ($e(S)$), Energy Budget Subspace ($\mathcal{B}_{K,N_{max}}$).
*   **Main Lemmas:** Vacuum Expectation, Rank Formula (Sorting Finsets), Frozen Margins.

### Chapter 8: The Umbral Boson Fock Layer
**Description:** Constructs the target bosonic Hilbert space purely algebraically using multivariate polynomials, avoiding unbounded operators and trace paradoxes.
*   **Main Definitions:** Bosonic Carrier Space ($\mathcal{F}_b = \mathbb{C}[X]$), Operators and Currents ($a, a^\dagger, J$), Bosonic Observables ($\hat{N}_b, H_b$), Weight Filtration ($\mathcal{F}_{\le K}$).
*   **Main Lemmas:** Exact CCR, Module Isomorphism of Euler Derivation, Exact BCH and Wick's Theorem, Truncated Nilpotency.

---

## Part II: Phase 2 The Density Sector

### Chapter 9: Density Modes and Kinematics
**Description:** Bridges the fermionic and bosonic spaces by defining exact, non-wrapping momentum-shift operators (densities) and proving their action strictly raises energy.
*   **Main Definitions:** Truncated Raw Density, Normal Ordered Density ($:\!\rho_m\!:$).
*   **Main Lemmas:** Finiteness and Linear Independence, Covariance with Particle Number and Energy, Budget Grading, Non-vacuous Action.

### Chapter 10: Heisenberg Algebra and the Exact Schwinger Term
**Description:** Proves the core miracle of bosonization: fermionic bilinears obey bosonic commutation relations. Identifies the quantum anomaly (Schwinger term) as an exact boundary effect on the finite lattice.
*   **Main Definitions:** (Conceptual) The Top and Bottom Edge Domains.
*   **Main Lemmas:** The Exact Diagonal Edge Formula, Regime M1 (The Diagonal Buffer Zone), Regime M2 (Off-Diagonal Suppression), U(1) Kac-Moody Algebra on the Budget.

### Chapter 11: Haldane Completeness
**Description:** Demonstrates that the low-energy fermionic Hilbert space is entirely and exactly spanned by bosonic density excitations, matching integer partition counts.
*   **Main Definitions:** Bosonic Partition States, Fixed-Energy Sector Subspace ($\mathcal{H}^N_K$).
*   **Main Lemmas:** Regime R1 (Unbounded Partition Counting), Regime R2 (Bosonic Orthogonality), Haldane Completeness Theorem.

### Chapter 12: Algebraic Equivalence of Energy Observables (Sugawara)
**Description:** Proves that the fermionic kinetic energy operator is algebraically identical to a quadratic sum of bosonic density modes without invoking time dynamics.
*   **Main Definitions:** Bosonic Sugawara Hamiltonian ($H_{sug}$).
*   **Main Lemmas:** Commutation with the Modes, Sugawara Equivalence on the Budget.

---

## Part III: Phase 3 The Bosonization Dictionary (Planned)

### Chapter 13: Klein Factors & Multi-Species Fermions
**Description:** Introduces chirality branches (Right/Left movers) and the Klein factors required to shift charge sectors and enforce anti-commutation across branches.
*   **Main Definitions:** Chiral Branches ($R, L$), Klein Factors ($F_R, F_L$).
*   **Main Lemmas:** Klein Anti-commutation, Ladder Operations on Sector Ground States.

### Chapter 14: The Mattis-Mandelstam Formula
**Description:** The complete dictionary mapping: constructing the physical fermionic annihilation operator $\psi(x)$ purely out of exponentiated bosonic density modes and Klein factors.
*   **Main Definitions:** The Bosonized Fermion Operator.
*   **Main Lemmas:** Exact Operator Equivalence on the Budget Subspace.

---

## Part IV: Phase 4 Free Dynamics & Dual Fields (Planned)

### Chapter 15: Dual Fields ($\phi$ and $\theta$)
**Description:** Defines the Hermitian phase and density scalar fields that represent the string displacement and momentum.
*   **Main Definitions:** Phase Field ($\theta$), Density Field ($\phi$).
*   **Main Lemmas:** Canonical Commutation Relations of Dual Fields.

### Chapter 16: Equivalence of Free Dynamics
**Description:** Rewrites the Sugawara Hamiltonian strictly in terms of the continuous dual field derivatives, establishing the massless free scalar field action.
*   **Main Definitions:** Field-Theoretic Hamiltonian.
*   **Main Lemmas:** Energy Evaluation of Dual Fields.

---

## Part V: Phase 5 Interactions & The Luttinger Liquid (Planned)

### Chapter 17: Forward Scattering & The Luttinger Hamiltonian
**Description:** Introduces $g_2$ and $g_4$ 4-fermion interactions (density-density scattering) and maps them exactly into quadratic bosonic operators.
*   **Main Definitions:** The Luttinger Interaction Hamiltonian ($H_{int}$).
*   **Main Lemmas:** Algebraic Reduction of Normal-Ordered 4-Fermion Terms.

### Chapter 18: The Bogoliubov Transformation
**Description:** Exactly diagonalizes the interacting bosonic Hamiltonian using an algebra isomorphism, yielding the renormalized velocity $u$ and the Luttinger parameter $g$.
*   **Main Definitions:** The Bogoliubov Transformation ($U_B$), Luttinger Parameters ($u, g$).
*   **Main Lemmas:** `AlgEquiv` Isomorphism of the Hamiltonian, Renormalized Spectrum.

---

## Part VI: Phase 6 Observables, Correlators & Duality (Planned)

### Chapter 19: Exact Correlation Functions
**Description:** Computes spatial and temporal correlations for physical observables purely algebraically over the budget space, showcasing non-Fermi-liquid behavior.
*   **Main Definitions:** Density Correlator ($D_c$), Charge Density Wave Correlator ($D_{CDW}$).
*   **Main Lemmas:** Exact Power-Law Decay on the Lattice.

### Chapter 20: The Duality Theorem
**Description:** Formalizes the striking 1D symmetry where flipping the interaction strength $g \leftrightarrow 1/g$ and exchanging fields $\phi \leftrightarrow \theta$ leaves the physics invariant.
*   **Main Definitions:** Duality Mapping.
*   **Main Lemmas:** Invariance of the Luttinger Hamiltonian under Dual Exchange.

### Chapter 21: Gaps & Spin-1/2 Generalizations
**Description:** Generalizes to systems with physical spin (Spin-Charge Separation) and analyzes when Umklapp scattering breaks the budget bounds to open an energy gap.
*   **Main Definitions:** Spin and Charge Densities, Sine-Gordon Umklapp Terms.
*   **Main Lemmas:** Factorization of Spin-Charge Hilbert Spaces.
