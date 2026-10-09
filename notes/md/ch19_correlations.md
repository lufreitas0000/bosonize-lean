# BOSONIZE-LEAN: Mathematical Reference Notes

## Part VI: Phase 6 Observables, Correlators & Duality

### Introduction to Phase 6: From Algebra to Physics

In the preceding phases, we constructed a mathematically exact, finite-dimensional framework for 1D fermions. We proved that their kinematics are exactly bosonic on a low-energy budget (Phases 1–3), mapped these modes to continuous-looking spatial fields (Phase 4), and used an exact algebraic Bogoliubov transformation to diagonalize the interacting density-density Hamiltonian (Phase 5).

What remains is the physics. A quantum field theory is ultimately judged by its predictions for physical observables—specifically, its **Correlation Functions**. Correlation functions measure how a fluctuation at one point in space and time affects the system at another point.

In standard many-body physics, turning on interactions completely changes the ground state. A Fermi Liquid has quasi-particles with infinite lifetimes at the Fermi surface. A Luttinger Liquid has no individual quasi-particles at all; any localized fermion instantly shatters into a collective ripple of charge and spin. This is mathematically detected by the decay rate of the spatial correlation functions: instead of standard exponential or specific free-fermion decays, the Luttinger Liquid exhibits anomalous **power-law decays** governed continuously by the interaction parameter $g$.

In this phase, we will calculate these correlators purely algebraically. Because we are on a finite lattice, we will not take infinite limits or use analytical integrals. Instead, our correlators will evaluate to **exact finite discrete sums** (analogous to Dirichlet kernels) that mathematically embody the physical power-law behavior without requiring any continuous regularizations. We will then use this exact algebraic machinery to formalize the famous **Topological Duality** of the Luttinger Liquid (Chapter 20).

### Chapter 19: Exact Correlation Functions

To calculate physical observables, we must define the interacting ground state and establish a rigorous algebraic method for evaluating expectation values without getting bogged down in explicitly constructing massive matrix eigenvectors.

#### 19.1 The Interacting Vacuum and Algebraic States

**Physical Intuition (The Bogoliubov Vacuum):**
In a free system, the ground state is the Dirac vacuum $\vert{}\Omega\rangle$, which is perfectly annihilated by all lowering operators: $\rho_{-m} \vert{}\Omega\rangle = 0$ (for $m > 0$).
However, under interactions, the Hamiltonian is diagonalized by the *dressed* modes $\tilde{\rho}$. The true ground state of the interacting system, denoted $\vert{}\tilde{\Omega}\rangle$, must be the state that is empty of these new dressed quasi-particles. Therefore, it is perfectly annihilated by the dressed lowering operators: $\tilde{\rho}_{-m} \vert{}\tilde{\Omega}\rangle = 0$.
Because the bare operators $\rho$ are mixtures of dressed creators and annihilators, the interacting vacuum $\vert{}\tilde{\Omega}\rangle$ is *not* empty with respect to the bare fermions; it is mathematically boiling with virtual particle-hole pairs!

**Definition 19.1 (Algebraic State Functional).**
In the algebraic formulation of Quantum Field Theory (AQFT), a "state" is not necessarily a vector; it is defined strictly as a normalized, positive linear functional on the algebra of observables.
Let $\mathfrak{A}_{\mathcal{B}} = \mathrm{End}_{\mathbb{C}}(\mathcal{B}_{K, \vec{N}_{max}})$ be the observable algebra on the budget subspace. We define the interacting vacuum state functional $\omega_{\tilde{\Omega}} : \mathfrak{A}_{\mathcal{B}} \to \mathbb{C}$ as the unique linear mapping satisfying:

1. **Normalization:**


   $$
   \omega_{\tilde{\Omega}}(I) = 1 \tag{19.1}
   $$

2. **Annihilation Conditions:** For *any* arbitrary operator $A \in \mathfrak{A}_{\mathcal{B}}$, and for all strictly positive modes $m \ge 1$, the functional evaluates to zero if the operator ends in a dressed annihilator (evaluating the right ideal) or begins with a dressed creator (evaluating the left ideal):


   $$
   \forall A, \forall \nu \in \{R, L\}, \quad \omega_{\tilde{\Omega}}(A \cdot \tilde{\rho}_{-m, \nu}) = 0 \tag{19.2}
   $$

   $$
   \forall A, \forall \nu \in \{R, L\}, \quad \omega_{\tilde{\Omega}}(\tilde{\rho}_{m, \nu} \cdot A) = 0 \tag{19.3}
   $$

*(Note: In Lean, we evaluate expectation values strictly by using the commutator relations to push all annihilation operators to the right until they hit the rightmost position, at which point the entire term evaluates to zero via Equation 19.2. This completely bypasses the need to instantiate the raw Fock space vector* $\vert\tilde{\Omega}\rangle$*)*.

#### 19.2 Algebraic Evaluation of the Mode Correlators

**Physical Intuition (Virtual Pair Density):**
If we want to measure the bare density fluctuations in the interacting ground state, we need to evaluate the expectation value of $\rho_m \rho_{-m}$. We do this by substituting the Inverse Bogoliubov transformation (from Chapter 18, Lemma 18.5) and using the vacuum functional properties.

**Lemma 19.2 (Inverse Mode Substitution).**
Recall the exact inverse transformation for the bare Right-moving modes in terms of the dressed modes:

$$
\rho_{m, R} = c \cdot \tilde{\rho}_{m, R} - s \cdot \tilde{\rho}_{-m, L} \tag{19.4}
$$

$$
\rho_{-m, R} = c \cdot \tilde{\rho}_{-m, R} - s \cdot \tilde{\rho}_{m, L} \tag{19.5}
$$

**Theorem 19.3 (Exact Interacting Mode Correlator).**
Let $m, n \ge 1$ be positive integer modes within the budget margin. The expectation value of the bare density correlation in the interacting vacuum evaluates exactly to:

$$
\omega_{\tilde{\Omega}}(\rho_{m, R} \rho_{-n, R}) = \delta_{mn} \cdot m \cdot s^2 \tag{19.6}
$$

*Formal Proof Sketch for Lean:*
Substitute the inverse definitions into the functional:
$\omega_{\tilde{\Omega}}((c \tilde{\rho}_{m, R} - s \tilde{\rho}_{-m, L})(c \tilde{\rho}_{-n, R} - s \tilde{\rho}_{n, L}))$.
Distributing this product linearly yields four terms. Because $\tilde{\rho}_{-n, R}$ is an annihilator on the right, any term ending in it evaluates to 0 by Def 19.1. Similarly, $\tilde{\rho}_{-m, L}$ is a creator on the left, so any term beginning with it evaluates to 0.
The only surviving term is the product of the two cross-branch operators:
$= \omega_{\tilde{\Omega}}(s^2 \tilde{\rho}_{-m, L} \tilde{\rho}_{n, L})$.
Using the dressed Kac-Moody algebra (Theorem 18.4), we commute them: $[\tilde{\rho}_{-m, L}, \tilde{\rho}_{n, L}] = m \delta_{mn} I$.
$= s^2 ( \omega_{\tilde{\Omega}}(\tilde{\rho}_{n, L} \tilde{\rho}_{-m, L}) + m \delta_{mn} \omega_{\tilde{\Omega}}(I) )$.
The first term vanishes (annihilator on the right). Because $\omega_{\tilde{\Omega}}(I) = 1$, the functional evaluates exactly to $m \cdot s^2 \delta_{mn}$. $\blacksquare$

*Corollary:* The interacting vacuum contains a strict, non-zero density of bare fluctuations directly proportional to $s^2$, which is determined entirely by the interaction strength $g_2$. The vacuum is "squeezed".

#### 19.3 Real-Space Spatial Correlators

**Physical Intuition (The Lattice Power Law):**
To see how this looks in physical space, we Fourier transform the mode correlator back to spatial coordinates. In the continuum, a momentum space correlator of $\langle \rho_q \rho_{-q} \rangle \propto \vert{}q\vert{}$ Fourier transforms to a real-space spatial decay of $1/x^2$. On our finite lattice, we sum over the discrete modes, yielding an exact trigonometric identity that perfectly mimics $1/x^2$ in the bulk, but respects the periodic boundaries of the lattice ring.

**Definition 19.4 (Spatial Density Operator).**
The bare, normal-ordered macroscopic spatial density for a given branch at position $x \in \Lambda$ is defined via the finite Fourier transform of the density modes:

$$
:\!\rho_R(x)\!: \ := \frac{1}{L} \sum_{m=1}^{h-1} \left( \zeta^{-mx} \rho_{m, R} + \zeta^{mx} \rho_{-m, R} \right) \tag{19.7}
$$

**Theorem 19.5 (Exact Spatial Density Correlator).**
The equal-time spatial correlation function between two points $x$ and $y$ on the lattice, evaluated in the interacting ground state, evaluates exactly to the finite discrete sum:

$$
D_c(x, y) := \omega_{\tilde{\Omega}} (:\!\rho_R(x)\!: :\!\rho_R(y)\!:) = \frac{s^2}{L^2} \sum_{m=1}^{h-1} m \left( \zeta^{m(x-y)} + \zeta^{-m(x-y)} \right) = \frac{2s^2}{L^2} \sum_{m=1}^{h-1} m \cos\left( \frac{2\pi m (x-y)}{L} \right) \tag{19.8}
$$

*(Note: This finite sum is an exact algebraic identity. For distance* $\vert{}x-y\vert{} \gg 1$ *and large* $L$*, this discrete trigonometric sum asymptotically evaluates exactly to* $\propto 1 / (x-y)^2$*, demonstrating the Luttinger liquid power-law directly from finite algebra).*

#### 19.4 Technical Notes for the Lean 4 Formalization (Chapter 19)

1. **Defining the State Functional (`LinearMap`):**

   * Do **not** attempt to compute the matrix eigenvectors of the interacting Hamiltonian to find $\vert{}\tilde{\Omega}\rangle$.

   * Instead, define `interacting_vacuum` as a `LinearMap` from the algebra of observables `Module.End ℂ BudgetSpace` to `ℂ`.

   * Define its properties purely axiomatically using universal quantifiers: `∀ A, eval (A * dressed_annihilator) = 0` and `∀ A, eval (dressed_creator * A) = 0`.

2. **Commutator Pushing Strategy:**

   * To prove Theorem 19.3 in Lean, the proof should be a structured sequence of rewrites (`rw`).

   * First, `rw [inverse_bogoliubov_R, inverse_bogoliubov_L]` to replace the bare modes.

   * Second, expand the algebraic multiplication using `mul_add` and `add_mul`. The functional's linearity `map_add` will split it into four evaluations.

   * Third, apply the Kac-Moody commutator to swap the order of the surviving $L$ branch operators: `rw [dressed_kac_moody]`.

   * Finally, `simp` using the vacuum annihilator axioms to collapse all non-scalar terms to 0, leaving only the exact algebraic scalar $s^2 \cdot m$.

3. **Spatial Correlators and `Real.cos`:**

   * The definition of $D_c(x, y)$ initially yields a sum of $\zeta^{m(x-y)} + \zeta^{-m(x-y)}$.

   * Stay in the complex algebraic field as long as possible. Only at the very end, introduce a bridge lemma equating $\zeta^k + \zeta^{-k}$ to $2 \cos(2\pi k / L)$ if the continuous physical interpretation is strictly required for documentation. The algebraic proof of the correlator completes flawlessly using only $\zeta$.
