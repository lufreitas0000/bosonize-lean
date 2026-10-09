# BOSONIZE-LEAN: Mathematical Reference Notes

## Part V: Phase 5 Interactions & The Luttinger Liquid

### Introduction to Phase 5: From Kinematics to Many-Body Models

In the strict algebraic formulation of Quantum Field Theory (AQFT) and Many-Body Physics, a complete physical theory is defined by a triad of structures:

1. **The Operator Algebra:** The observables (e.g., the CAR net constructed in Chapter 6).

2. **The State Space:** The Hilbert space representation (e.g., our Energy Budget subspace).

3. **The Hamiltonian:** The operator governing energy and dynamics.

**The End of General Kinematics:**
Everything we have formalized in Phases 1 through 4 is purely **Kinematic**. The creation of fermions, the existence of bosonic density waves, the commutation relations, and the Mattis-Mandelstam dictionary are universal mathematical identities. They hold true regardless of whether the particles are free, interacting, or subject to external fields.

**The Role of the Hamiltonian (Dynamics & Ground States):**
However, a physical model is only defined once we specify the Hamiltonian. Even before we turn on the clock to calculate time evolution, the Hamiltonian does something profound: it defines the **ground state** (the vacuum) and the **normal modes** (the quasi-particles).
In higher dimensions (2D and 3D), interacting many-body Hamiltonians typically reorganize the vacuum into "quasi-free" states. For example, Coulomb interactions might lead to a Fermi Liquid (where excitations are dressed fermions with a finite lifetime), or attractive interactions might trigger non-perturbative symmetry breaking, reorganizing the vacuum into a BCS superconducting state or magnetically ordered matter.

**The 1D Hamiltonian Zoo:**
In 1+1 dimensions, the physics is famously different. Interacting fermions cannot pass each other, so individual quasi-particle excitations are strictly forbidden. All excitations must become collective waves.
A general many-body fermionic Hamiltonian in 1D consists of free hopping (kinetic energy) plus generic two-body interactions: $H = H_{\text{kin}} + \int V(x-y) \rho(x) \rho(y)$. In momentum space, this scatters fermions. We classify these scattering processes into a "zoo" of models based on the momentum transfer $q$:

* **Forward Scattering (**$g_2, g_4$**):** Particles scatter with small momentum transfer ($q \approx 0$). They stay on their respective branches (Right or Left). This interaction modifies the sound velocity but keeps the system gapless. This is the **Luttinger Liquid**.

* **Backscattering (**$g_1$**):** Particles scatter with large momentum transfer ($q \approx 2k_F$), bouncing from the Right branch to the Left branch.

* **Umklapp Scattering (**$g_3$**):** If the lattice is half-filled, two Right-movers can scatter into two Left-movers, dumping momentum $4k_F$ into the underlying discrete lattice.

**Why focus on Forward Scattering (The Luttinger Model)?**
We focus exclusively on local, forward-scattering density-density interactions in this phase for a profound mathematical reason: **It is exactly solvable.** Because the interaction is a product of densities ($\rho \rho$), and because we proved in Phase 2 that densities act as independent bosons, this interacting quartic fermionic Hamiltonian is strictly **quadratic** in the bosonic basis. By focusing on this model, we can formalize the exact breakdown of the Fermi liquid and the emergence of the Luttinger Liquid fixed point purely via algebraic diagonalization, completely non-perturbatively. (We will address Umklapp scattering and the opening of physical gaps in Phase 6).

### Chapter 17: Forward Scattering & The Luttinger Hamiltonian

In the strict 1D Luttinger Liquid model, we focus on interactions that occur near the Fermi points. We introduced the Left ($L$) and Right ($R$) chirality species in Chapter 13. When particles undergo forward scattering, they strictly conserve the number of fermions on each individual branch ($N_R$ and $N_L$ are conserved independently).

Traditionally, this local forward scattering is parametrized by two coupling constants:

* $g_4$ **(Intra-branch):** Scattering between two Right-movers or two Left-movers.

* $g_2$ **(Inter-branch):** Dispersive scattering between a Right-mover and a Left-mover.

#### 17.1 Definitions of the 4-Fermion Interactions

**Physical Intuition (The Point-Interaction Limit):**
A completely local density-density interaction in real space, $V \int dx \sum_{\nu, \nu'} :\! n_\nu(x) n_{\nu'}(x) \!:$, corresponds to a momentum-space scattering amplitude that is constant for all momentum transfers $q$. To rigorously map this onto our finite lattice, we define the exact 4-fermion momentum sums.

**Definition 17.1 (Raw Intra-branch Interaction** $g_4$**).**
Let $g_4 \in \mathbb{R}$ be the interaction strength. The intra-branch interaction involves two particles of the same species $\nu \in \{R, L\}$ exchanging momentum $m$. To avoid infinite background vacuum energies, we explicitly define it using the normal-ordered fermionic operators:

$$
H_{4, \text{raw}} := \frac{g_4}{2L} \sum_{\nu \in \{R, L\}} \sum_{m \in \Lambda^*} \sum_{k, p \in \Lambda^*} :\! c^\dagger_{(\nu, k+m)} c_{(\nu, k)} c^\dagger_{(\nu, p-m)} c_{(\nu, p)} \!: \tag{17.1}
$$

**Definition 17.2 (Raw Inter-branch Interaction** $g_2$**).**
Let $g_2 \in \mathbb{R}$ be the interaction strength between different branches. The momentum exchange $m$ shifts one Right-mover and one Left-mover in opposite directions. Because the species operators strictly commute, fermionic normal ordering reduces exactly to placing the respective branch operators side-by-side:

$$
H_{2, \text{raw}} := \frac{g_2}{L} \sum_{m \in \Lambda^*} \left( \sum_{k \in \Lambda^*} :\!c^\dagger_{(R, k+m)} c_{(R, k)}\!: \right) \left( \sum_{p \in \Lambda^*} :\!c^\dagger_{(L, p-m)} c_{(L, p)}\!: \right) \tag{17.2}
$$

#### 17.2 Algebraic Reduction to Bosonic Modes

**Physical Intuition (Sum Factorization):**
Looking closely at $H_{2, \text{raw}}$, the sums over the fermion momenta $k$ and $p$ are completely decoupled from each other. They factorize perfectly into the exact definitions of the macroscopic density modes $\rho_{m, R}$ and $\rho_{-m, L}$. The $g_4$ term factorizes similarly, though we must carefully account for the normal-ordering of operators of the *same* species.

**Lemma 17.3 (Exact Factorization of Inter-branch** $g_2$**).**
By the definition of the normal-ordered density modes (Definition 9.3, $:\!\rho_{m, \nu}\!:$), the inter-branch 4-fermion interaction is algebraically identical to a purely bilinear sum of density modes on the entire Fock space:

$$
H_{2, \text{raw}} = \frac{g_2}{L} \sum_{m \in \Lambda^*} :\!\rho_{m, R}\!: :\!\rho_{-m, L}\!: \tag{17.3}
$$

Because $R$ and $L$ operators commute, bosonic normal-ordering is trivial here. On the low-energy budget subspace $\mathcal{B}_{K, \vec{N}_{max}}$, modes where $\vert{}m\vert{} > K$ strictly annihilate the state.

**Lemma 17.4 (Exact Factorization of Intra-branch** $g_4$**).**
For the intra-branch scattering, standard fermionic Wick contractions reduce the 4-fermion term to the product of two density modes, minus a singular diagonal contraction term. When mapped to the bosonic density operators, this precisely matches the requirement for *bosonic* normal ordering (placing creation modes $m > 0$ strictly to the left).
On the budget subspace $\mathcal{B}_{K, \vec{N}_{max}}$, under the standard M2 margin condition, the intra-branch interaction simplifies exactly to:

$$
H_{4, \text{raw}} = \frac{g_4}{L} \sum_{\nu \in \{R, L\}} \sum_{m=1}^{h-1} \rho_{m, \nu} \rho_{-m, \nu} + \frac{g_4}{2L} \sum_{\nu \in \{R, L\}} \hat{N}_\nu^2 \tag{17.4}
$$

#### 17.3 The Interacting Luttinger Hamiltonian and Helper Lemmas

We can now define the full Hamiltonian of the 1D system. To ensure our Lean 4 proofs do not suffer from massive, monolithic algebra steps, we define the Hamiltonian and then introduce precise helper lemmas to group the terms.

**Definition 17.5 (The Luttinger Hamiltonian).**
Let the free Fermi velocity be $v_F$ (where $v_F = 2\pi/L$ in our previous dimensionless units). The exact, global Luttinger Hamiltonian on the budget subspace, combining free kinetic energy and forward scattering interactions, is defined as:

$$
H_{\text{Lutt}} := H_0 + H_{4, \text{raw}} + H_{2, \text{raw}} \tag{17.5}
$$

**Helper Lemma 17.6 (Chiral Sugawara Decomposition).**
The full kinetic energy operator $H_0$ decomposes identically into independent left and right-moving Sugawara Hamiltonians. On the budget subspace:

$$
H_0 = \frac{2\pi v_F}{L} \sum_{\nu \in \{R,L\}} \left( \sum_{m=1}^{h-1} \rho_{m, \nu} \rho_{-m, \nu} + \frac{1}{2}\hat{N}_\nu^2 \right) \tag{17.6}
$$

**Helper Lemma 17.7 (Algebraic Mode Regrouping).**
Because the sums in Lemmas 17.3, 17.4, and 17.6 share the identical finite indexing set $m \in \{1, \dots, h-1\}$, the sum operator $\sum_{m}$ distributes linearly over the algebra. The zero-mode terms ($\hat{N}_R, \hat{N}_L$) strictly decouple from the strictly positive $m \ge 1$ fluctuation sums.

**Theorem 17.8 (The Bosonized Luttinger Hamiltonian).**
Under the R2 margin condition, applying the helper lemmas to collect all $m \ge 1$ terms inside a single summation, the full interacting 4-fermion Luttinger Hamiltonian evaluates exactly to a quadratic bilinear bosonic form on the budget subspace:

$$
H_{\text{Lutt}} = \frac{2\pi}{L} \sum_{m=1}^{h-1} \left[ \left( v_F + \frac{g_4}{2\pi} \right) \left( \rho_{m, R} \rho_{-m, R} + \rho_{m, L} \rho_{-m, L} \right) + \frac{g_2}{2\pi} \left( \rho_{m, R} \rho_{-m, L} + \rho_{m, L} \rho_{-m, R} \right) \right] + E_{\text{zero}} \tag{17.8}
$$

where the zero-mode energy $E_{\text{zero}}$ depends only on the strictly conserved total particle numbers $\hat{N}_R$ and $\hat{N}_L$:

$$
E_{\text{zero}} = \frac{2\pi}{L} \left[ \frac{1}{2}\left(v_F + \frac{g_4}{2\pi}\right)(\hat{N}_R^2 + \hat{N}_L^2) + \frac{g_2}{2\pi}\hat{N}_R \hat{N}_L \right] \tag{17.9}
$$

#### 17.4 Physical Corollaries and Consequences

The mathematical structure of Theorem 17.8 has profound physical implications for 1D matter, completely breaking the standard Fermi liquid paradigm.

**Corollary 17.9 (Exact Solvability via Quadraticity).**
Despite originating from an intractable, non-linear 4-fermion interaction term, the Hamiltonian $H_{\text{Lutt}}$ is strictly quadratic (degree 2) in the bosonic basis. The physics of strongly interacting fermions in 1D is thus mathematically isomorphic to a set of macroscopic, coupled non-interacting harmonic oscillators.

**Corollary 17.10 (Matrix Formulation and Chiral Mixing).**
To see the coupling clearly, the terms inside the sum for each mode $m$ can be factored into a $2 \times 2$ symmetric block matrix acting on the density vector $\vec{\rho}_m = (\rho_{m, R}, \rho_{m, L})^T$:

$$
H_{\text{mode } m} \propto (\rho_{m,R}, \rho_{m,L}) \begin{pmatrix} v_F + \frac{g_4}{2\pi} & \frac{g_2}{2\pi} \\ \frac{g_2}{2\pi} & v_F + \frac{g_4}{2\pi} \end{pmatrix} \begin{pmatrix} \rho_{-m,R} \\ \rho_{-m,L} \end{pmatrix} \tag{17.10}
$$

Because the off-diagonal $g_2$ elements are non-zero, the Right and Left density waves are linearly coupled. Therefore, the bare chiral operators $\rho_{m, R}$ are **no longer the eigenstates (normal modes)** of the system. The true eigenstates must be a linear mixture of $R$ and $L$ waves. (We will explicitly diagonalize this matrix using the Bogoliubov transformation in Chapter 18).

**Corollary 17.11 (Velocity Renormalization).**
If $g_2 = 0$ but $g_4 \neq 0$, the matrix is diagonal. The $g_4$ interaction does not mix branches, but it strictly shifts the leading diagonal term. This means the intra-branch repulsion simply causes the density waves to propagate faster. The free Fermi velocity $v_F$ is strictly renormalized to a faster "sound velocity":

$$
v_{\text{sound}} = v_F + \frac{g_4}{2\pi} \tag{17.11}
$$

#### 17.5 Technical Notes for the Lean 4 Formalization (Chapter 17)

1. **Defining the 4-Fermion Sums (`Finset.sum` factorizations):**

   * Do **not** attempt to prove the factorization by expanding the raw definitions of $\rho_m$ into the Hamiltonian and matching terms.

   * Instead, define the interaction algebraically using Lean's `Finset.sum` over the independent indices $k$ and $p$.

   * Use `Finset.sum_mul` and `Finset.mul_sum` (distributivity of finite sums over algebra products) to explicitly factor the inner sums out of the $m$ summation.

   * Lean's algebraic solver (`ring` or `abel`) will easily recognize that $\left(\sum_k A_k\right) \cdot \left(\sum_p B_p\right) = \sum_k \sum_p A_k B_p$.

2. **Fermionic vs. Bosonic Normal Ordering:**

   * In Lemma 17.4, the 4-fermion term is defined with fermionic normal ordering. You will need to apply the CAR commutator $[c_p^\dagger, c_k] = \delta_{pk} - c_k c_p^\dagger$ once to swap the middle operators to match the definition of $\rho_m \rho_{-m}$.

   * This CAR swap generates a trace term (a Kronecker delta $\delta_{k, p-m}$), which explicitly evaluates to the density zero-mode $\hat{N}_\nu$. This perfectly accounts for the $\hat{N}^2$ background shift in Equation 17.4.

3. **Applying the Helper Lemmas (`sum_add_distrib`):**

   * The proof of Theorem 17.8 in Lean should be a sequence of pure `rw` (rewrite) tactics.

   * First, `rw [Helper_17_6, Helper_17_3, Helper_17_4]` to replace the raw Hamiltonians with their bosonic forms.

   * Second, repeatedly apply `Finset.sum_add_distrib.symm` to pull the disjoint sums over $m$ together into one giant sum.

   * Finally, use `ring` to group the scalar coefficients $(v_F + g_4/2\pi)$ and $g_2/2\pi$.

4. **Equality on the Budget Subspace:**

   * Just like the Sugawara equivalence, Theorem 17.8 must be stated as an exact equality on the `BudgetSpace L K Nmax` type, **not** as a global identity on `Module.End ℂ (FockSpace _)`. The boundary margins must be strictly enforced so that modes where $\vert{}m\vert{} > K$ are mathematically annihilated, preventing any sum divergences.
