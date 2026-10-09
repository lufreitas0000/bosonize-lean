# BOSONIZE-LEAN: Mathematical Reference Notes

## Part VI: Phase 6 Observables, Correlators & Duality

### Chapter 21: Gaps & Spin-1/2 Generalizations

In all previous chapters, we analyzed a "spinless" (or fully spin-polarized) fermionic fluid. Real electrons, however, possess a spin-1/2 degree of freedom. In higher dimensions, an interacting electron moves as a single unified quasi-particle carrying both its charge and its spin. In 1D, the strict geometric constraints force the collective charge density waves and the collective spin density waves to decouple entirely, traveling at different macroscopic speeds. This is known as **Spin-Charge Separation**.

By expanding our finite-lattice multi-species index set, we will prove that this separation is not an approximation, but an exact, strict algebraic factorization of the Kac-Moody algebras and the Hamiltonian on the budget space.

Finally, we will examine non-forward scattering processes (Umklapp and backscattering), proving algebraically why they break our exact quadratic diagonalization and lead to the opening of physical energy gaps, strictly placing limits on the budget subspace.

#### 21.1 The Spinful Index Set and Spin-Charge Separation

To introduce spin, we expand the internal species index set $\mathcal{C}$ from Chapter 13.

**Definition 21.1 (Spinful Species Index).**
Let the chirality set be $\mathcal{D} = \{R, L\}$ and the spin set be $\mathcal{S} = \{\uparrow, \downarrow\}$. The complete multi-species index set is the Cartesian product:

$$
\mathcal{C} := \mathcal{D} \times \mathcal{S} = \{(R, \uparrow), (R, \downarrow), (L, \uparrow), (L, \downarrow)\} \tag{21.1}
$$

The fundamental density modes are now indexed by both chirality and spin: $\rho_{m, \nu, s}$ for $\nu \in \mathcal{D}$ and $s \in \mathcal{S}$. Because modes with different species strictly commute, we have four independent Kac-Moody algebras.

**Physical Intuition (Symmetric and Antisymmetric Modes):**
If we push a spin-up electron and a spin-down electron in the same direction, we create a wave of electrical charge, but zero net spin. If we push a spin-up electron forward and a spin-down electron backward, we create a wave of magnetization (spin), but zero net electrical charge.

**Definition 21.2 (Charge and Spin Density Modes).**
We define the collective Charge ($c$) and Spin ($s$) density modes as the exact normalized algebraic sum and difference of the bare spin modes:

$$
\rho_{m, \nu}^c := \frac{1}{\sqrt{2}} \left( \rho_{m, \nu, \uparrow} + \rho_{m, \nu, \downarrow} \right) \tag{21.2}
$$

$$
\rho_{m, \nu}^s := \frac{1}{\sqrt{2}} \left( \rho_{m, \nu, \uparrow} - \rho_{m, \nu, \downarrow} \right) \tag{21.3}
$$

**Lemma 21.3 (Algebraic Spin-Charge Decoupling).**
Because the bare modes commute $[\rho_{m, \nu, \uparrow}, \rho_{n, \nu, \downarrow}] = 0$, the cross-commutator between any charge mode and any spin mode identically vanishes. The new modes form two strictly independent Kac-Moody algebras on the energy budget:

$$
[\rho_{m, \nu}^c, \rho_{n, \nu'}^s] = 0 \tag{21.4}
$$

$$
[\rho_{-m, \nu}^c, \rho_{m, \nu}^c] = [\rho_{-m, \nu}^s, \rho_{m, \nu}^s] = m \tag{21.5}
$$

*Proof Sketch:* $[\rho^c, \rho^s] \propto [\rho_\uparrow + \rho_\downarrow, \rho_\uparrow - \rho_\downarrow] = [\rho_\uparrow, \rho_\uparrow] - [\rho_\downarrow, \rho_\downarrow] = m - m = 0$.

**Corollary 21.4 (Hamiltonian Factorization).**
If the microscopic 4-fermion interactions are symmetric with respect to spin (i.e., spin-up particles interact with each other identically to how they interact with spin-down particles), the full Luttinger Hamiltonian algebraically factorizes into two completely uncoupled components:

$$
H_{\text{Lutt}} = H_{\text{charge}}[\rho^c] + H_{\text{spin}}[\rho^s] \tag{21.6}
$$

Because these Hamiltonians are completely decoupled, the interaction parameters $g_{charge}$ and $g_{spin}$ will renormalize the charge and spin sound velocities independently, yielding exact, distinct eigenvalues $u_c \neq u_s$.

#### 21.2 The True Spin-Singlet Cooper Pair and Phase Fields

In Chapter 20, we used a mathematically convenient "spinless" pair. Now we can formally define the physical **Spin-Singlet Superconducting (SSC)** order parameter, which binds two fermions from opposite branches with opposite spins, strictly antisymmetric under exchange.

**Definition 21.5 (Singlet Cooper Pair).**
The macroscopic singlet pairing operator is defined algebraically as:

$$
O_{SSC}(x) := c_{(R, \uparrow, x)} c_{(L, \downarrow, x)} - c_{(R, \downarrow, x)} c_{(L, \uparrow, x)} \tag{21.7}
$$

To bosonize this exactly without using vague proportionalities ($\propto$) or continuous limits (like $\cos$), we must explicitly construct the separated phase fields.

**Definition 21.6 (Charge and Spin Phase Fields).**
Using the base unnormalized phase fields $W^\pm_{\nu, s}(x)$ defined in Chapter 14 (Definition 14.1), we define the exact charge and spin phase fields strictly as linear combinations:

$$
W^\pm_{c, \nu}(x) := \frac{1}{\sqrt{2}} \left( W^\pm_{\nu, \uparrow}(x) + W^\pm_{\nu, \downarrow}(x) \right) \tag{21.8}
$$

$$
W^\pm_{s, \nu}(x) := \frac{1}{\sqrt{2}} \left( W^\pm_{\nu, \uparrow}(x) - W^\pm_{\nu, \downarrow}(x) \right) \tag{21.9}
$$

**Theorem 21.7 (Exact Factorization of the Cooper Pair).**
By substituting the exact Mattis-Mandelstam dictionary (Definition 14.4) into $O_{SSC}(x)$, the expression rigorously factorizes into a product of charge operators and spin operators. On the budget subspace, the operator evaluates strictly to:

$$
O_{SSC}(x) = \frac{1}{L} \left( K_{SSC} \cdot \exp(W^-_{c,R} + W^-_{c,L}) \exp(W^+_{c,R} + W^+_{c,L}) \cdot \Psi_{\text{spin}}(x) \right) \tag{21.10}
$$

where $K_{SSC} := F_{R,\uparrow} F_{L,\downarrow} Z_{R,\uparrow} Z_{L,\downarrow}$ is the composite zero-mode and Klein operator, and $\Psi_{\text{spin}}(x)$ is the exact finite algebraic combination of the independent spin phase fields (which in the continuous thermodynamic limit asymptotically approximates the $\cos(\sqrt{2}\phi_s)$ term).

#### 21.3 Umklapp Scattering and the Budget Breakdown

**Recall (Forward Scattering):**
In Chapter 17, we proved that the forward scattering Hamiltonian $H_{\text{forward}} = H_0 + H_{4} + H_{2}$ strictly preserves the number of particles on each branch independently ($[H_{\text{forward}}, \hat{N}_R] = [H_{\text{forward}}, \hat{N}_L] = 0$). This global sector conservation was the absolute mathematical prerequisite for exactly diagonalizing the system using bosonic density modes on the budget space.

What happens if interactions transfer large momentum, bouncing a Right-mover into a Left-mover?

**Physical Intuition (Backscattering and Umklapp):**

* **Backscattering (**$g_1$**):** A Right-mover and Left-mover collide and switch places.

* **Umklapp (**$g_3$**):** At exactly half-filling, two Right-movers collide and are both bounced into the Left-moving branch. The deficit momentum of $4k_F$ is perfectly absorbed by the underlying discrete atomic lattice.

Because these processes change the branch charges (e.g., $\Delta N_R = -2, \Delta N_L = +2$), they cannot be written as quadratic products of density modes $\rho_R \rho_L$.

**Definition 21.8 (The Exact Umklapp Operator).**
The Umklapp scattering operator destroys two $R$ particles and creates two $L$ particles of opposite spins. It is defined precisely as:

$$
O_{U}(x) := c^\dagger_{(L, \uparrow, x)} c^\dagger_{(L, \downarrow, x)} c_{(R, \downarrow, x)} c_{(R, \uparrow, x)} \tag{21.11}
$$

The exact Hermitian Umklapp Hamiltonian is the spatial sum over the lattice:

$$
H_U := \frac{g_3}{2} \sum_{x \in \Lambda} \left( O_U(x) + O_U^\dagger(x) \right) \tag{21.12}
$$

**Lemma 21.9 (Breakdown of the Energy Budget).**
The Umklapp Hamiltonian strictly violates the margin conditions of the energy budget subspace $\mathcal{B}_{K, \vec{N}_{max}}$.
Specifically, substituting the bosonization dictionary into $O_U(x)$ explicitly requires the composite Klein factor $F^\dagger_{L,\uparrow} F^\dagger_{L,\downarrow} F_{R,\downarrow} F_{R,\uparrow}$. This operator evaluates to an exact shift of the charge sector vector:

$$
\vec{N} \mapsto \vec{N} + 2e_{L,\uparrow} + 2e_{L,\downarrow} - 2e_{R,\downarrow} - 2e_{R,\uparrow} \tag{21.13}
$$

If a state $\psi$ lies on the strict upper boundary of the charge margin $N_{max}$, the application of $H_U$ maps the vector cleanly and violently outside the defined budget subspace.

**Physical Consequence (The Mott Gap):**
This mathematical breakdown corresponds to a profound physical phase transition. Because $H_U$ couples different charge sectors, it explicitly breaks the strict algebraic nilpotency required for the Baker-Campbell-Hausdorff truncations. The exact quadratic diagonalization (the Bogoliubov Transformation of Chapter 18) mathematically fails.
When Umklapp scattering is relevant (which occurs when interactions are sufficiently repulsive), the charge field becomes locked into the minima of the interaction potential. The system transitions from a gapless conducting Luttinger Liquid into a **Mott Insulator** with a strict physical energy gap. Solving this exact massive model (the Sine-Gordon model) algebraically requires stepping beyond free bosons into Integrable Systems (Bethe Ansatz), which lies outside the quadratic kinematic framework of this text.

#### 21.4 Technical Notes for the Lean 4 Formalization (Chapter 21)

1. **Defining the Spinful Product Type:**

   * Do not define four independent integer variables. Define `inductive Spin | up | down` with `[DecidableEq Spin]`.

   * The new species type is `ι := (Chirality × Spin) × LambdaDual L`.

   * Lean's `Prod.lex` will automatically handle the lexicographical ordering needed for the global CAR sign tracking across all four branches identically.

2. **Spin and Charge Density Basis:**

   * You can define $\rho^c$ and $\rho^s$ strictly as linear maps over the module.

   * Proving Lemma 21.3 is a massive payoff for Lean's algebra system. By expanding the bilinear definitions of $\rho^c$ and $\rho^s$ and pushing them through the basic commutator `[A+B, A-B] = [B, A] + [A, B] = 0` (since independent species commute), Lean will instantly verify the decoupling without needing to re-prove the underlying edge anomalies.

3. **Formalizing Umklapp in Lean:**

   * We define the operator $O_{U}(x)$ strictly as the 4-fermion product using $c$ and $c^\dagger$.

   * We do **not** attempt to prove a Sugawara-like equivalence for it. Instead, we formalize Lemma 21.9 as a negative proof: we construct a specific state on the boundary of the budget where the application of the Umklapp term evaluates to a vector whose type/bounds strictly violate the `BudgetSpace` bounds, formally certifying the limits of the quadratic theory within the proof assistant.
