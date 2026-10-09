# BOSONIZE-LEAN: Mathematical Reference Notes

## Part III: Phase 3 The Bosonization Dictionary

### Chapter 14: The Mattis-Mandelstam Formula

We have arrived at the core dictionary of bosonization: constructing a localized fermionic destruction operator $c_{(\nu, x)}$ purely out of bosonic components.

**Physical Intuition (The Vertex Operator):**
How can a collection of smooth, collective bosonic density waves ($\rho_m$) simulate the sudden destruction of a single, localized fermionic point particle?
In momentum space, destroying a fermion at position $x$ creates a "shockwave" that is perfectly localized in space, meaning it must involve a coherent superposition of *all* available momentum modes. In Conformal Field Theory (CFT) and String Theory, this is achieved using a **Vertex Operator**—an exponential of the bosonic fields.
By exponentiating the density modes, we are creating a *coherent state* of particle-hole excitations. This specific macroscopic ripple in the Fermi sea perfectly mimics the density profile and the momentum-shift properties of a missing fermion. The Klein factor $F_\nu$ then steps in to remove the actual unit of charge and enforce the correct anti-commutation statistics.

#### 14.1 Bosonic Phase Fields (No Square Roots)

In standard continuum bosonization, the exponentiated fields are written using normalized bosons $b_q$ and $b_q^\dagger$, which introduces explicit $1/\sqrt{q}$ factors. As discussed in Phase 2, we strictly avoid non-algebraic square roots in this formalization. Instead, we use the unnormalized integer-weighted currents $\rho_{m, \nu}$.
Because $\rho_m \sim \sqrt{m} b_m$, the traditional $1/\sqrt{m}$ scaling translates directly to a rational $1/m$ factor when using our modes, keeping the algebra strictly over $\mathbb{Q}(\zeta)$.

**Definition 14.1 (Chiral Phase Operators).**
Let $\zeta = e^{2\pi i / L}$ be the primitive root of unity. For each species $\nu \in \mathcal{C}$ and spatial position $x \in \Lambda$, we define the lowering and raising bosonic phase operators:

$$
W^+_{\nu}(x) := \sum_{m=1}^{h-1} \frac{\zeta^{m x}}{m} \rho_{-m, \nu} \tag{14.1}
$$

$$
W^-_{\nu}(x) := -\sum_{m=1}^{h-1} \frac{\zeta^{-m x}}{m} \rho_{m, \nu} \tag{14.2}
$$

*(Note on Convention: In accordance with standard QFT literature, such as Peskin & Schroeder, the "*$+$*" field conventionally denotes the positive-frequency/annihilation part which lowers energy, while the "*$-$*" field denotes the negative-frequency/creation part which raises energy).*

**Definition 14.2 (The Zero-Mode Phase).**
While the density modes handle the fluctuations (the ripples), the overall baseline momentum of the sector must be shifted when a particle is removed. This is governed by the total particle number $\hat{N}_\nu$. We define the zero-mode unitary phase operator:

$$
Z_\nu(x) := \zeta^{x \left( \hat{N}_\nu - \frac{1}{2} \right)} \tag{14.3}
$$

*Implementation Note:* In formal systems, exponentiating a scalar by a matrix operator is not natively well-typed. Furthermore, the $-1/2$ implies a fractional power. To define this rigorously, let $\omega$ be a primitive $2L$-th root of unity (such that $\omega^2 = \zeta$). $Z_\nu(x)$ is defined as the unique linear map whose diagonal action on the joint sector basis states $\vert{}\vec{N}\rangle$ evaluates strictly to the complex scalar $\omega^{2x N_\nu - x}$.

#### 14.2 Exact Truncated Exponentials

**Physical Intuition (Nilpotency on the Budget):**
In infinite-dimensional QFT, $\exp(W^-)$ is an infinite power series, leading to convergence and domain issues. On our finite-lattice energy budget $\mathcal{B}_{K, \vec{N}_{max}}$, these issues vanish entirely.
Because $W^-$ is a linear combination of creation modes $\rho_{m}$ (where $m \ge 1$), every application of $W^-$ strictly raises the total energy of the state by at least 1. If we apply it $K+1$ times to a state with budget $K$, it attempts to push the energy past the strict budget ceiling. By definition of the budget subspace projections, this evaluates exactly to the zero vector.

**Lemma 14.3 (Exact Nilpotency of the Phase Fields).**
On the budget subspace $\mathcal{B}_{K, \vec{N}_{max}}$, the raising phase operator is strictly nilpotent of step $K+1$. Consequently, its exponential is a finite polynomial (a truncated Taylor series) that evaluates exactly:

$$
\forall \psi \in \mathcal{B}_{K, \vec{N}_{max}}, \quad \exp(W^-_{\nu}(x)) \psi = \sum_{j=0}^{K} \frac{1}{j!} (W^-_{\nu}(x))^j \psi \tag{14.4}
$$

Because $W^+$ lowers the energy, it is similarly nilpotent, annihilating any state once it hits the sector ground state (energy 0).

#### 14.3 Helper Lemmas and The Exact Bosonization Identity

We now define the composite, purely bosonic operator that will act as our dictionary translation for the physical fermion.

**Definition 14.4 (The Bosonized Field).**
For each species $\nu \in \mathcal{C}$ and position $x \in \Lambda$, the composite bosonized field operator $B_\nu(x)$ is defined via normal ordering (raising operators to the left, lowering to the right) combined with the Klein factor and the zero-mode:

$$
B_\nu(x) := \frac{1}{\sqrt{L}} F_\nu Z_\nu(x) \exp(W^-_{\nu}(x)) \exp(W^+_{\nu}(x)) \tag{14.5}
$$

To prove the equivalence without combinatorial expansion, we establish two helper lemmas corresponding to the algebraic behavior of the fields.

**Lemma 14.5 (Commutator Matching).**
The newly defined bosonic field $B_\nu(x)$ obeys the exact same Kac-Moody commutation relations with the density modes $\rho_{m, \eta}$ as the true fermion $c_{(\nu, x)}$. For any mode $m \ge 1$:

$$
[\rho_{m, \eta}, B_\nu(x)] = -\delta_{\nu, \eta} \zeta^{mx} B_\nu(x) \tag{14.6}
$$

*Proof Sketch:* $F_\nu$ commutes with the densities. The exact BCH formulas (Lemma 8.8) applied to the phase field exponentials analytically extract the $\zeta^{mx}$ factor.

**Lemma 14.6 (Adjoint Properties of the Bosonized Field).**
The formal adjoint of the bosonized field operator flips the phase operations and inverses the Klein factor, evaluating to:

$$
B^\dagger_\nu(x) = \frac{1}{\sqrt{L}} \exp(W^-_{\nu}(x)) \exp(W^+_{\nu}(x)) Z^{-1}_\nu(x) F^\dagger_\nu \tag{14.7}
$$

*(Note: The raising and lowering fields naturally swap roles because* $(W^+_{\nu})^\dagger = W^-_{\nu}$*)*.

**Theorem 14.7 (The Mattis-Mandelstam Equivalence).**
Under the R2 Margin condition ($2K + \vert{}N_\nu\vert{} \le h$), the composite bosonized field operator $B_\nu(x)$ is algebraically identical to the true fermionic annihilation operator $c_{(\nu, x)}$ when restricted to the multi-species budget subspace:

$$
\forall \psi \in \mathcal{B}_{K, \vec{N}_{max}}, \quad c_{(\nu, x)} \psi = B_\nu(x) \psi \tag{14.8}
$$

**Corollary 14.8 (Creation Operator Equivalence).**
By applying the adjoint lemma (Lemma 14.6) to the main theorem, the fermionic creation operator is equivalently bosonized on the budget:

$$
\forall \psi \in \mathcal{B}_{K, \vec{N}_{max}}, \quad c^\dagger_{(\nu, x)} \psi = B^\dagger_\nu(x) \psi \tag{14.9}
$$

**Corollary 14.9 (Emergent CAR Algebra).**
Because $B_\nu(x)$ and $c_{(\nu, x)}$ represent the exact same operator on the budget space, the complex bosonic exponentials trivially and exactly inherit the Canonical Anticommutation Relations. For any valid states on the budget:
$$
\{B_\nu(x), B^\dagger_{\nu'}(y)\} = \delta_{\nu\nu'} \delta_{xy} I \tag{14.10}
$$
There is no need to manually expand and normal-order the bosonic exponentials to prove the CAR algebra; it is structurally guaranteed.

#### 14.4 Technical Notes for the Lean 4 Formalization (Chapter 14)

1. **Defining the Zero-Mode via `Basis.constr`:**
   * To safely define $Z_\nu(x)$ without taking fractional powers of endomorphisms, we use the property established in Chapter 13 that the budget space is spanned by the joint partition states $\vert{}\vec{\lambda}; \vec{N}\rangle$.
   * We define a scalar evaluation function: `z_scalar (x : ℤ) (N_nu : ℤ) : ℂ := ω^(2 * x * N_nu - x)`, where `ω` is a fixed `2L`-th primitive root.
   * We then define $Z_\nu(x)$ as a `LinearMap` using `Basis.constr` that simply scales each basis vector by its corresponding `z_scalar`.

2. **Defining the Truncated Exponential:**
   * Do **not** use `Real.exp` or `Complex.exp` (which require analytic topology and infinite sums).
   * Define a computable algebraic function:
     `def truncated_exp (K : ℕ) (A : Module.End ℂ V) : Module.End ℂ V := ∑ j in Finset.range (K + 1), (1 / j.factorial) • A^j`
   * By Lemma 14.3, this finite sum is mathematically exact on the `BudgetSpace`.

3. **The "Smart" Proof Strategy (`span_induction` and Schur's Lemma):**
   * **Hazard:** Attempting to prove Theorem 14.7 by directly Taylor-expanding $\exp(W^-)\exp(W^+)$ and comparing it to the polynomial expansion of $c_{(\nu, x)}$ is a combinatorial nightmare.
   * **The Algebraic CFT Solution:** We leverage **Haldane Completeness** (Theorem 11.5) and the core logic of **Schur's Lemma**. Because the density modes generate an irreducible representation on the budget space via a cyclic vacuum state, any two operators that match on the vacuum and perfectly match the algebra's commutation relations must be identically equal everywhere.
   * **Step 1 (Ground State Equivalence):** Prove that $c_{(\nu, x)} \vert{}\vec{N}\rangle_0 = B_\nu(x) \vert{}\vec{N}\rangle_0$. (This reduces to evaluating the zero-mode $Z_\nu$ and the Klein factor $F_\nu$, as the exponential $\exp(W^+)$ collapses to 1 on the ground state).
   * **Step 2 (Commutator Matching):** Apply Lemma 14.5.
   * **Step 3 (`span_induction`):** In Lean, we implement this Schur's Lemma argument using `Submodule.span_induction`. If two linear maps agree on the vacuum, and they satisfy identical commutation relations with the operators that generate the entire basis, they are identically equal on the entire span.
