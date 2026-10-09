# BOSONIZE-LEAN: Mathematical Reference Notes

## Part III: Phase 3 The Bosonization Dictionary

### Chapter 13: Klein Factors & Multi-Species Fermions

To achieve the full bosonization dictionary, we must reconstruct the physical fermionic field operator $\psi(x)$ entirely out of bosonic components.
There is a fundamental obstruction: bosonic density modes $\rho_{m, \nu}$ destroy one fermion and create one fermion, strictly conserving the total particle number of that species. They can only map states within the same charge sector. However, the true operator $\psi(x)$ removes one particle, mapping a state in sector $\vec{N}$ to sector $\vec{N}-e_\nu$ (where $e_\nu$ is the unit vector for species $\nu$).

To fix this, we must factorize the fermionic field into two parts:

1. A **bosonic exponential** that handles the density fluctuations (particle-hole excitations) within a fixed sector.

2. A **Klein factor** $F_\nu$ that acts as a ladder operator, formally shifting the system from one charge sector to another while correctly tracking the cross-species fermionic statistics.

#### 13.1 Multi-Species Index and the Vacuum

In models with internal degrees of freedom (like spin, valleys, or 1D chirality/branches), we upgrade our index set to include a species label.

**Definition 13.1 (Multi-Species Index).**
Let $\mathcal{C}$ be a finite, strictly ordered index set of species (where $M = \#\mathcal{C}$). The total single-particle index set is the Cartesian product:

$$
\iota := \mathcal{C} \times \Lambda^* \tag{13.1}
$$

The total index set $\iota$ is ordered lexicographically: $(\nu, k) < (\nu', p)$ if and only if $\nu < \nu'$, or ($\nu = \nu'$ and $k < p$). As established in Chapter 4, this strict linear ordering uniquely and safely defines the Canonical Anticommutation Relations (CAR) over the extended Fock space $\mathrm{Fock}(\iota)$.

**Definition 13.2 (Joint Sector Ground States).**
Let $\vec{N} \in \mathbb{Z}^M$ be a vector of relative charges for each species. The joint vacuum state and joint sector ground states are given by the tensor product of the independent species ground states:

$$
\vert{}\vec{N}\rangle_0 := \bigotimes_{\nu \in \mathcal{C}} \vert{}N_\nu\rangle_0 \tag{13.2}
$$

**Definition 13.3 (Species Density Modes).**
The unnormalized density operator is generalized to act strictly within its own species branch. For any $\nu \in \mathcal{C}$ and $m \in \mathbb{Z}$:

$$
\rho_{m, \nu} := \sum_{\substack{k \in \Lambda^* \\ k+m \in \Lambda^*}} c^\dagger_{(\nu, k+m)} c_{(\nu, k)} \tag{13.3}
$$

Because these operators act on disjoint indices, density modes of different species strictly commute everywhere on the Fock space: $[\rho_{m, \nu}, \rho_{n, \nu'}] = 0$ for $\nu \neq \nu'$.

#### 13.2 The Klein Factors

A naive ladder operator that maps $\vert{}N_\nu\rangle \mapsto \vert{}N_\nu - 1\rangle$ would commute with operators from other species. However, true fermionic operators from species $\nu$ must *anticommute* with operators from species $\nu'$. To enforce this, the Klein factor must be "dressed" with a parity sign depending on the total particle occupation of all preceding species in the ordered set $\mathcal{C}$.

**Definition 13.4 (Klein Factors on the Haldane Basis).**
For each species $\nu \in \mathcal{C}$, the Klein factor $F_\nu$ and its adjoint $F_\nu^\dagger$ are defined constructively by their action on the joint bosonic partition basis (the Haldane basis) $\vert{}\vec{\lambda}; \vec{N}\rangle$:

$$
F_\nu \vert{}\lambda^{(1)}, \dots, \lambda^{(M)}; N_1, \dots, N_\nu, \dots, N_M\rangle := (-1)^{\sum_{\eta < \nu} N_\eta} \vert{}\lambda^{(1)}, \dots, \lambda^{(M)}; N_1, \dots, N_\nu - 1, \dots, N_M\rangle \tag{13.4}
$$

$$
F_\nu^\dagger \vert{}\lambda^{(1)}, \dots, \lambda^{(M)}; N_1, \dots, N_\nu, \dots, N_M\rangle := (-1)^{\sum_{\eta < \nu} N_\eta} \vert{}\lambda^{(1)}, \dots, \lambda^{(M)}; N_1, \dots, N_\nu + 1, \dots, N_M\rangle \tag{13.5}
$$

Because the Klein factor strictly preserves the integer partitions $\lambda^{(\eta)}$ acting as a pure spectator on the bosonic excitations, it commutes exactly with all species density modes by definition:

$$
\forall m \in \mathbb{Z}, \forall \nu, \nu' \in \mathcal{C}, \quad [F_\nu, \rho_{m, \nu'}] = 0 \tag{13.6}
$$

#### 13.3 Algebraic and Geometric Interpretations

Before establishing the strict budget projections, it is highly illuminating to recognize the deep mathematical structures that the Klein factors embody. They are not mere algebraic tricks; they are manifestations of fundamental concepts in representation theory and algebra.

1. **Representation Theory (Intertwining Operators and Isomorphisms):**
   The density modes $\rho_{m, \nu}$ generate a $U(1)$ Kac-Moody algebra. However, they cannot change the total charge $N_\nu$. Therefore, each distinct charge sector $\vec{N}$ forms an isolated, disjoint, irreducible representation of this algebra (a "superselection sector").
   Mathematically, for a fixed energy budget $K$, $F_\nu$ establishes a strict vector space isomorphism between the fixed-energy subspaces of adjacent charge sectors:

   $$
   F_\nu : \mathcal{H}^{\vec{N}}_K \xrightarrow{\sim} \mathcal{H}^{\vec{N}-e_\nu}_K \tag{13.7}
   $$

   Because it commutes with all density modes ($F_\nu \rho_{m, \nu'} = \rho_{m, \nu'} F_\nu$), it preserves the action of the Kac-Moody algebra perfectly. In representation theory, an operator $T$ satisfying $T \pi_1(x) = \pi_2(x) T$ is an **intertwining operator**. $F_\nu$ intertwines the disjoint representation spaces, bridging them into a unified fermionic algebra.

2. **Clifford Algebras and Spinors:**
   As we will prove below, the Klein factors anti-commute across different species: $\{F_\nu, F_{\nu'}\} = 0$. This means the set of Klein factors $\{F_\nu, F_\nu^\dagger\}$ generates a finite-dimensional **Clifford Algebra**.
   Consequently, the manifold of joint vacuum states (the set of all $\vert{}\vec{N}\rangle_0$) forms a **Spinor Module** for this Clifford algebra. The Klein factors act as Dirac gamma matrices rotating the vacuum state through this spinorial target space.

3. **Algebraic Topology (2-Cocycles and Twisted Algebras):**
   Why does the formula contain the highly specific sign dressing $(-1)^{\sum_{\eta < \nu} N_\eta}$?
   If we naively took the tensor product of the species, they would commute. In the language of cohomology, to convert a commutative tensor product algebra into a graded anti-commutative algebra, we must twist the multiplication using a **2-cocycle**. The parity sign explicitly realizes this 2-cocycle, mathematically twisting the disjoint bosonic algebras back into a unified fermionic CAR algebra.

#### 13.4 Exact Algebraic Properties and Subspace Constraints

**Physical Intuition (Majorana-like vs. Fermionic):**
Are Klein factors fermions? No. While they anti-commute with each other across *different* species to fix the statistics, their repeated action on the *same* species does not yield zero. Because $F_\nu$ lowers the sector from $N$ to $N-1$, applying it twice yields sector $N-2$. They are unitary shift operators (sometimes called "hard-core bosons" or "Majorana-like" operators).

In our strict finite-dimensional formalization, exact unitarity ($F F^\dagger = I$) fails at the absolute edges of the band. If $N_\nu = -h$, we cannot remove a particle; if $N_\nu = h$, we cannot add one. Therefore, the unitarity identities must be strictly formulated using budget subspace boundaries.

**Definition 13.5 (Multi-Species Budget Projection).**
Let $\mathcal{B}_{K, \vec{N}_{max}}$ be the multi-species budget subspace where the total excitation energy is bounded by $K$ and the charge of *each* species is strictly bounded: $\forall \nu, \vert{}N_\nu\vert{} \le N_{max}$. Let $P_{\mathcal{B}}$ be the orthogonal projection operator onto this subspace.

**Lemma 13.6 (Klein Factor Algebra).**
The Klein factors form a strict Clifford-like algebra on the budget.

1. **Exact Partial Unitarity on the Budget:**
   If the bounding box avoids the absolute band edges ($N_{max} < h$), then the operators act as exact mutual inverses on the subspace. As identities in $\mathrm{End}_{\mathbb{C}}(\mathrm{Fock}(\iota))$:

   $$
   F_\nu F_\nu^\dagger P_{\mathcal{B}} = P_{\mathcal{B}} \tag{13.8}
   $$

   $$
   F_\nu^\dagger F_\nu P_{\mathcal{B}} = P_{\mathcal{B}} \tag{13.9}
   $$

2. **Global Intra-species Commutators:**

   $$
   [F_\nu, F_\nu] = 0, \quad [F_\nu^\dagger, F_\nu^\dagger] = 0 \tag{13.10}
   $$

3. **Global Cross-species Anti-commutators:**
   If $\nu \neq \nu'$, the exact global identities hold on the entire Fock space:

   $$
   \{F_\nu, F_{\nu'}\} = 0, \quad \{F_\nu^\dagger, F_{\nu'}^\dagger\} = 0, \quad \{F_\nu^\dagger, F_{\nu'}\} = 0 \tag{13.11}
   $$

**Lemma 13.7 (Global Number Shifting).**
Because $F_\nu$ removes exactly one particle from branch $\nu$ and leaves all other branches untouched, its commutator with the number operators $\hat{N}_{\nu'}$ is exactly scalar:

$$
[F_\nu, \hat{N}_{\nu'}] = \delta_{\nu, \nu'} F_\nu, \quad [F_\nu^\dagger, \hat{N}_{\nu'}] = -\delta_{\nu, \nu'} F_\nu^\dagger \tag{13.12}
$$

#### 13.5 Technical Notes for the Lean 4 Formalization (Chapter 13)

1. **Finiteness of the Multi-Species Budget in Lean:**

   * Will Lean happily accept that this subspace is finite? Yes, but through a specific typeclass route. The total underlying Hilbert space `FockSpace (C × LambdaDual L)` has complex dimension $2^{\#C \times L}$.

   * By instantiating `[FiniteDimensional ℂ (FockSpace ι)]`, Lean's linear algebra library guarantees that *any* `Submodule` of this space is automatically finite-dimensional. We do not need to manually prove the dimension of the multi-species budget to satisfy finiteness criteria.

2. **Defining the Projectors vs. Using Subtype Constraints:**

   * The text uses $P_{\mathcal{B}}$ (orthogonal projection). To define this strictly in Lean requires upgrading the vector space to an `InnerProductSpace` and relying on `orthogonalProjection`. This carries heavy analytical baggage.

   * **The Lean Architect Strategy:** It is far more idiomatic and computationally clean to state partial unitarity without projectors, using vectors bundled into the Submodule types. We define $F_\nu$ as a map between specific submodules:
     `F_nu : BudgetSpace K N_vec →ₗ[ℂ] BudgetSpace K (N_vec - e_nu)`

   * We formulate Partial Unitarity (Lemma 13.6.1) cleanly as an exact identity on the subtype:
     `∀ (ψ : BudgetSpace K N_vec) (h_margin : N_vec.nu < h), F_nu_dag (F_nu ψ) = ψ`

   * This completely sidesteps explicit matrix projectors, relying instead on Lean's powerful `LinearMap` and `LinearEquiv` (`≃ₗ[ℂ]`) API. It enforces the domain restriction at the type level, making impossible states (like pushing past the band edge) unrepresentable rather than relying on operators evaluating to zero.

3. **Defining the Klein Factor via `Basis.constr`:**

   * How do we formalize Definition 13.4 natively? We use Mathlib's `Basis.constr`. Because we proved in Chapter 11 (Theorem 11.5) that the Haldane partition states form an exact basis for the Budget Subspace, we feed this basis into `Basis.constr` to define $F_\nu$ as a linear map.

   * We specify its action on the basis elements as `(-1)^(sum) • |λ, N - e_nu>`. Lean automatically extends this to a rigorously linear endomorphism.

   * **Massive Advantage:** Because it is defined this way, proving that it commutes with the bosonic modes $\rho_m$ is trivial by definition. The $\rho_m$ operators act strictly on the $\lambda$ partitions, and $F_\nu$ acts strictly on the $N$ labels.

4. **Lexicographical Index (`ι := C × LambdaDual L`):**

   * Do **not** attempt to manually code the $(-1)^{\sum N_\eta}$ signs in the CAR commutators of the raw space.

   * By defining `ι` as the Cartesian product and providing Lean with `[LinearOrder C]`, the `Prod.lex` order handles the cross-species anti-commutation organically when the fundamental fermions $c^\dagger_{(\nu, k)}$ are evaluated.

   * The explicit signs in Definition 13.4 are required *only* because $F_\nu$ acts macroscopically on the Haldane basis, skipping over the underlying individual fermions.

5. **Proving Cross-Species Anti-commutation (`{F_nu, F_eta} = 0`):**

   * Prove this by evaluating the action of $(F_\nu F_\eta + F_\eta F_\nu)$ on an arbitrary joint basis state $\vert{}\vec{\lambda}; \vec{N}\rangle$.

   * Assume without loss of generality that $\nu < \eta$.

   * $F_\nu F_\eta$ evaluates the sign for $\eta$ *before* $\nu$ lowers its charge.

   * $F_\eta F_\nu$ evaluates the sign for $\eta$ *after* $\nu$ lowers its charge, which causes $\sum_{\gamma < \eta} N_\gamma$ to drop by exactly 1, flipping the parity.

   * The sum of the two operators therefore evaluates exactly to the zero vector. By `Basis.ext`, the operators strictly anti-commute globally.
