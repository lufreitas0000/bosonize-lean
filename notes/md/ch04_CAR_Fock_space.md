# BOSONIZE-LEAN: Mathematical Reference Notes
## Chapters 4 & 5: CAR Representation, Fock Space, and Lattice Fermions

---

### Chapter 4: CAR Representation and Fock Space

In algebraic quantum field theory, prior to mapping fermionic modes to spatial or momentum coordinates, we construct the algebra over a generic, abstract set of single-particle states. The algebraic formalization strictly follows [Appendix A02](../appendices/a02_car_hilbert_and_normal_ordering.md) and is implemented in `Bosonize.A02` and `Bosonize.Ch04`.

Let $\iota$ be a finite, linearly ordered index set (`[Fintype ι] [LinearOrder ι]`). The linear ordering is strictly necessary to unambiguously fix the phases acquired during fermionic anticommutation.

**Canonical Examples of $\iota$:**

1. A finite set of abstract modes $\iota = \{1, \dots, N\}$.

2. The discrete Brillouin zone $\Lambda^*$ ordered as $\{-h+1, \dots, h\}$.

3. Spinful chiral fermions: $\iota = \{R, L\} \times \{\uparrow, \downarrow\} \times \Lambda^*$ endowed with lexicographic order to eliminate silent sign ambiguities.

---

#### 4.1 The Two-Tiered CAR Hierarchy: Algebraic vs. Hilbert Setting

To cleanly delineate between pure algebraic consequences and inner-product geometric properties, we establish a two-tiered definition:

**Definition 4.1a (Abstract Algebraic CAR — Tier 1).**
Let $V$ be any complex vector space (`[AddCommGroup V] [Module ℂ V]`). An Algebraic CAR representation over $\iota$ on $V$ (`Bosonize.A02.AlgebraicCAR`) consists of two families of linear operators $c, c^\dagger : \iota \to \mathrm{End}_{\mathbb{C}}(V)$ such that for all $i, j \in \iota$:
$$
\{c_i^{\phantom{\dagger}}, c_j^{\phantom{\dagger}}\} = 0, \quad \{c_i^\dagger, c_j^\dagger\} = 0, \quad \{c_i^{\phantom{\dagger}}, c_j^\dagger\} = \delta_{ij} I_V \tag{4.3}
$$
where $\{A, B\} := AB + BA$.

*Purely Algebraic Theorems (`A02.AlgebraicCAR`):*
Without requiring any inner product, Hilbert adjoints, or topological convergence, the algebraic anticommutators alone prove:

1. **Bilinear Commutator Identity (`car_bilinear_commutator`):**
   $$
   [c_a^\dagger c_b^{\phantom{\dagger}}, c_c^\dagger c_d^{\phantom{\dagger}}] = \delta_{bc} c_a^\dagger c_d^{\phantom{\dagger}} - \delta_{ad} c_c^\dagger c_b^{\phantom{\dagger}} \tag{4.3a}
   $$

2. **Number Commutators with Generators (`car_number_creation_commutator`, `car_number_annihilation_commutator`):**
   $$
   [n_i, c_j^\dagger] = \delta_{ij} c_j^\dagger, \qquad [n_i, c_j^{\phantom{\dagger}}] = -\delta_{ij} c_j^{\phantom{\dagger}} \tag{4.3b}
   $$
   where $n_i := c_i^\dagger c_i$.

3. **Number Idempotence & Commutativity (`car_number_idempotent`, `car_number_commute`):**
   $$
   n_i^2 = n_i, \qquad [n_i, n_j] = 0 \tag{4.3c}
   $$

**Definition 4.1b (Hilbert Space CAR Representation — Tier 2).**
Let $V$ be a finite-dimensional complex Euclidean space (`[NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]`). A full CAR representation (`Bosonize.A02.CAR`) is an `AlgebraicCAR` that additionally satisfies **Hilbert Adjoint Compatibility**:
$$
\forall i \in \iota, \quad c_i^\dagger = (c_i)^\dagger \tag{4.3d}
$$
where $(A)^\dagger$ is the unique operator satisfying $\langle f \mid A g \rangle = \langle A^\dagger f \mid g \rangle$.

*(Pedagogical Note on Conjugation: If $c, c^\dagger$ is an algebraic CAR pair and $S \in \mathrm{GL}(V)$ is an invertible operator, the similarity transform $\tilde{c}_i = S c_i S^{-1}, \tilde{c}_i^\dagger = S c_i^\dagger S^{-1}$ preserves all anticommutators $\{ \tilde{c}_i, \tilde{c}_j^\dagger \} = \delta_{ij} I$, but $\tilde{c}_i^\dagger \ne (\tilde{c}_i)^\dagger$ unless $S$ is unitary. Thus, adjointness is an essential, independent geometric requirement).*

---

#### 4.2 The Concrete Occupation Fock Space

**Definition 4.2 (Occupation Basis and State Carrier).**
For a finite index set $\iota$, the concrete Fock space is the Euclidean space indexed by the power set $\mathcal{P}(\iota) \equiv \mathrm{Finset} \ \iota$:
$$
\mathrm{FockSpace}(\iota) := \ell^2(\mathrm{Finset} \ \iota) \equiv \mathrm{EuclideanSpace} \ \mathbb{C} \ (\mathrm{Finset} \ \iota) \tag{4.4}
$$

- Dimension: $\dim_{\mathbb{C}}(\mathrm{FockSpace}(\iota)) = 2^{|\iota|}$ (`fock_finrank`).

- For every subset $S \subseteq \iota$, the indicator vector is denoted $\mathrm{ket}(S) \equiv |S\rangle = \delta_S$.

- Inner product: $\langle u \mid v \rangle = \sum_{S \subseteq \iota} \overline{u(S)} v(S)$ (`fock_inner`).

- Basis Orthonormality: $\langle \mathrm{ket}(S) \mid \mathrm{ket}(T) \rangle = \delta_{S, T}$ (`ket_inner`).

**Constructing Operators via Basis Extension (`A02.extendBasis`):**
Any endomorphism on $\mathrm{FockSpace}(\iota)$ can be constructed from its action on basis states using Lean's `Module.Basis.constr`:
$$
\mathrm{extendBasis}(F)\left(\sum_S v_S |S\rangle\right) := \sum_S v_S F(S) \tag{4.4a}
$$
satisfying $\mathrm{extendBasis}(F)(|S\rangle) = F(S)$ identically (`extend_basis_ket`).

---

#### 4.3 Operator Construction & Exact Sign Mechanics

**Definition 4.3 (Preceding Counts and Fermionic Signs).**
For any mode $i \in \iota$ and occupation subset $S \subseteq \iota$:

1. **Preceding Count (`precedingCount`):**
   $$
   \sigma(i, S) := \#\{j \in S \mid j < i\} = (S.\mathrm{filter}(\cdot < i)).\mathrm{card} \tag{4.5}
   $$

2. **Fermionic Phase Sign (`fermionSign`):**
   $$
   \epsilon(i, S) := (-1)^{\sigma(i, S)} \in \mathbb{C} \tag{4.5a}
   $$
   satisfying $\epsilon(i, S)^2 = 1$ and $\overline{\epsilon(i, S)} = \epsilon(i, S)$.

**Definition 4.3b (Concrete Annihilation & Creation Operators).**
Using `extendBasis`, we define `annihilation i` and `creation i` by:
$$
c_i |S\rangle := \begin{cases} \epsilon(i, S) |S \setminus \{i\}\rangle & \text{if } i \in S \\ 0 & \text{if } i \notin S \end{cases} \tag{4.6}
$$
$$
c_i^\dagger |S\rangle := \begin{cases} \epsilon(i, S) |S \cup \{i\}\rangle & \text{if } i \notin S \\ 0 & \text{if } i \in S \end{cases} \tag{4.7}
$$
*Special Cases:* Vacuum annihilation $c_i |\emptyset\rangle = 0$, single-particle creation $c_i^\dagger |\emptyset\rangle = |\{i\}\rangle$, and nilpotency $c_i^2 = (c_i^\dagger)^2 = 0$.

---

#### 4.4 Fundamental Lemmas: Atomic Counts and Sign Algebra

**Lemma 4.5 (Atomic Additive Counts, Avoiding Nat Underflow).**
To prevent truncation errors in natural number subtraction (`0 - 1 = 0`), all count updates are expressed strictly additively:

1. For $j \notin S$:
   $$
   \sigma(i, S \cup \{j\}) = \sigma(i, S) + \begin{cases} 1 & \text{if } j < i \\ 0 & \text{otherwise} \end{cases} \tag{4.8}
   $$

2. For $j \in S$:
   $$
   \sigma(i, S) = \sigma(i, S \setminus \{j\}) + \begin{cases} 1 & \text{if } j < i \\ 0 & \text{otherwise} \end{cases} \tag{4.9}
   $$

3. Self-invariance: $\sigma(i, S \cup \{i\}) = \sigma(i, S)$ and $\sigma(i, S \setminus \{i\}) = \sigma(i, S)$.

**Lemma 4.5b (Fermionic Sign Exchange Identities).**
For any distinct modes $i \ne j$:

1. **Creation Pair (`sign_insert_insert`):** For $i, j \notin S$:
   $$
   \epsilon(j, S) \epsilon(i, S \cup \{j\}) = - \epsilon(i, S) \epsilon(j, S \cup \{i\}) \tag{4.9a}
   $$

2. **Annihilation Pair (`sign_erase_erase`):** For $i, j \in S$:
   $$
   \epsilon(j, S) \epsilon(i, S \setminus \{j\}) = - \epsilon(i, S) \epsilon(j, S \setminus \{i\}) \tag{4.9b}
   $$

3. **Mixed Pair (`sign_insert_erase`):** For $i \notin S, j \in S$:
   $$
   \epsilon(j, S) \epsilon(i, S \setminus \{j\}) = - \epsilon(i, S) \epsilon(j, S \cup \{i\}) \tag{4.9c}
   $$
*Proof:* In each case, if $j < i$, inserting/erasing mode $j$ changes the number of elements preceding $i$ by exactly 1, multiplying the sign by $(-1)^1 = -1$. If $i < j$, the same logic applies symmetrically to $j$.

---

#### 4.5 Verification of the CAR Instantiation

**Lemma 4.6 (Adjointness and Concrete CAR Instantiation).**

1. **Basis Pairing Adjointness (`creation_adjoint_pairing`, `creation_eq_adjoint`):**
   For all basis states $|S\rangle, |T\rangle$:
   $$
   \langle |S\rangle \mid c_i^{\phantom{\dagger}} |T\rangle \rangle = \langle c_i^\dagger |S\rangle \mid |T\rangle \rangle \tag{4.10}
   $$
   Lifting via `A02.adjoint_of_basis_pairing` proves $c_i^\dagger = (c_i)^\dagger$ and $c_i = (c_i^\dagger)^\dagger$.

2. **Concrete Anticommutators (`annihilation_car`, `creation_car`, `mixed_car`):**
   Evaluating on any basis state $|S\rangle$ using the sign exchange lemmas yields:
   $$
   \{c_i^{\phantom{\dagger}}, c_j^{\phantom{\dagger}}\} = 0, \qquad \{c_i^\dagger, c_j^\dagger\} = 0, \qquad \{c_i^{\phantom{\dagger}}, c_j^\dagger\} = \delta_{ij} I
   $$

3. **Constructive Witness (`concrete_car_exists`):**
   Combining adjointness and anticommutators yields a constructive instance of `Bosonize.A02.CAR ι (FockSpace ι)`.

---

#### 4.6 Physical Observables, Parity, and Hopping

**Definition 4.7 (Observables and Parity Operator).**

1. **Local Number Operator:** $n_i := c_i^\dagger c_i$. On basis states:
   $$
   n_i |S\rangle = \begin{cases} 1 |S\rangle & \text{if } i \in S \\ 0 & \text{if } i \notin S \end{cases} \tag{4.11}
   $$
   satisfying $n_i^\dagger = n_i$, $n_i^2 = n_i$, and $[n_i, n_j] = 0$.

2. **Total Particle Number Operator:** $\hat{N}_{\mathrm{tot}} := \sum_{i \in \iota} n_i$. On basis states:
   $$
   \hat{N}_{\mathrm{tot}} |S\rangle = |S| \cdot |S\rangle \tag{4.12}
   $$
   satisfying $[\hat{N}_{\mathrm{tot}}, c_i^\dagger] = c_i^\dagger$ and $[\hat{N}_{\mathrm{tot}}, c_i] = -c_i$.

3. **Global Parity Operator $\Gamma$ (`Ch04.parity`):**
   Because operator multiplication in $\mathrm{End}_{\mathbb{C}}(V)$ is non-commutative, $\Gamma$ is defined by sorting the modes ascendingly (`Finset.sort (· ≤ ·) Finset.univ`):
   $$
   \Gamma := \prod_{i \in \mathrm{sort}(\le, \iota)} (I - 2 n_i) \tag{4.13}
   $$
   **Properties Proved in Lean:**
   - Action on states (`parity_ket`): $\Gamma |S\rangle = (-1)^{|S|} |S\rangle$.
   - Involution & Hermiticity (`parity_square`, `parity_adjoint`): $\Gamma^2 = I$ and $\Gamma^\dagger = \Gamma$.
   - Fermionic Grading Inversion (`parity_creation`, `parity_annihilation`):
     $$
     \Gamma c_i^{\phantom{\dagger}} = - c_i^{\phantom{\dagger}} \Gamma, \qquad \Gamma c_i^\dagger = - c_i^\dagger \Gamma \tag{4.14}
     $$

4. **Hopping Operator $T_{ij}$ (`Ch04.hopping`):**
   $$
   T_{ij} := c_i^\dagger c_j^{\phantom{\dagger}} \tag{4.15}
   $$
   - Diagonal action: $T_{ii} = n_i$.
   - Off-diagonal action on basis states ($i \ne j$):
     $$
     T_{ij} |S\rangle = \begin{cases} \epsilon(j, S) \epsilon(i, S \setminus \{j\}) |(S \setminus \{j\}) \cup \{i\}\rangle & \text{if } j \in S \text{ and } i \notin S \\ 0 & \text{otherwise} \end{cases} \tag{4.16}
     $$
   - Adjoint identity: $T_{ij}^\dagger = (c_i^\dagger c_j)^\dagger = c_j^\dagger c_i = T_{ji}$ (`hopping_adjoint`).
   - Commutator algebra: derived from Lemma 4.1a (`bilinear_commutator`):
     $$
     [T_{ab}, T_{cd}] = \delta_{bc} T_{ad} - \delta_{ad} T_{cb} \tag{4.17}
     $$
     which forms the exact Lie algebra of $\mathfrak{u}(|\iota|)$, providing the foundation for the upcoming density mode algebra.
