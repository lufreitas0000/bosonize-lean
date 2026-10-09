# BOSONIZE-LEAN: Mathematical Reference Notes
## Chapters 4 & 5: CAR Representation, Fock Space, and Lattice Fermions

---

### Chapter 4: CAR Representation and Fock Space

In algebraic quantum field theory, prior to mapping fermionic modes to spatial or momentum coordinates, we construct the algebra over a generic, abstract set of single-particle states.

Let $\iota$ be a finite, linearly ordered index set. The linear ordering is strictly necessary to unambiguously fix the phases acquired during fermionic anticommutation (analogous to fixing a Jordan–Wigner ordering string).

**Examples of $\iota$:**
1. A finite set of abstract modes $\iota = \{1, \dots, N\}$.
2. The discrete Brillouin zone $\Lambda^*$ (as used in Chapter 5).
3. A product space introducing internal degrees of freedom, such as chirality: $\iota = \{R, L\} \times \Lambda^*$ (lexicographically ordered).

---

#### 4.1 Algebraic and Functional Setting

To bridge abstract algebra to quantum states without resorting to unbounded topological spaces, we work in a finite-dimensional complex Hilbert space.

**Mathematical Background ($\ell^2$ Spaces and Adjoints):**
For any finite set $X$, the space $\ell^2(X)$ is the complex vector space of functions $f: X \to \mathbb{C}$, isomorphic to $\mathbb{C}^X$. It is equipped with the standard canonical inner product:

$$
\forall f, g \in \ell^2(X), \quad \langle f \mid g \rangle := \sum_{x \in X} \overline{f(x)} \, g(x) \tag{4.1}
$$

For any linear operator $A \in \mathrm{End}_{\mathbb{C}}(\ell^2(X))$, its adjoint $A^\dagger$ is the unique operator satisfying:

$$
\forall f, g \in \ell^2(X), \quad \langle f \mid A g \rangle = \langle A^\dagger f \mid g \rangle \tag{4.2}
$$

**Definition 4.1 (CAR Representation).**
Let $V$ be a complex Hilbert space. A Canonical Anticommutation Relations (CAR) representation over $\iota$ on $V$ is a pair of maps $c, c^\dagger : \iota \to \mathrm{End}_{\mathbb{C}}(V)$ such that for all $i, j \in \iota$:

$$
\{c_i, c_j\} = 0, \quad \{c_i^\dagger, c_j^\dagger\} = 0, \quad \{c_i, c_j^\dagger\} = \delta_{ij} I \tag{4.3}
$$

where $\{A, B\} := AB + BA$, $I$ is the identity endomorphism on $V$, and $c_i^\dagger = (c_i)^\dagger$ is the Hilbert space adjoint.

**Definition 4.2 (Fock Space and Basis).**
We define the concrete Fock space as the Hilbert space of complex-valued functions on the power set of $\iota$:

$$
\mathrm{Fock}(\iota) := \ell^2(\mathcal{P}(\iota)) \tag{4.4}
$$

For every subset $S \subseteq \iota$, the basis vector $\delta_S \in \mathrm{Fock}(\iota)$ is defined by the indicator function:

$$
\forall S' \subseteq \iota, \quad \delta_S(S') := \begin{cases} 1 & \text{if } S' = S \\ 0 & \text{if } S' \neq S \end{cases} \tag{4.5}
$$

The collection $\{\delta_S\}_{S \subseteq \iota}$ forms an orthonormal basis of $\mathrm{Fock}(\iota)$ with respect to the $\ell^2$ inner product:

$$
\forall S, S' \subseteq \iota, \quad \langle \delta_S \mid \delta_{S'} \rangle = \delta_{S, S'} \tag{4.6}
$$

Physically, $\delta_S$ represents the many-body state where exactly the single-particle modes in $S$ are occupied, and all modes in $\iota \setminus S$ are vacant.

**Example ($\iota = \{1, 2\}$):**
The power set is $\mathcal{P}(\iota) = \{\emptyset, \{1\}, \{2\}, \{1, 2\}\}$. The Fock space $\mathrm{Fock}(\iota)$ is 4-dimensional, spanned by:
- $\delta_\emptyset$: Vacuum state $\vert \Omega \rangle$ (no occupied modes).
- $\delta_{\{1\}}$: Mode 1 occupied, mode 2 empty.
- $\delta_{\{2\}}$: Mode 2 occupied, mode 1 empty.
- $\delta_{\{1, 2\}}$: Both modes occupied.

---

#### 4.2 Operators and Sign Mechanics

**Definition 4.3 (Fermionic Sign Function).**
For any mode $i \in \iota$ and any subset configuration $S \subseteq \iota$, the sign exponent $\sigma(i, S) \in \mathbb{N}$ counts the number of occupied modes strictly preceding $i$ in the total order of $\iota$:

$$
\sigma(i, S) := \#\{j \in S \mid j < i\} \tag{4.7}
$$

The creation and annihilation operators act on the orthonormal basis vectors as follows. For all $i \in \iota$ and all $S \subseteq \iota$:

$$
c_i^\dagger \delta_S := \begin{cases} (-1)^{\sigma(i, S)} \delta_{S \cup \{i\}} & \text{if } i \notin S \\ 0 & \text{if } i \in S \end{cases} \tag{4.8}
$$

$$
c_i \delta_S := \begin{cases} (-1)^{\sigma(i, S)} \delta_{S \setminus \{i\}} & \text{if } i \in S \\ 0 & \text{if } i \notin S \end{cases} \tag{4.9}
$$

**Definition 4.4 (Observables).**
For all $i \in \iota$:
1. **Local Mode Density Operator:** $n_i := c_i^\dagger c_i \in \mathrm{End}_{\mathbb{C}}(\mathrm{Fock}(\iota))$.
2. **Total Particle Number Operator:** $\hat{N}_{\mathrm{tot}} := \sum_{i \in \iota} n_i$.
3. **Global Parity Operator:** $\Gamma := \prod_{i \in \iota} (I - 2n_i)$.

---

#### 4.3 Fundamental Lemmas of the CAR Representation

**Lemma 4.5 (Dimension).**
The complex vector space dimension is finite and satisfies:

$$
\dim_{\mathbb{C}} \mathrm{Fock}(\iota) = 2^{\#\iota} \tag{4.10}
$$

**Lemma 4.6 (Atomic Sign Lemma).**
For any $i, j \in \iota$ and any subset $S \subseteq \iota$:
1. If $j \notin S$, then:
   $$
   \sigma(i, S \cup \{j\}) = \sigma(i, S) + \begin{cases} 1 & \text{if } j < i \\ 0 & \text{otherwise} \end{cases} \tag{4.11}
   $$
2. If $j \in S$, then:
   $$
   \sigma(i, S \setminus \{j\}) = \sigma(i, S) - \begin{cases} 1 & \text{if } j < i \\ 0 & \text{otherwise} \end{cases} \tag{4.12}
   $$
3. For $j = i$: $\sigma(i, S \cup \{i\}) = \sigma(i, S)$ and $\sigma(i, S \setminus \{i\}) = \sigma(i, S)$.

**Lemma 4.7 (Pure-CAR Commutator Identities).**
For all modes $a, b, c, d, k \in \iota$, the following identities hold in $\mathrm{End}_{\mathbb{C}}(\mathrm{Fock}(\iota))$:

$$
[c_a^\dagger c_b, c_c^\dagger c_d] = \delta_{bc} c_a^\dagger c_d - \delta_{ad} c_c^\dagger c_b \tag{4.13}
$$

$$
[n_k, c_a^\dagger] = \delta_{ka} c_a^\dagger, \quad [n_k, c_a] = -\delta_{ka} c_a \tag{4.14}
$$

**Lemma 4.8 (Hop Action).**
For any $a, b \in \iota$ and any configuration $S \subseteq \iota$:
If $b \in S$ and $a \notin S \setminus \{b\}$, then:

$$
c_a^\dagger c_b \delta_S = (-1)^{\sigma(b, S) + \sigma(a, S \setminus \{b\})} \delta_{(S \setminus \{b\}) \cup \{a\}} \tag{4.15}
$$

Otherwise, $c_a^\dagger c_b \delta_S = 0$. When $a = b$, the sign simplifies identically to $+1$.

---

#### 4.4 Technical Notes for the Lean 4 Formalization (Chapter 4)

1. **Typeclass Assumptions:**
   - Instead of general types, assume `[Fintype ι] [LinearOrder ι] [DecidableEq ι]`.
   - The linear order ensures that the decidability of `j < i` is available for `Finset.filter`.
2. **Representation of $\mathrm{Fock}(\iota)$:**
   - Modeled in Lean as `FockSpace (ι : Type) [Fintype ι] [DecidableEq ι] := Finset ι → ℂ`.
   - Use `Pi.basisFun ℂ (Finset ι)` to realize $\{\delta_S\}$ as a formal basis `Basis (Finset ι) ℂ (FockSpace ι)`.
   - To define operators $c_i$ and $c_i^\dagger$, avoid defining functions on the function type directly. Instead, specify the action on basis elements `Finset ι → FockSpace ι` and lift using `Basis.constr`. This automatically guarantees $\mathbb{C}$-linearity without manual proofs of additivity and scalar multiplication.
3. **Sign Arithmetic & Filter Lemmas:**
   - Define $\sigma(i, S)$ as `((S.filter (· < i)).card : ℕ)`.
   - Lemma 4.6 (Atomic Sign Lemma) requires `Finset.filter_insert` and `Finset.card_insert_of_not_mem`. Proving `(-1 : ℂ) ^ σ` properties reduces to tracking exponents modulo 2 (`Odd` / `Even` or integer powers).
4. **Inner Product & Adjointness:**
   - Endow `FockSpace ι` with the Euclidean inner product via `PiLp 2 (fun _ : Finset ι => ℂ)`.
   - Proving $c_i^\dagger = (c_i)^\dagger$ reduces to verifying $\langle \delta_T \mid c_i^\dagger \delta_S \rangle = \langle c_i \delta_T \mid \delta_S \rangle$ for all subsets $S, T \in \mathrm{Finset} \, \iota$, which factors into simple case analyses: $T = S \cup \{i\}$ versus $T \neq S \cup \{i\}$.

---
