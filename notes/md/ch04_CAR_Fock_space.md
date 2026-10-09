# BOSONIZE-LEAN: Mathematical Reference Notes
## Chapters 4 & 5: CAR Representation, Fock Space, and Lattice Fermions

---

### Chapter 4: CAR Representation and Fock Space

In algebraic quantum field theory, prior to mapping fermionic modes to spatial or momentum coordinates, we construct the algebra over a generic, abstract set of single-particle states. The algebraic formalization strictly follows [Appendix A02](../appendices/a02_car_hilbert_and_normal_ordering.md).

Let $\iota$ be a finite, linearly ordered index set. The linear ordering is strictly necessary to unambiguously fix the phases acquired during fermionic anticommutation.

**Examples of $\iota$:**
1. A finite set of abstract modes $\iota = \{1, \dots, N\}$.
2. The discrete Brillouin zone $\Lambda^*$.
3. A product space introducing internal degrees of freedom: $\iota = \{R, L\} \times \Lambda^*$ (lexicographically ordered to avoid silent phase ambiguity).

---

#### 4.1 Algebraic and Functional Setting

To bridge abstract algebra to quantum states without resorting to unbounded topological spaces, we work in a finite-dimensional complex Euclidean space.

**Mathematical Background (Euclidean Space):**
For any finite set $X$, the space $\ell^2(X)$ is the complex vector space equipped with the standard canonical inner product. To avoid conflating the standard product norm with the Euclidean norm, we explicitly use `EuclideanSpace ℂ X` (or equivalent matrix conjugate-transpose algebra) to formally define adjoints.

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

where $\{A, B\} := AB + BA$ and $I$ is the identity endomorphism.

**Definition 4.2 (Fock Space and Basis).**
We define the concrete Fock space as the Euclidean space over the power set of $\iota$:

$$
\mathrm{Fock}(\iota) := \ell^2(\mathcal{P}(\iota)) \tag{4.4}
$$

For every subset $S \subseteq \iota$, the basis vector $\delta_S \in \mathrm{Fock}(\iota)$ is the indicator function. The collection $\{\delta_S\}_{S \subseteq \iota}$ forms an exact orthonormal basis.

---

#### 4.2 Operators and Sign Mechanics

**Definition 4.3 (Fermionic Sign Function).**
For any mode $i \in \iota$ and subset $S \subseteq \iota$, the sign exponent $\sigma(i, S) \in \mathbb{N}$ counts the occupied modes strictly preceding $i$:

$$
\sigma(i, S) := \#\{j \in S \mid j < i\} \tag{4.5}
$$

The creation and annihilation operators act on the orthonormal basis vectors exactly as:

$$
c_i^\dagger \delta_S := \begin{cases} (-1)^{\sigma(i, S)} \delta_{S \cup \{i\}} & \text{if } i \notin S \\ 0 & \text{if } i \in S \end{cases} \tag{4.6}
$$

$$
c_i \delta_S := \begin{cases} (-1)^{\sigma(i, S)} \delta_{S \setminus \{i\}} & \text{if } i \in S \\ 0 & \text{if } i \notin S \end{cases} \tag{4.7}
$$
These basis actions are then linearly extended to $\mathrm{End}_{\mathbb{C}}(\mathrm{Fock}(\iota))$.

**Definition 4.4 (Observables).**
For all $i \in \iota$:
1. **Local Mode Density Operator:** $n_i := c_i^\dagger c_i$.
2. **Total Particle Number Operator:** $\hat{N}_{\mathrm{tot}} := \sum_{i \in \iota} n_i$.
3. **Global Parity Operator:** $\Gamma := \overrightarrow{\prod}_{i \in \iota} (I - 2n_i)$. (An explicit ordered product is required because generic endomorphisms are noncommutative).

---

#### 4.3 Fundamental Lemmas of the CAR Representation

**Lemma 4.5 (Atomic Sign Lemma).**
To avoid natural number truncated subtraction (which is problematic to invert algebraically), we state the erasure count strictly in additive form.
For any $i, j \in \iota$ and subset $S \subseteq \iota$:
1. If $j \notin S$:
   $$
   \sigma(i, S \cup \{j\}) = \sigma(i, S) + \begin{cases} 1 & \text{if } j < i \\ 0 & \text{otherwise} \end{cases} \tag{4.8}
   $$
2. If $j \in S$:
   $$
   \sigma(i, S) = \sigma(i, S \setminus \{j\}) + \begin{cases} 1 & \text{if } j < i \\ 0 & \text{otherwise} \end{cases} \tag{4.9}
   $$

**Lemma 4.6 (Adjointness and Parity).**
The operations at distinct modes commute as set operations but flip the combined sign exactly according to the CAR. Evaluated on the basis pairs and lifted by finite sums, $c_i^\dagger$ and $c_i$ are exact Hilbert adjoints.
Furthermore, the number operators commute pairwise, $\Gamma^2 = I$, and $\Gamma^\dagger = \Gamma$.

**Lemma 4.7 (Pure-CAR Commutator Identities).**
Derived directly and algebraically from the CAR representation without assuming topology:

$$
[c_a^\dagger c_b, c_c^\dagger c_d] = \delta_{bc} c_a^\dagger c_d - \delta_{ad} c_c^\dagger c_b \tag{4.10}
$$

$$
[n_k, c_a^\dagger] = \delta_{ka} c_a^\dagger, \quad [n_k, c_a] = -\delta_{ka} c_a \tag{4.11}
$$

These exact bilinear commutators form the necessary foundation for the density algebra.
