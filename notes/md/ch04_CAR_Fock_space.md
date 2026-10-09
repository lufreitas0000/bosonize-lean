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
Let $V$ be a finite-dimensional complex Euclidean space. A Canonical Anticommutation Relations (CAR) representation over a finite index set $\iota$ on $V$ is a pair of maps $c, c^\dagger : \iota \to \mathrm{End}_{\mathbb{C}}(V)$ such that:
1. **Adjoint Compatibility:** For all $i \in \iota$, $c_i^\dagger = (c_i)^\dagger$ is the actual Hilbert adjoint of $c_i$.
2. **Anticommutation Relations:** For all $i, j \in \iota$:

$$
\{c_i, c_j\} = 0, \quad \{c_i^\dagger, c_j^\dagger\} = 0, \quad \{c_i, c_j^\dagger\} = \delta_{ij} I \tag{4.3}
$$

where $\{A, B\} := AB + BA$ and $I$ is the identity endomorphism.

*(Note: The three anticommutation relations alone are purely algebraic; conjugating an algebraic CAR pair by a non-unitary invertible operator preserves the anticommutators while destroying Hilbert adjointness. Adjoint compatibility is therefore an essential, independent requirement).*

*Lean 4 Proof Strategy:*
Define this as a structure `CAR (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (ι : Type) [Fintype ι]`. The fields are `c, cdag : ι → Module.End ℂ V`, an adjoint field `adj_compat : ∀ i, cdag i = LinearMap.adjoint (c i)`, and three anticommutator equations: `c i * c j + c j * c i = 0`, `cdag i * cdag j + cdag j * cdag i = 0`, and `c i * cdag j + cdag j * c i = (if i = j then 1 else 0) • 1`. Restricting to finite-dimensional Euclidean $V$ ensures every linear map admits a well-defined Hilbert adjoint.

**Definition 4.2 (Fock Space and Basis).**
We define the concrete Fock space as the Euclidean space over the power set of $\iota$:

$$
\mathrm{Fock}(\iota) := \ell^2(\mathcal{P}(\iota)) \tag{4.4}
$$

For every subset $S \subseteq \iota$, the basis vector $\delta_S \in \mathrm{Fock}(\iota)$ is the indicator function. The collection $\{\delta_S\}_{S \subseteq \iota}$ forms an exact orthonormal basis.

*Lean 4 Proof Strategy:*
Define `FockSpace ι := EuclideanSpace ℂ (Finset ι)`, with `[Fintype ι]` and the order/decidable equality needed by occupations. Use the checked `EuclideanSpace.basisFun (Finset ι) ℂ`; its `.toBasis` supplies the algebraic occupation basis.

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

*Lean 4 Proof Strategy:*
Define the preceding occupation count with `Finset.filter`. Specify the image of each occupation basis vector, then construct `c i` and `cdag i` using `Module.Basis.constr`. Prove their evaluation lemmas first. `Module.Basis.ext` proves equality of existing maps; it does not construct a map.

**Definition 4.4 (Observables).**
For all $i \in \iota$:
1. **Local Mode Density Operator:** $n_i := c_i^\dagger c_i$.
2. **Total Particle Number Operator:** $\hat{N}_{\mathrm{tot}} := \sum_{i \in \iota} n_i$.
3. **Global Parity Operator:** $\Gamma := \overrightarrow{\prod}_{i \in \iota} (I - 2n_i)$. (An explicit ordered product is required because generic endomorphisms are noncommutative).

*Lean 4 Proof Strategy:*
Define `def n (i : ι) : Module.End ℂ (FockSpace ι) := cdag i * c i`. The total particle number is simply `def N_tot := ∑ i : ι, n i` using `Finset.sum`. For the global parity operator $\Gamma$, since endomorphisms generally do not commute, we need an ordered product. We can map `Finset.univ` to a sorted list `List.prod` using the `LinearOrder ι`: `def Gamma := (Finset.sort (· ≤ ·) Finset.univ).map (fun i => 1 - 2 * n i) |>.prod`. We will need an auxiliary lemma showing that $n_i$ and $n_j$ actually commute, meaning the ordering is technically arbitrary, but defining it with a fixed order is safer.

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

*Lean 4 Proof Strategy:*
Prove these lemmas using `Finset.filter_insert` and `Finset.card_insert_of_not_mem`. For the first part ($j \notin S$), substituting $S \cup \{j\}$ translates to `insert j S`. Filtering by `< i` distributes over `insert`. If `j < i`, it adds `1` to the cardinality, otherwise `0`. The second part is symmetrical; we can apply the first part with $S \setminus \{j\}$ in place of $S$, noting that `insert j (S \ {j}) = S` since $j \in S$. These will be very clean, `simp`-friendly integer math lemmas.

**Lemma 4.6 (Adjointness, CAR Instantiation, and Parity).**
The operations at distinct modes commute as set operations but flip the combined sign exactly according to the CAR. Evaluated on the basis pairs and lifted by finite sums:
1. $c_i^\dagger$ and $c_i$ are exact Hilbert adjoints: $c_i^\dagger = (c_i)^\dagger$.
2. The concrete operators satisfy all three CAR anticommutation identities (4.3).
Consequently, the concrete occupation operators constructively instantiate the abstract CAR representation of Definition 4.1.
Furthermore, the number operators commute pairwise, $\Gamma^2 = I$, and $\Gamma^\dagger = \Gamma$.

*Lean 4 Proof Strategy:*
1. **Adjointness**: Prove `⟪δ_S, c i δ_T⟫_ℂ = ⟪cdag i δ_S, δ_T⟫_ℂ` for all basis vectors $S, T$. Using the linearity of the inner product and `PiLp` EuclideanSpace properties, extend this via `Module.Basis.ext` to prove `c i` and `cdag i` are adjoints.
2. **CAR Identities**: Prove `{c i, c j} = 0`, `{cdag i, cdag j} = 0`, and `{c i, cdag j} = δ_ij I` directly from the atomic sign lemmas (Lemma 4.5).
3. **CAR Instantiation**: Combine adjointness and the CAR identities into an explicit `CAR (FockSpace ι) ι` instance.
4. **Commutativity of $n$**: Show `n i * n j = n j * n i` by applying the CAR anticommutation identities.
5. **Parity**: For $\Gamma^2 = I$, use `lemma n_sq_eq_n (i : ι) : n i * n i = n i`. Then `(1 - 2 * n i)^2 = 1 - 4 * n i + 4 * n i^2 = 1`. Since the $n_i$ commute, the product squared is the product of squares, giving $I$. The self-adjointness $\Gamma^\dagger = \Gamma$ follows from $n_i^\dagger = n_i$.

**Lemma 4.7 (Pure-CAR Commutator Identities).**
Derived directly and algebraically from the CAR representation without assuming topology:

$$
[c_a^\dagger c_b, c_c^\dagger c_d] = \delta_{bc} c_a^\dagger c_d - \delta_{ad} c_c^\dagger c_b \tag{4.10}
$$

$$
[n_k, c_a^\dagger] = \delta_{ka} c_a^\dagger, \quad [n_k, c_a] = -\delta_{ka} c_a \tag{4.11}
$$

These exact bilinear commutators form the necessary foundation for the density algebra.

*Lean 4 Proof Strategy:*
Prove the pure CAR bilinear identities by distributivity and the CAR equations in a fixed factor order. Symmetric swap rules are not safe unconditional simp lemmas. If a normal-order procedure is added, give it a fixed word order and a decreasing measure; use its checked evaluation-preservation theorem.
