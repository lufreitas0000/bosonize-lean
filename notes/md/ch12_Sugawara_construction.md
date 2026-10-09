
### Chapter 12: Algebraic Equivalence of Energy Observables (The Sugawara Construction)

**Physical and Algebraic Motivation:**
It is natural to think of the Hamiltonian strictly as the generator of time evolution (Dynamics). If so, why introduce it now, while we are still establishing the kinematic/algebraic foundations?
In the context of bosonization and Conformal Field Theory, the Sugawara construction is fundamentally a **structural, kinematic identity**. We are asking a purely algebraic question: *Can the observable that measures fermionic energy be constructed entirely out of bosonic density blocks?*
We are not looking at time evolution yet. We are proving that the energy operator $\hat{E}$ is algebraically equivalent to a specific quadratic sum of density modes on the budget subspace. This proves that the low-energy physics is truly, structurally bosonic.

#### 12.1 Definitions and Normal Ordering

**Physical Intuition for Normal Ordering Bosons:**
When constructing the bosonic energy observable, we must sum the energies of all individual density waves: $H_{sug} \propto \sum \rho_{-m} \rho_m$. However, we must be careful with operator ordering. Because $[\rho_{-m}, \rho_m] = m$, placing the annihilator on the right ($\rho_m \rho_{-m}$) differs from placing it on the left ($\rho_{-m} \rho_m$) by an additive constant $m$.
If we used the wrong order, summing over all modes would yield a mathematically infinite zero-point energy shift $\sum_{m=1}^\infty m$. To prevent this, bosonic normal ordering dictates that **creation operators must strictly sit on the left**. Because $\rho_m$ for $m > 0$ creates energy, $\rho_m$ must be on the left.

**Definition 12.1 (Bosonic Sugawara Hamiltonian).**
The Sugawara kinetic energy operator is defined as the normal-ordered sum of density bilinears:

$$
H_{\text{sug}} := \sum_{m=1}^{h-1} \rho_m \rho_{-m} \tag{12.1}
$$

*(Note: The upper limit* $h-1$ *spans all valid modes. In practice, acting on the budget space* $\mathcal{B}^N_K$*, any term where* $m > K$ *will identically annihilate the state, acting as an effective natural cutoff).*

#### 12.2 The Equivalence Theorem

**Physical Intuition for the Equivalence Proof:**
Attempting to prove the Sugawara construction by directly expanding the infinite sum of four-fermion operators and algebraically canceling terms is a combinatorial nightmare. Instead, we use a powerful representation-theoretic approach relying on the basis we just built.
We define a difference operator $D = \hat{E} - H_{\text{sug}}$. We show that $D$ acts as zero on the ground state. Then, we show that $D$ commutes with every density mode. This implies that $D$ must also act as zero on *every* partition state constructed from the ground state. Because the partition states completely span the budget subspace (Haldane Completeness), $D$ must be the exact zero matrix on that subspace.

**Recall the Fermionic Excitation Energy (**$\hat{E}$**):**
From Definition 7.5, $\hat{E}$ is the operator that measures the exact excitation energy above the sector ground state. It is defined by removing the ground-state energy shift from the normal-ordered free Hamiltonian: $\hat{E} := \ :\!H_0\!: - \frac{1}{2}\hat{N}(\hat{N}+1)I$.

**Lemma 12.2 (Commutation with the Modes).**
Under the R2 Margin condition, the Sugawara Hamiltonian correctly measures and shifts the energy of a density mode. For any non-zero mode $n$:

$$
\forall \psi \in \mathcal{B}^N_K, \quad [H_{\text{sug}}, \rho_n] \psi = n \rho_n \psi \tag{12.2}
$$

**Theorem 12.3 (Sugawara Equivalence on the Budget).**
Under the R2 Margin condition ($2K + \vert{}N\vert{} \le h$), the true fermionic excitation energy operator $\hat{E}$ is algebraically identical to the bosonic Sugawara Hamiltonian when acting on the budget subspace:

$$
\forall \psi \in \mathcal{B}^N_K, \quad \hat{E} \psi = H_{\text{sug}} \psi \tag{12.3}
$$

Equivalently, substituting the definition of the excitation energy $\hat{E}$, the full free fermionic Hamiltonian evaluates to:

$$
\forall \psi \in \mathcal{B}^N_K, \quad :\!H_0\!: \psi = \left( H_{\text{sug}} + \frac{1}{2}\hat{N}(\hat{N}+1)I \right) \psi \tag{12.4}
$$

*(Note: The zero-mode shift is explicitly* $\frac{1}{2}N(N+1)$*, which arises from the asymmetric Fermi level at 0. It must not be symmetrized to* $\frac{1}{2}N^2$*.)*

#### 12.3 Technical Notes for the Lean 4 Formalization (Chapters 11 & 12)

1. **Mathlib Partitions API:**
   * Lean 4's Mathlib has a dedicated API for integer partitions: `Mathlib.Combinatorics.Partition`.
   * Specifically, `Nat.Partition.partitions K` generates the `Finset` of all valid partitions.
   * To map a partition to a state, use `Partition.parts` (which is a `Multiset ℕ`) and map over it to apply the corresponding $\rho_m$ operators to the ground state. E.g., `Multiset.prod (parts.map fun m => density_mode m) |N>_0`.

2. **Proving Orthogonality and the Hall Inner Product "The Smart Way":**
   * To prove linear independence (Lemma 11.4), calculate the inner product $\langle \lambda; N \mid \mu; N \rangle$.
   * While this norm evaluates exactly to the Hall inner product normalization $z_\lambda$ from symmetric function theory, **do not import Mathlib's heavy symmetric polynomial libraries**. The Lean formalization should stay lean.
   * *The Lean Strategy:* Keep the proof strictly internal to the CAR algebra Endomorphisms. Proceed by structural induction on the length (or parts) of the partition. For the inductive step, pull one annihilation mode $\rho_{-m}$ to the right past the creation modes $\prod \rho_{n_i}$ using the exact Kac-Moody commutation relation $[\rho_{-m}, \rho_n] = m \delta_{mn}$ (from Lemma 10.5).
   * This step-by-step reduction algebraically expands to the diagonal matrix matching the standard bosonic norm. In Lean, vectors that form an orthogonal set with non-zero norms are strictly linearly independent (invoke `LinearIndependent.of_orthogonal`).

3. **Proving Completeness (Theorem 11.5) via `Module.finrank`:**
   * You have two facts:
     1. The algebraic number of linearly independent partition states is $p(K)$.
     2. The spatial dimension of the fermionic subspace $\mathcal{H}^N_K$ (from the Rank Formula mapping in Chapter 7) is exactly equal to $p(K)$ (Lemma 11.3).
   * Mathlib dictates that if a linearly independent set has a cardinality exactly equal to the `finrank` of the space, its `Submodule.span` equals the entire space (`top`).
   * `span_eq_top_of_linearIndependent_of_card_eq_finrank` is the precise theorem to invoke here.

4. **Proving Sugawara (Theorem 12.3) via `Submodule.span_induction`:**
   * Do not assert $\hat{E} = H_{\text{sug}}$ as a global equality in `Module.End ℂ (FockSpace _)`, because outside the budget margins, edge-effects ruin the equality.
   * State the theorem strictly for vectors within the Submodule:
     `∀ (ψ : BudgetSpace L K Nmax), (E_op) ψ.val = (H_sug) ψ.val`
   * Define the difference operator `D := E_op - H_sug`.
   * **The Induction Step:** Since `BudgetSpace` is spanned by the partition states $\{ \vert{}\lambda; N\rangle \}$, use `Submodule.span_induction`.
     * *Base Case:* Prove `D |N>_0 = 0`. Both $\hat{E}$ and $H_{sug}$ annihilate the sector ground state.
     * *Step Case:* Prove that if `D ψ = 0`, then `D (ρ_n ψ) = 0`. This follows immediately from `[D, ρ_n] = 0` (Lemma 12.2).
     * By induction, $D$ is the zero vector for every element in the span.
