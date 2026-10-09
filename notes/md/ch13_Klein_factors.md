### Chapter 13: Klein Factors & Multi-Species Fermions

To achieve the full bosonization dictionary, we must reconstruct the physical fermionic field operator $\psi(x)$ entirely out of bosonic components.
Because bosonic density modes $\rho_{m, \nu}$ strictly conserve the total particle number of a species, they cannot change the charge sector. The true operator $\psi(x)$ removes one particle. We factorize the fermionic field into:
1. A **bosonic exponential** that handles density fluctuations.
2. A **Klein map** $F_\nu$ that explicitly shifts the system from one charge sector to another while correctly tracking cross-species fermionic statistics.

The mathematical formulation strictly adheres to [Appendix A05](../appendices/a05_exponentials_klein_and_vertex_scope.md).

#### 13.1 Multi-Species Index and the Vacuum

**Definition 13.1 (Multi-Species Index).**
Let $\mathcal{C}$ be a finite, strictly ordered index set of species. The total single-particle index set is ordered lexicographically:

$$
\iota := \mathcal{C} \times \Lambda^* \tag{13.1}
$$

*Lean 4 Proof Strategy:*
Define the index set as `Prod C Λ*`. Since `C` and `Λ*` are ordered types, derive `LinearOrder` using `Prod.Lex` to provide the lexicographic ordering required by the CAR algebra.

**Definition 13.2 (Joint Sector Ground States).**
Let $\vec{N} \in \mathbb{Z}^M$ be a vector of relative charges for each species. The joint vacuum state is the tensor product of independent species ground states:

$$
\vert{}\vec{N}\rangle_0 := \bigotimes_{\nu \in \mathcal{C}} \vert{}N_\nu\rangle_0 \tag{13.2}
$$

*Lean 4 Proof Strategy:*
Formalize `N` as a function `C → ℤ`. Define the joint ground state as a finite tensor product over the `Fintype` `C` of the single-species ground states `|N_nu⟩`. Use `PiTensorProduct` or construct a joint Hilbert space recursively for finite index sets.

**Definition 13.3 (Species Density Modes).**
Density operators are partitioned by species:

$$
\rho_{m, \nu} := \sum_{\substack{k \in \Lambda^* \\ k+m \in \Lambda^*}} c^\dagger_{(\nu, k+m)} c_{(\nu, k)} \tag{13.3}
$$

Because they act on disjoint indices, $[\rho_{m, \nu}, \rho_{n, \nu'}] = 0$ for $\nu \neq \nu'$.

*Lean 4 Proof Strategy:*
Define density operators parameterized by species `ν : C` and momentum `m : ℤ`. The sum over `k` is constrained within the bounds `Λ*` for `k` and `k+m`. Provide an auxiliary lemma proving `[rho_m_ν, rho_n_ν'] = 0` for `ν ≠ ν'` by showing that the creation and annihilation operators act on disjoint indices, relying on `Prod.Lex` and `Fermion.CAR`.

#### 13.2 Klein Maps Between Admissible Sectors

A true Klein map is not a global unitary endomorphism on the entire finite-dimensional Fock space. We define it specifically as a mapped linear isometry between admissible source and target sector budgets of equal excitation cutoff.

**Definition 13.4 (Klein Maps on the Haldane Basis).**
For each species $\nu \in \mathcal{C}$, the Klein map $F_\nu$ is defined between the fixed-energy budget subspace of sector $\vec{N}$ and sector $\vec{N}-e_\nu$. Its action on the bosonic partition basis is:

$$
F_\nu \vert{}\vec{\lambda}; \vec{N}\rangle := P(\nu, \vec{N}) \vert{}\vec{\lambda}; \vec{N} - e_\nu\rangle \tag{13.4}
$$

To strictly respect the CAR lexicographic sign rules of the underlying Fock space without phase anomalies, the parity sign $P$ counts the *actual total preceding occupation*, not just the relative charge:

$$
P(\nu, \vec{N}) := (-1)^{\sum_{\eta < \nu} (h + N_\eta)} \times (\text{same-species ground-ket phase}) \tag{13.5}
$$

By defining the map independently of the bosonic partitions $\vec{\lambda}$, we mathematically enforce that the Klein map commutes with all density modes:

$$
\forall m \in \mathbb{Z}, \forall \nu, \nu' \in \mathcal{C}, \quad F_\nu \rho_{m, \nu'} = \rho_{m, \nu'} F_\nu \tag{13.6}
$$

(Note: This is an intertwining equality between maps on the budget spaces, not a global commutator).

*Lean 4 Proof Strategy:*
Define `F_nu` as a linear map from the fixed-energy subspace of sector `N` to sector `N - e_nu`. Compute the sign function `P(ν, N)` using `Finset.sum` over `{η ∈ C | η < ν}`. Prove that `F_nu` intertwines with the bosonic operators `rho_m_ν'` by explicitly proving `F_nu ∘ rho_m = rho_m ∘ F_nu` evaluated on the `|λ; N⟩` basis states.

#### 13.3 Exact Algebraic Properties and Isometry

**Lemma 13.5 (Isometry).**
Because the Haldane basis completeness holds on both the source budget $B(\vec{N}, K)$ and the target budget $B(\vec{N}-e_\nu, K)$ (provided the maximum energy $K$ satisfies the completeness regimes for both $N_\nu$ and $N_\nu - 1$), and because the standard bosonic Gram matrix inner product $z_\lambda$ is independent of the sector charge, the Klein map is an exact **isometry**.

*Lean 4 Proof Strategy:*
Use the `LinearIsometry` class in Mathlib to bundle `F_nu`. To prove `∥F_nu v∥ = ∥v∥`, use the fact that `F_nu` maps standard orthogonal basis vectors `|λ; N⟩` to `±|λ; N - e_nu⟩`, and their inner products depend only on `λ` (via `z_λ`), independent of the charge sector `N`. State an auxiliary lemma `inner_product_charge_independent`.

**Lemma 13.6 (Cross-Species Anti-Commutation).**
Because $F_\nu$ lowers the actual total occupation of species $\nu$ by exactly 1, applying $F_\eta$ after $F_\nu$ strictly drops the sum $\sum_{\gamma < \eta} (h + N_\gamma)$ by 1 if $\nu < \eta$. Consequently, mapping across distinct species anti-commutes:

$$
F_\nu F_{\nu'} + F_{\nu'} F_\nu = 0 \quad (\text{for } \nu \neq \nu') \tag{13.7}
$$

*Correction to Clifford Terminologies:*
Klein shifts generally have $F^2 \neq 0$ and do *not* generate a finite-dimensional Clifford algebra merely from cross-species anti-commutation. We reserve Clifford terminology strictly for Majorana combinations with exact square relations.

*Lean 4 Proof Strategy:*
Prove the relation `F_nu ∘ F_nu' + F_nu' ∘ F_nu = 0`. Evaluate the action of both composite maps on a generic basis state `|λ; N⟩`. Compute the parity sign product `P(ν, N - e_nu') * P(ν', N)` versus `P(ν', N - e_nu) * P(ν, N)`. By calculating the change in the occupation sum `∑ (h + N_γ)` when the sector charge changes, demonstrate that a relative minus sign appears, thus establishing the anti-commutation.

**Lemma 13.7 (Number Shifting).**
Because $F_\nu$ explicitly targets the $\vec{N}-e_\nu$ sector, it structurally satisfies the fundamental intertwining equations for number operators:

$$
F_\nu \hat{N}_{\nu'} = (\hat{N}_{\nu'} + \delta_{\nu, \nu'} I) F_\nu \tag{13.8}
$$

*Lean 4 Proof Strategy:*
Express the number operator `N_hat` acting on a specific charge sector as a scalar multiplication by `N_nu'`. Apply both sides to a basis vector `|λ; N⟩`. The operator `N_hat_nu'` yields eigenvalue `N_nu'`, while on the RHS, mapping to `N - e_nu` reduces the species charge by `δ_nu_nu'`, which perfectly offsets the added `δ_nu_nu' I` term, proving `F_nu ∘ N_hat_nu' = (N_hat_nu' + δ_nu_nu' • id) ∘ F_nu`.
