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
Define the index set as `Prod C (Ch01.Band L)`. Since `C` and $\Lambda^*$ are ordered types, derive `LinearOrder` using `Prod.Lex` to provide the lexicographic ordering required by the CAR algebra.

**Definition 13.2 (Joint Sector Ground States).**
Let $\vec{N} \in \mathbb{Z}^M$ be a vector of relative charges for each species. The joint vacuum state is the tensor product of independent species ground states:

$$
\vert{}\vec{N}\rangle_0 := \bigotimes_{\nu \in \mathcal{C}} \vert{}N_\nu\rangle_0 \tag{13.2}
$$

*Lean 4 Proof Strategy:*
Formalize `N` as a function `C → ℤ`. Define the joint ground state as a finite tensor product over the `Fintype` `C` of the single-species ground states $|N_\nu\rangle$. Use `PiTensorProduct` or construct a joint Hilbert space recursively for finite index sets.

**Definition 13.3 (Species Density Modes).**
Density operators are partitioned by species:

$$
\rho_{m, \nu} := \sum_{\substack{k \in \Lambda^* \\ k+m \in \Lambda^*}} c^\dagger_{(\nu, k+m)} c_{(\nu, k)}^{\phantom{\dagger}} \tag{13.3}
$$

Because they act on disjoint indices, $[\rho_{m, \nu}, \rho_{n, \nu'}] = 0$ for $\nu \neq \nu'$.

*Lean 4 Proof Strategy:*
Define density operators parameterized by species `ν : C` and momentum `m : ℤ`. The sum over `k` is constrained within the bounds $\Lambda^*$ for `k` and `k+m`. Provide an auxiliary lemma proving $[\rho_{m,\nu},\rho_{n,\nu'}]=0$ for `ν ≠ ν'` by showing that the creation and annihilation operators act on disjoint indices, relying on `Prod.Lex` and `Fermion.CAR`.

#### 13.2 Klein Maps Between Admissible Sectors

A true Klein map is not a global unitary endomorphism on the entire finite-dimensional Fock space. We define it specifically as a mapped linear isometry between admissible source and target sector budgets of equal excitation cutoff.

**Definition 13.4 (Klein Maps on Budget Subspaces).**
For each species $\nu \in \mathcal{C}$ and admissible sector pair with $\vec{N}$ and $\vec{N}-e_\nu$ both admissible (meaning $-h+1 \le N_\nu \le h$), under the multispecies completeness condition:
$$
\forall \eta \in \mathcal{C}, \quad 2K + \max(|N_\eta|, |N_\eta - \delta_{\nu\eta}|) \le h
$$
the Klein map $F_{\nu, \vec{N}, K}$ is defined as a linear map from $B(\vec{N}, K)$ to $B(\vec{N}-e_\nu, K)$ by its action on the bosonic partition basis states $|\vec{\lambda}; \vec{N}\rangle$:

$$
F_{\nu, \vec{N}, K} \vert{}\vec{\lambda}; \vec{N}\rangle := P(\nu, \vec{N}) \vert{}\vec{\lambda}; \vec{N} - e_\nu\rangle \tag{13.4}
$$

The exact sign factor $P(\nu, \vec{N}) \in \{+1, -1\}$ accounts for both the lexicographic CAR ordering of species and the annihilation of the top mode in the Fermi sea:

$$
P(\nu, \vec{N}) := (-1)^{\sum_{\eta < \nu} (h + N_\eta) + (h + N_\nu - 1)} \tag{13.5}
$$

Because $P(\nu, \vec{N})$ depends only on the charge vector $\vec{N}$ and not on the partition $\vec{\lambda}$, the Klein map intertwines with density modes across a four-budget commuting square. For any raising density mode $\rho_{m, \nu'}$ of weight $m > 0$:

$$
F_{\nu, \vec{N}, K+m} \circ \rho_{m, \nu'} = \rho_{m, \nu'} \circ F_{\nu, \vec{N}, K} \tag{13.6}
$$

as linear maps from $B(\vec{N}, K)$ into $B(\vec{N}-e_\nu, K+m)$, provided the enlarged multispecies completeness margin:
$$
\forall \eta \in \mathcal{C}, \quad 2(K+m) + \max(|N_\eta|, |N_\eta - \delta_{\nu\eta}|) \le h
$$
holds across all four budget spaces $B(\vec{N}, K)$, $B(\vec{N}, K+m)$, $B(\vec{N}-e_\nu, K)$, and $B(\vec{N}-e_\nu, K+m)$. For lowering modes $m > 0$, the corresponding square intertwines maps into target cutoff $K$.

*Lean 4 Proof Strategy:*
Define the phase exponent as `(∑ η in Finset.univ.filter (· < ν), ((h : ℤ) + N η)) + ((h : ℤ) + N ν - 1)`, with integer power or a proved parity character. The same-species term occurs once, outside the preceding-species sum. Construct the map by `Module.Basis.constr` on tuples of partitions whose summed energy is at most K, prove the four-budget square on that joint basis, and extend linearly.

#### 13.3 Exact Algebraic Properties and Isometry

**Lemma 13.5 (Isometry).**
Because Haldane basis completeness holds on both the source budget $B(\vec{N}, K)$ and target budget $B(\vec{N}-e_\nu, K)$ under the multispecies completeness condition $\forall \eta \in \mathcal{C}, 2K + \max(|N_\eta|, |N_\eta - \delta_{\nu\eta}|) \le h$, and because the standard bosonic Gram matrix inner product $z_\lambda = \prod m^{r_m} r_m!$ is independent of the sector charge, $F_{\nu, \vec{N}, K}$ is an exact **linear isometry**:

$$
\forall \psi \in B(\vec{N}, K), \quad \| F_{\nu, \vec{N}, K} \psi \| = \| \psi \|
$$

*Lean 4 Proof Strategy:*
Use the `LinearIsometry` class in Mathlib to bundle `F_nu`. To prove `∥F_nu v∥ = ∥v∥`, use the fact that `F_nu` maps standard orthogonal basis vectors $|\lambda;N\rangle$ to $\pm|\lambda;N-e_\nu\rangle$, and their inner products depend only on `λ` (via $z_\lambda$), independent of the charge sector `N`. State an auxiliary lemma `inner_product_charge_independent`.

**Lemma 13.6 (Cross-Species Anti-Commutation).**
Let $\nu \neq \nu'$ be distinct species. Assume the source sector $\vec{N}$, intermediate sectors $\vec{N}-e_\nu$, $\vec{N}-e_{\nu'}$, and final sector $\vec{N}-e_\nu-e_{\nu'}$ are all admissible ($-h \le N_\gamma - \delta_{\nu\gamma} - \delta_{\nu'\gamma} \le h$), and that cutoff $K$ satisfies the completeness margin on all four sectors:
$$
\forall \eta \in \mathcal{C}, \quad 2K + \max(|N_\eta|, |N_\eta - \delta_{\nu\eta}|, |N_\eta - \delta_{\nu'\eta}|, |N_\eta - \delta_{\nu\eta} - \delta_{\nu'\eta}|) \le h.
$$
Because lowering species $\nu$ changes the preceding occupation count $\sum_{\eta < \nu'} (h + N_\eta)$ by $\pm 1$ whenever $\nu < \nu'$, the two composite paths from $B(\vec{N}, K)$ to $B(\vec{N}-e_\nu-e_{\nu'}, K)$ differ by an exact minus sign:

$$
F_{\nu', \vec{N}-e_\nu, K} \circ F_{\nu, \vec{N}, K} + F_{\nu, \vec{N}-e_{\nu'}, K} \circ F_{\nu', \vec{N}, K} = 0 \tag{13.7}
$$

*Correction to Clifford Terminologies:*
Klein shifts generally have $F^2 \neq 0$ and do *not* generate a finite-dimensional Clifford algebra merely from cross-species anti-commutation. We reserve Clifford terminology strictly for Majorana combinations with exact square relations.

*Lean 4 Proof Strategy:*
Prove the relation `F_nu ∘ F_nu' + F_nu' ∘ F_nu = 0`. Evaluate the action of both composite maps on a generic basis state $|\lambda;N\rangle$. Compute the parity sign product $P(\nu,N-e_{\nu'})P(\nu',N)$ versus $P(\nu',N-e_\nu)P(\nu,N)$. By calculating the change in the occupation sum $\sum(h+N_\gamma)$ when the sector charge changes, demonstrate that a relative minus sign appears, thus establishing the anti-commutation.

**Lemma 13.7 (Number Shifting).**
Because $F_\nu$ explicitly targets the $\vec{N}-e_\nu$ sector, it structurally satisfies the fundamental intertwining equations for number operators:

$$
F_\nu \hat{N}_{\nu'} = (\hat{N}_{\nu'} + \delta_{\nu, \nu'} I) F_\nu \tag{13.8}
$$

*Lean 4 Proof Strategy:*
Express the number operator `N_hat` acting on a specific charge sector as a scalar multiplication by `N_nu'`. Apply both sides to a basis vector $|\lambda;N\rangle$. The operator `N_hat_nu'` yields eigenvalue `N_nu'`, while on the RHS, mapping to $N-e_\nu$ reduces the species charge by `δ_nu_nu'`, which perfectly offsets the added `δ_nu_nu' I` term, proving `F_nu ∘ N_hat_nu' = (N_hat_nu' + δ_nu_nu' • id) ∘ F_nu`.
