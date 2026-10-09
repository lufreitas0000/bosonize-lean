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

**Definition 13.2 (Joint Sector Ground States).**
Let $\vec{N} \in \mathbb{Z}^M$ be a vector of relative charges for each species. The joint vacuum state is the tensor product of independent species ground states:

$$
\vert{}\vec{N}\rangle_0 := \bigotimes_{\nu \in \mathcal{C}} \vert{}N_\nu\rangle_0 \tag{13.2}
$$

**Definition 13.3 (Species Density Modes).**
Density operators are partitioned by species:

$$
\rho_{m, \nu} := \sum_{\substack{k \in \Lambda^* \\ k+m \in \Lambda^*}} c^\dagger_{(\nu, k+m)} c_{(\nu, k)} \tag{13.3}
$$

Because they act on disjoint indices, $[\rho_{m, \nu}, \rho_{n, \nu'}] = 0$ for $\nu \neq \nu'$.

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

#### 13.3 Exact Algebraic Properties and Isometry

**Lemma 13.5 (Isometry).**
Because the Haldane basis completeness holds on both the source budget $B(\vec{N}, K)$ and the target budget $B(\vec{N}-e_\nu, K)$ (provided the maximum energy $K$ satisfies the completeness regimes for both $N_\nu$ and $N_\nu - 1$), and because the standard bosonic Gram matrix inner product $z_\lambda$ is independent of the sector charge, the Klein map is an exact **isometry**.

**Lemma 13.6 (Cross-Species Anti-Commutation).**
Because $F_\nu$ lowers the actual total occupation of species $\nu$ by exactly 1, applying $F_\eta$ after $F_\nu$ strictly drops the sum $\sum_{\gamma < \eta} (h + N_\gamma)$ by 1 if $\nu < \eta$. Consequently, mapping across distinct species anti-commutes:

$$
F_\nu F_{\nu'} + F_{\nu'} F_\nu = 0 \quad (\text{for } \nu \neq \nu') \tag{13.7}
$$

*Correction to Clifford Terminologies:*
Klein shifts generally have $F^2 \neq 0$ and do *not* generate a finite-dimensional Clifford algebra merely from cross-species anti-commutation. We reserve Clifford terminology strictly for Majorana combinations with exact square relations.

**Lemma 13.7 (Number Shifting).**
Because $F_\nu$ explicitly targets the $\vec{N}-e_\nu$ sector, it structurally satisfies the fundamental intertwining equations for number operators:

$$
F_\nu \hat{N}_{\nu'} = (\hat{N}_{\nu'} + \delta_{\nu, \nu'} I) F_\nu \tag{13.8}
$$
