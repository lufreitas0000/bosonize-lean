# BOSONIZE-LEAN: Mathematical Reference Notes

## Part II: Phase 2 The Density Sector

### Chapter 11: Haldane Completeness

We have established that density modes $\rho_m$ behave algebraically like independent bosonic creation and annihilation operators when confined to a low-energy budget. The next crucial step is to prove **Haldane Completeness**: demonstrating that the *entire* low-energy fermionic Hilbert space can be spanned purely by these collective bosonic density waves.

**Physical Intuition for Bosonic States as Partitions:**
Imagine the sector ground state $\vert{}N\rangle_0$ as a perfectly flat, undisturbed Fermi sea. We can add energy $K$ to this sea in various ways using the density creation modes (where $m > 0$). For example, to add $K=4$ units of energy, we could apply one $\rho_4$ mode, or two $\rho_2$ modes, or one $\rho_3$ and one $\rho_1$.
Mathematically, these combinations correspond exactly to the **integer partitions** of $K$. A partition $\lambda$ of $K$ is a way of writing $K$ as a sum of positive integers. If we apply the corresponding string of density operators to the ground state, we create a "bosonic partition state."

#### 11.1 Definitions

**Definition 11.1 (Bosonic Partition States).**
Let $K \in \mathbb{N}$ be a total excitation energy. Let $\lambda$ be an integer partition of $K$, which can be represented by the multiplicities $r_m$ of each integer part $m \ge 1$, such that $\sum_{m \ge 1} m \cdot r_m = K$.
For any relative charge sector $N$, the bosonic partition state generated from the sector ground state $\vert{}N\rangle_0$ is defined as:

$$
\forall \lambda \vdash K, \quad \vert{}\lambda; N\rangle := \left( \prod_{m \ge 1} \rho_m^{r_m} \right) \vert{}N\rangle_0 \tag{11.1}
$$

**Definition 11.2 (Fixed-Energy Sector Subspace).**
The fixed-energy fermionic subspace $\mathcal{H}^N_K$ is the span of all pure fermionic indicator basis states that have exactly relative charge $N$ and excitation energy $K$:

$$
\mathcal{H}^N_K := \mathrm{span}_{\mathbb{C}} \{ \delta_S \mid N(S) = N \text{ and } e(S) = K \} \tag{11.2}
$$

#### 11.2 Regime R1: Exact Counting

**Physical Intuition for the Counting Regime (R1):**
How many independent fermionic states exist at energy $K$? In a standard infinite Dirac sea, the number of fermionic excitations exactly matches the number of integer partitions $p(K)$. However, our lattice is finite. The available single-particle excitations are constrained by a "box" of empty states above the Fermi surface (size $h-N$) and occupied states below (size $h+N$).
If $K$ is too large, the excitations will hit the absolute ceiling or floor of the band, and some partitions will be physically impossible to construct, leading to fewer states than $p(K)$.
To guarantee that the finite lattice perfectly mimics the infinite continuum, we must restrict $K$ so that the highest possible excitation never reaches the band edges. Remember that $N$ is the *relative* charge (deviation from half-filling). If $N=0$ (half-filling), the ceiling is $h$ steps away. If $N>0$, the Fermi surface is higher, so the ceiling is closer. This boundary-free condition is known as the **R1 Margin**.

**Lemma 11.3 (Regime R1: Unbounded Partition Counting).**
If the energy budget $K$ and the relative sector charge $N$ satisfy the strict **R1 Margin Condition**:

$$
K \le h - \vert{}N\vert{} \tag{11.3}
$$

Then boundary effects are entirely absent. The dimension of the fermionic fixed-energy subspace $\mathcal{H}^N_K$ is exactly equal to $p(K)$, the number of standard integer partitions of $K$:

$$
\dim_{\mathbb{C}} (\mathcal{H}^N_K) = p(K) \tag{11.4}
$$

#### 11.3 Regime R2: Orthogonality and Completeness

**Physical Intuition for the Algebraic Regime (R2):**
To prove that the partition states $\{\vert{}\lambda; N\rangle\}$ form a valid basis, we must compute their inner products (the Gram matrix) and prove they are orthogonal. To do this, we must commute annihilation modes $\rho_{-m}$ past creation modes $\rho_n$ using the Kac-Moody algebra (from Lemma 10.5).
However, applying a creation operator *raises* the energy of the state. If we are evaluating a complex inner product of states with target energy $K$, the intermediate mathematical steps will involve states with transient energies up to $2K$. Therefore, to ensure that *every single intermediate step* safely remains inside the frozen buffer zones, we require a stronger margin condition: the **R2 Margin**.

**Lemma 11.4 (Regime R2: Bosonic Orthogonality).**
Let $\lambda$ and $\mu$ be integer partitions of $K$. If the parameters satisfy the conservative **R2 Margin Condition**:

$$
2K + \vert{}N\vert{} \le h \tag{11.5}
$$

Then the inner product of the partition states evaluates exactly to the standard bosonic Gram matrix, proving they are strictly orthogonal:

$$
\langle \lambda; N \mid \mu; N \rangle = \delta_{\lambda\mu} \prod_{m \ge 1} m^{r_m} (r_m)! \tag{11.6}
$$

Because all parts $m \ge 1$, the norm of every state is strictly positive ($\neq 0$), ensuring linear independence.

**Connection to Symmetric Functions and the Hall Inner Product:**
In the mathematical field of algebraic combinatorics, it is a well-known result that if one identifies the density mode $\rho_m$ with the power-sum symmetric function $p_m = \sum_i x_i^m$, the bosonic partition state $\vert{}\lambda; N\rangle$ corresponds directly to the polynomial $p_\lambda = \prod p_{\lambda_i}$. The orthogonal norm derived in Lemma 11.4 matches exactly the standard **Hall inner product** on symmetric polynomials, where the standard normalization factor is denoted $z_\lambda = \prod m^{r_m} r_m!$.

**Theorem 11.5 (Haldane Completeness).**
Under the R2 Margin condition, the set of bosonic partition states $\{\vert{}\lambda; N\rangle \mid \lambda \vdash K \}$ forms a complete, orthogonal basis for the fermionic fixed-energy subspace $\mathcal{H}^N_K$.
Consequently, the full energy budget subspace $\mathcal{B}^N_K$ (which contains all states with energy $\le K$) is completely spanned by the union of partition states up to $K$.
