### Chapter 9: Density Modes and Kinematics

The formulation of density modes strictly follows the shift definitions and margin accounting set out in [Appendix A03](../appendices/a03_energy_budgets_and_filtered_maps.md) and [Appendix A04](../appendices/a04_density_partitions_and_sugawara.md).

#### 9.1 The Fock Space Kinematics and Valid Pairs

To avoid the complexities of subtype filtering inside sums, we define valid kinematic momentum shifts precisely as sets of valid integer pairs. The shift $m$ is always typed as $m \in \mathbb{Z}$.

**Definition 9.1 (Valid Shift Pairs).**
For any integer shift $m \in \mathbb{Z}$, the set of valid momentum bounds $D_m$ strictly avoids cyclic wrapping:

$$
D_m := \{ (p, k) \in \Lambda^* \times \Lambda^* \mid p = k + m \} \tag{9.1}
$$

*Lean 4 Proof Strategy:*
Use `Finset.univ.filter` on `Ch01.Band L × Ch01.Band L` with the integer predicate `p.val = k.val + m`. Reuse the positive-Nyquist band `{-h+1,...,h}` from Core. The periodic position lattice and integer band labels must not be interchanged.

**Definition 9.2 (One-Particle Shift Matrix).**
We define the one-particle partial shift matrix $T_m \in \mathrm{End}_{\mathbb{C}}(\ell^2(\Lambda^*))$ exactly on the single-particle indices:

$$
(T_m)_{p,k} := \begin{cases} 1 & \text{if } (p,k) \in D_m \\ 0 & \text{otherwise} \end{cases} \tag{9.2}
$$

*Lean 4 Proof Strategy:*
Formalize $T_m$ as a matrix `Matrix (Ch01.Band L) (Ch01.Band L) ℂ` or a linear map `(Ch01.Band L → ℂ) →ₗ[ℂ] (Ch01.Band L → ℂ)`.
```lean
def T (m : ℤ) : Matrix (Ch01.Band L) (Ch01.Band L) ℂ :=
  fun p k => if p.val = k.val + m then 1 else 0
```
Auxiliary lemmas needed: proving that $T_m T_n$ corresponds to $T_{m+n}$ under the right conditions, and establishing the adjoint $(T_m)^\dagger = T_{-m}$.

**Definition 9.3 (Second Quantization Map).**
For any single-particle matrix $A$, its second-quantized operator $d\Gamma(A) \in \mathrm{End}_{\mathbb{C}}(\mathrm{Fock}(\Lambda^*))$ is:

$$
d\Gamma(A) := \sum_{p,k \in \Lambda^*} A_{pk} c_p^\dagger c_k \tag{9.3}
$$

*Lean 4 Proof Strategy:*
Define $d\Gamma$ as a linear map from `Matrix (Ch01.Band L) (Ch01.Band L) ℂ` to the algebra of Fock space operators, e.g., `Module.End ℂ (FockSpace (Ch01.Band L))`.
```lean
def dGamma (A : Matrix (Ch01.Band L) (Ch01.Band L) ℂ) : Module.End ℂ (FockSpace (Ch01.Band L)) :=
  ∑ p k, A p k • (cDag p * c k)
```
Auxiliary lemma: `dGamma_comm : ⁅dGamma A, dGamma B⁆ = dGamma ⁅A, B⁆`. This relies on the canonical anticommutation relations (CAR) of $c_p^\dagger$ and $c_k$, requiring careful index manipulation and simplification.

By the CAR identities, this map exactly preserves commutators: $d\Gamma([A,B]) = [d\Gamma(A), d\Gamma(B)]$.

#### 9.2 Density Modes

**Definition 9.4 (Raw and Normal-Ordered Density).**
The raw density mode $\rho_m$ is exactly the second-quantized shift:

$$
\forall m \in \mathbb{Z}, \quad \rho_m := d\Gamma(T_m) = \sum_{(p,k) \in D_m} c_p^\dagger c_k \tag{9.4}
$$

Normal-ordered density zero-points the macroscopic charge $h$ at $m=0$:

$$
:\!\rho_m\!: \ := \rho_m - \delta_{m,0} h I \tag{9.5}
$$

*Lean 4 Proof Strategy:*
Formalize the raw density directly via `rho m := dGamma (T m)`.
Normal ordering can be written as `normal_rho m := rho m - (if m = 0 then h • 1 else 0)`.
The sea contains exactly h occupied momenta per species. Prove `rho 0 Ω = h • Ω` by the number-operator occupation indicator and band counting; this fixes the subtraction independently of later scalar CCR.

#### 9.3 Kinematic Lemmas and Linear Independence

**Lemma 9.5 (Finiteness and Global Commutativity).**
1. **Vanishing bounds:** For $|m| \ge L$, $D_m$ is empty, so $T_m = 0$ and $\rho_m = 0$.
2. **Adjointness:** $T_m^\dagger = T_{-m}$ and $\rho_m^\dagger = \rho_{-m}$.
3. **Same-sign commutativity:** For any non-negative $m, n \ge 0$, the partial shifts strictly compose: $T_m T_n = T_{m+n}$. Because the single-particle matrices commute, $[T_m, T_n] = 0$. Thus $[\rho_m, \rho_n] = 0$ **globally** as an exact endomorphism identity over the entire Fock space (not just on a budget).

*Lean 4 Proof Strategy:*
1. **Vanishing bounds**: Proved using `linarith` on the momentum indices bounded by $\Lambda^*$.
2. **Adjointness**: Follows from `Matrix.conjTranspose` properties and `(cDag p * c k)† = cDag k * c p`.
3. **Same-sign commutativity**: First prove `T_comp : m ≥ 0 → n ≥ 0 → T m * T n = T (m + n)` by expanding matrix multiplication. Deduce `⁅T m, T n⁆ = 0`. Then, apply `dGamma_comm` to elevate this to the $\rho_m$ operators.

**Lemma 9.6 (Covariance and Energy).**
Using the normal-ordered Hamiltonian $\hat{P} = H_0 - E_\Omega I$ (where $E_\Omega = -h(h-1)/2$), the densities conserve particle number and rigorously shift energy:

$$
[\hat{N}, \rho_m] = 0, \qquad [\hat{P}, \rho_m] = m \rho_m \tag{9.6}
$$

*Lean 4 Proof Strategy:*
Formalize $\hat{N} = \rho_0$. The particle number conservation is simply $[\rho_0, \rho_m] = 0$, derived from `dGamma_comm` and $[T_0, T_m] = 0$.
For the Hamiltonian shift, define $H_0 = \sum_{p} p c_p^\dagger c_p$. The proof relies on computing the fundamental commutator $[H_0, c_p^\dagger c_k] = (p - k) c_p^\dagger c_k$. Summing this over $D_m$, where $p - k = m$, neatly extracts the factor $m$, yielding $m \rho_m$.

**Lemma 9.7 (Exact Vacuum Norm and Linear Independence).**
To prove linear independence without circular assumptions about the Schwinger term, we explicitly compute the vacuum action using orthogonal single-particle hop kets. For any $1 \le m \le h$:

$$
\|\rho_m |\Omega\rangle \|^2 = m \tag{9.7}
$$

Because applying $\rho_m$ to the vacuum yields a non-zero state with distinct energy eigenvalue $m$, the positive density modes $\{\rho_m\}_{m=1}^h$ are strictly linearly independent over $\mathbb{C}$.

*Lean 4 Proof Strategy:*
Formalize the vacuum state $|\Omega\rangle$ using its defining annihilation conditions (e.g., $c_p |\Omega\rangle = 0$ for $p > 0$ and $c_p^\dagger |\Omega\rangle = 0$ for $p \le 0$).
The norm squared is $\langle \Omega | \rho_{-m} \rho_m | \Omega \rangle$. To compute this, prove an auxiliary lemma for the vacuum expectation value (VEV) of four-fermion operators using Wick's theorem or iterated anticommutators. Only exactly $m$ terms survive the vacuum projection bounds, yielding the result $m$.
After the exact occupation-hop norm calculation, prove independence of the resulting vectors by orthogonal distinct-energy eigenspaces (or a verified eigenvector API). Independence of the density maps follows by evaluating a linear relation at the vacuum. Do not invoke the later scalar CCR to prove this first norm lemma.

**Lemma 9.8 (Budget Action on Admissible Sectors).**
For any admissible charge sector $-h \le N \le h$, the operator $\rho_m$ preserves charge ($[\hat{N}, \rho_m] = 0$) and maps the budget subspace $B(N,K)$ into $B(N, K+m)$ for $m \ge 0$. A lowering mode $m \ge 1$ mapped onto the unique sector ground state $|N\rangle_0$ falls below the zero-energy bound and rigidly annihilates:

$$
\forall -h \le N \le h, \quad \forall m \ge 1, \quad \rho_{-m} |N\rangle_0 = 0 \tag{9.8}
$$

*Lean 4 Proof Strategy:*
Formalize using the admissible sector subtype `-h ≤ N ∧ N ≤ h`.
Using the commutation relations $[\hat{N}, \rho_m] = 0$ and $[\hat{P}, \rho_m] = m \rho_m$ from Lemma 9.6, show that $\rho_m$ maps elements between the budget subspaces correctly.
For the annihilation condition, assume by contradiction that $\rho_{-m} |N\rangle_0 \neq 0$. This resulting state would have excitation energy $-m < 0$, which contradicts the exact positivity of excitation energy $e(S) \ge 0$ proved in Lemma 7.4. Thus, the state must be identically 0.
