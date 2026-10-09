### Chapter 9: Density Modes and Kinematics

The formulation of density modes strictly follows the shift definitions and margin accounting set out in [Appendix A03](../appendices/a03_energy_budgets_and_filtered_maps.md) and [Appendix A04](../appendices/a04_density_partitions_and_sugawara.md).

#### 9.1 The Fock Space Kinematics and Valid Pairs

To avoid the complexities of subtype filtering inside sums, we define valid kinematic momentum shifts precisely as sets of valid integer pairs. The shift $m$ is always typed as $m \in \mathbb{Z}$.

**Definition 9.1 (Valid Shift Pairs).**
For any integer shift $m \in \mathbb{Z}$, the set of valid momentum bounds $D_m$ strictly avoids cyclic wrapping:

$$
D_m := \{ (p, k) \in \Lambda^* \times \Lambda^* \mid p = k + m \} \tag{9.1}
$$

**Definition 9.2 (One-Particle Shift Matrix).**
We define the one-particle partial shift matrix $T_m \in \mathrm{End}_{\mathbb{C}}(\ell^2(\Lambda^*))$ exactly on the single-particle indices:

$$
(T_m)_{p,k} := \begin{cases} 1 & \text{if } (p,k) \in D_m \\ 0 & \text{otherwise} \end{cases} \tag{9.2}
$$

**Definition 9.3 (Second Quantization Map).**
For any single-particle matrix $A$, its second-quantized operator $d\Gamma(A) \in \mathrm{End}_{\mathbb{C}}(\mathrm{Fock}(\Lambda^*))$ is:

$$
d\Gamma(A) := \sum_{p,k \in \Lambda^*} A_{pk} c_p^\dagger c_k \tag{9.3}
$$

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

#### 9.3 Kinematic Lemmas and Linear Independence

**Lemma 9.5 (Finiteness and Global Commutativity).**
1. **Vanishing bounds:** For $|m| \ge L$, $D_m$ is empty, so $T_m = 0$ and $\rho_m = 0$.
2. **Adjointness:** $T_m^\dagger = T_{-m}$ and $\rho_m^\dagger = \rho_{-m}$.
3. **Same-sign commutativity:** For any non-negative $m, n \ge 0$, the partial shifts strictly compose: $T_m T_n = T_{m+n}$. Because the single-particle matrices commute, $[T_m, T_n] = 0$. Thus $[\rho_m, \rho_n] = 0$ **globally** as an exact endomorphism identity over the entire Fock space (not just on a budget).

**Lemma 9.6 (Covariance and Energy).**
Using the normal-ordered Hamiltonian $\hat{P} = H_0 - E_\Omega I$ (where $E_\Omega = -h(h-1)/2$), the densities conserve particle number and rigorously shift energy:

$$
[\hat{N}, \rho_m] = 0, \qquad [\hat{P}, \rho_m] = m \rho_m \tag{9.6}
$$

**Lemma 9.7 (Exact Vacuum Norm and Linear Independence).**
To prove linear independence without circular assumptions about the Schwinger term, we explicitly compute the vacuum action using orthogonal single-particle hop kets. For any $1 \le m \le h$:

$$
\|\rho_m |\Omega\rangle \|^2 = m \tag{9.7}
$$

Because applying $\rho_m$ to the vacuum yields a non-zero state with distinct energy eigenvalue $m$, the positive density modes $\{\rho_m\}_{m=1}^h$ are strictly linearly independent over $\mathbb{C}$.

**Lemma 9.8 (Budget Action).**
The operator $\rho_m$ maps the budget subspace $B(N,K)$ exactly into $B(N, K+m)$. A lowering mode $m > 0$ mapped onto the ground state falls below the zero-energy bound and rigidly annihilates:

$$
\forall m \ge 1, \quad \rho_{-m} |N\rangle_0 = 0 \tag{9.8}
$$
