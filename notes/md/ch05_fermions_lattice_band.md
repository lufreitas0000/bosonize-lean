### Chapter 5: Position and Momentum Fermions

In this chapter, the abstract index set $\iota$ from Chapter 4 is instantiated as the centered momentum band $\iota = \Lambda^*$. The algebraic and normal-ordering mechanics follow [Appendix A01](../appendices/a01_fourier_scalars_and_characters.md) and [Appendix A04](../appendices/a04_density_partitions_and_sugawara.md).

*Notation Convention:*
- Spatial lattice positions are exclusively denoted by $x, y \in \Lambda$.
- Momentum modes are exclusively denoted by $k, p, q \in \Lambda^* = \{-h+1, \dots, h\}$.
- Operators $c_k, c_k^\dagger$ are the exact CAR operators from Chapter 4 acting on $\mathrm{Fock}(\Lambda^*)$.

---

#### 5.1 Definitions

**Definition 5.1 (Position Fermions).**
Using the finite unitary discrete Fourier transform $U$ and its inverse $U^\dagger$ established in Chapter 3 with scalar normalization $a = 1/\sqrt{L}$, we define the position annihilation and creation operators exactly:

$$
\forall x \in \Lambda, \quad c_x := a \sum_{k \in \Lambda^*} \chi(k,x) c_k \tag{5.1}
$$

$$
\forall x \in \Lambda, \quad c_x^\dagger := a \sum_{k \in \Lambda^*} \chi(-k,x) c_k^\dagger \tag{5.2}
$$

The local spatial density operator is $n_x := c_x^\dagger c_x$.

**Definition 5.2 (Bare and Normal-Ordered Hamiltonian).**
The bare momentum-space linearized Hamiltonian is:

$$
H_0 := \sum_{k \in \Lambda^*} k n_k = \sum_{k \in \Lambda^*} k c_k^\dagger c_k \tag{5.3}
$$

Because the bottom of the band is filled, the Dirac vacuum state $|\Omega\rangle$ has a macroscopic negative eigenvalue under $H_0$:

$$
E_\Omega := -h(h-1)/2 \tag{5.4}
$$

To properly measure physical energy without this constant shift, we define the normal-ordered momentum Hamiltonian:

$$
\hat{P} := H_0 - E_\Omega I \tag{5.5}
$$

---

#### 5.2 Lemmas and Theorems

**Lemma 5.3 (Position CAR).**
Because the DFT mapping is scaled by the exact real unitary constant $1/\sqrt{L}$ over the complex Euclidean space, the position operators strictly inherit the Canonical Anticommutation Relations without any scalar scaling artifacts. For all $x, y \in \Lambda$:

$$
\{c_x, c_y^\dagger\} = \delta_{xy} I, \quad \{c_x, c_y\} = 0, \quad \{c_x^\dagger, c_y^\dagger\} = 0 \tag{5.6}
$$

**Lemma 5.4 (Inverse Fourier Transform).**
The momentum operators can be recovered from the position operators. For all $k \in \Lambda^*$:

$$
c_k = a \sum_{x \in \Lambda} \chi(-k,x) c_x \tag{5.7}
$$

**Lemma 5.5 (Invariance of Total Particle Number).**
The sum of local densities equals the sum of mode occupation numbers:

$$
\sum_{x \in \Lambda} n_x = \sum_{k \in \Lambda^*} n_k = \hat{N}_{\mathrm{tot}} \tag{5.8}
$$

**Lemma 5.6 (Spectrum and Commutators of $H_0$ and $\hat{P}$).**
For every subset configuration $S \subseteq \Lambda^*$, the basis vector $\delta_S$ is an exact eigenvector:

$$
H_0 \delta_S = \left( \sum_{k \in S} k \right) \delta_S \tag{5.9}
$$

Consequently, $\hat{P} |\Omega\rangle = 0$. Both operators satisfy the same exact algebraic commutators. For all $k \in \Lambda^*$:

$$
[H_0, c_k^\dagger] = [\hat{P}, c_k^\dagger] = k c_k^\dagger, \quad [H_0, c_k] = [\hat{P}, c_k] = -k c_k \tag{5.10}
$$
