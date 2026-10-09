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

*Lean 4 Proof Strategy:*
Define `c_x` and `c_x^\dagger` as linear combinations of the momentum operators `c_k` and `c_k^\dagger`. Utilize the discrete Fourier transform definitions where the character `χ` is represented as a function `Λ* × Λ → ℂ` (or an appropriate root of unity in an algebra). The normalization constant `a` is defined as `1 / √L`.

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

*Lean 4 Proof Strategy:*
Define `H_0` using a `Finset.sum` over `Λ*` of the terms `k • (c_k^\dagger * c_k)`. Define the Dirac vacuum state `Ω` explicitly (likely as a specific `Basis` vector corresponding to the filled Fermi sea) and compute its eigenvalue `E_Ω` by summing the arithmetic progression from `-h+1` to `0`. Finally, define the normal-ordered `P` as `H_0 - E_Ω • 1`.

---

#### 5.2 Lemmas and Theorems

**Lemma 5.3 (Position CAR).**
Because the DFT mapping is scaled by the exact real unitary constant $1/\sqrt{L}$ over the complex Euclidean space, the position operators strictly inherit the Canonical Anticommutation Relations without any scalar scaling artifacts. For all $x, y \in \Lambda$:

$$
\{c_x, c_y^\dagger\} = \delta_{xy} I, \quad \{c_x, c_y\} = 0, \quad \{c_x^\dagger, c_y^\dagger\} = 0 \tag{5.6}
$$

*Lean 4 Proof Strategy:*
Use the bilinearity of the anticommutator to expand `{c_x, c_y^\dagger}` into a double sum over momentum modes. The inner sum evaluates the orthogonality relation of the characters: `∑_k χ(k, x) χ(-k, y) = L δ_{xy}`. This factor of `L` precisely cancels the `a^2 = 1/L` normalization. Use the existing CAR rules for `c_k` via `simp` to complete the reduction.

**Lemma 5.4 (Inverse Fourier Transform).**
The momentum operators can be recovered from the position operators. For all $k \in \Lambda^*$:

$$
c_k = a \sum_{x \in \Lambda} \chi(-k,x) c_x \tag{5.7}
$$

*Lean 4 Proof Strategy:*
Apply the inverse discrete Fourier transform. Start with the right-hand side, substitute the definition of `c_x`, and interchange the sums. The sum over the spatial lattice `x ∈ Λ` of `χ(-k, x) χ(q, x)` will yield `L δ_{kq}` by character orthogonality, which isolates `c_k` after canceling the normalization `1/L`.

**Lemma 5.5 (Invariance of Total Particle Number).**
The sum of local densities equals the sum of mode occupation numbers:

$$
\sum_{x \in \Lambda} n_x = \sum_{k \in \Lambda^*} n_k = \hat{N}_{\mathrm{tot}} \tag{5.8}
$$

*Lean 4 Proof Strategy:*
Expand `n_x = c_x^\dagger c_x` using the definitions of the position operators. Interchange the summation order to sum over `x` first. Applying the spatial character orthogonality relation `∑_x χ(-k, x) χ(q, x) = L δ_{kq}` simplifies the resulting double momentum sum into a single sum over `k` of `c_k^\dagger c_k`, which is exactly `∑_k n_k`.

**Lemma 5.6 (Spectrum and Commutators of $H_0$ and $\hat{P}$).**
For every subset configuration $S \subseteq \Lambda^*$, the basis vector $\delta_S$ is an exact eigenvector:

$$
H_0 \delta_S = \left( \sum_{k \in S} k \right) \delta_S \tag{5.9}
$$

Consequently, $\hat{P} |\Omega\rangle = 0$. Both operators satisfy the same exact algebraic commutators. For all $k \in \Lambda^*$:

$$
[H_0, c_k^\dagger] = [\hat{P}, c_k^\dagger] = k c_k^\dagger, \quad [H_0, c_k] = [\hat{P}, c_k] = -k c_k \tag{5.10}
$$

*Lean 4 Proof Strategy:*
For the eigenvector property, use induction on the size of the subset `S` or apply the operators directly using the established module action on the Fock space basis. For the commutators, express `[H_0, c_q^\dagger]` as `∑_k k [c_k^\dagger c_k, c_q^\dagger]`. Use the commutator identity `[AB, C] = A{B, C} - {A, C}B` along with the CAR to show that only the `k = q` term survives, giving `q c_q^\dagger`. The shift by `E_Ω I` in `P` commutes with everything, trivially preserving the commutators.
