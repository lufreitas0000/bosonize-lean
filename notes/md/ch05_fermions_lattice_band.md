
### Chapter 5: Position and Momentum Fermions

In this chapter, the abstract index set $\iota$ from Chapter 4 is instantiated as the centered momentum band $\iota = \Lambda^*$.

*Notation Convention:*
- Spatial lattice positions are exclusively denoted by $x, y \in \Lambda = \mathbb{Z} / L\mathbb{Z}$.
- Momentum modes are exclusively denoted by $k, p, q \in \Lambda^* = \{k \in \mathbb{Z} \mid -L < 2k \le L\}$.
- Operators $c_k, c_k^\dagger$ are the exact CAR operators from Chapter 4 acting on $\mathrm{Fock}(\Lambda^*)$.

---

#### 5.1 Definitions

**Definition 5.1 (Position Fermions).**
For every spatial site $x \in \Lambda$, the position annihilation and creation operators are defined via the finite discrete Fourier transform:

$$
\forall x \in \Lambda, \quad c_x := \frac{1}{\sqrt{L}} \sum_{k \in \Lambda^*} \zeta^{kx} c_k \tag{5.1}
$$

$$
\forall x \in \Lambda, \quad c_x^\dagger := \frac{1}{\sqrt{L}} \sum_{k \in \Lambda^*} \zeta^{-kx} c_k^\dagger \tag{5.2}
$$

where $\zeta = e^{2\pi i / L}$ is the chosen primitive $L$-th root of unity. The local spatial density operator is $n_x := c_x^\dagger c_x$.

**Definition 5.2 (Linearized Free Hamiltonian).**
In units where the scaled Fermi velocity $2\pi v / L = 1$, the momentum-space linearized Hamiltonian is:

$$
H_0 := \sum_{k \in \Lambda^*} k n_k = \sum_{k \in \Lambda^*} k c_k^\dagger c_k \tag{5.3}
$$

---

#### 5.2 Lemmas and Theorems

**Lemma 5.3 (Position CAR).**
The position operators strictly inherit the Canonical Anticommutation Relations. For all $x, y \in \Lambda$:

$$
\{c_x, c_y^\dagger\} = \delta_{xy} I, \quad \{c_x, c_y\} = 0, \quad \{c_x^\dagger, c_y^\dagger\} = 0 \tag{5.4}
$$

and $c_x^\dagger = (c_x)^\dagger$ with respect to the $\ell^2$ inner product on $\mathrm{Fock}(\Lambda^*)$.

*Proof Sketch:*
Expanding the anticommutator using linearity:
$$
\{c_x, c_y^\dagger\} = \frac{1}{L} \sum_{k, p \in \Lambda^*} \zeta^{kx} \zeta^{-py} \{c_k, c_p^\dagger\} = \frac{1}{L} \sum_{k \in \Lambda^*} \zeta^{k(x-y)} I = \delta_{xy} I
$$
The evaluation utilizes the dual plane wave orthogonality (Lemma 3.4). Crucially, this algebraic derivation requires no Jordan–Wigner phase calculations. $\blacksquare$

**Lemma 5.4 (Inverse Fourier Transform).**
The momentum operators can be recovered from the position operators. For all $k \in \Lambda^*$:

$$
c_k = \frac{1}{\sqrt{L}} \sum_{x \in \Lambda} \zeta^{-kx} c_x \tag{5.5}
$$

**Lemma 5.5 (Invariance of Total Particle Number).**
The sum of local densities equals the sum of mode occupation numbers:

$$
\sum_{x \in \Lambda} n_x = \sum_{k \in \Lambda^*} n_k = \hat{N}_{\mathrm{tot}} \tag{5.6}
$$

**Lemma 5.6 (Spectrum and Commutators of $H_0$).**
For every subset configuration $S \subseteq \Lambda^*$, the basis vector $\delta_S$ is an exact eigenvector of $H_0$:

$$
H_0 \delta_S = \left( \sum_{k \in S} k \right) \delta_S \tag{5.7}
$$

Furthermore, for all $k \in \Lambda^*$:

$$
[H_0, c_k^\dagger] = k c_k^\dagger, \quad [H_0, c_k] = -k c_k \tag{5.8}
$$

---

#### 5.3 Technical Notes for the Lean 4 Formalization (Chapter 5)

1. **Root of Unity Management:**
   - Define $\zeta$ using `IsPrimitiveRoot ζ L`.
   - The pairing $\zeta^{kx}$ involves an integer $k \in \Lambda^*$ and a modular class $x \in \mathbb{Z} / L\mathbb{Z}$. In Lean, one must take a representative `x.val : ℤ` and apply `IsPrimitiveRoot.zpow_eq_one_iff_dvd` to prove well-definedness independent of the chosen representative.
2. **Double Sum Swapping:**
   - Proving Lemma 5.3 and Lemma 5.5 requires reordering finite sums:
     `Finset.sum_comm` followed by factoring out constant operators using `Finset.mul_sum` and `Finset.sum_mul`.
   - The orthogonality collapse $\sum_{k \in \Lambda^*} \zeta^{k(x-y)} = L \delta_{xy}$ requires a bridge lemma connecting the `Finset` sum over the subtype `LambdaDual L` to a sum over the cyclic group `ZMod L`.
3. **Operator Identity Scope:**
   - The operators $c_x$ and $H_0$ live in the endomorphism algebra `Module.End ℂ (FockSpace (LambdaDual L))`.
   - Since all sums are over finite sets (`Finset.univ` where `Fintype (LambdaDual L)` is active), no topological convergence, limits, or domain issues arise. Proofs of $[H_0, c_k^\dagger] = k c_k^\dagger$ follow from the CAR commutator identity (Lemma 4.7) by applying linearity:
     $$
     [H_0, c_k^\dagger] = \sum_{p \in \Lambda^*} p [n_p, c_k^\dagger] = \sum_{p \in \Lambda^*} p \, \delta_{pk} c_k^\dagger = k c_k^\dagger
     $$
