### Chapter 5: Position and Momentum Fermions

In this chapter, the abstract index set $\iota$ from Chapter 4 is instantiated as the centered momentum band $\iota = \Lambda^* = \mathrm{Band}(L)$. The algebraic, Fourier, and normal-ordering mechanics follow [Appendix A01](../appendices/a01_fourier_scalars_and_characters.md) and [Appendix A04](../appendices/a04_density_partitions_and_sugawara.md) and are proved completely in `Bosonize.Core.Ch05Fermions`.

*Lattice and Notation Conventions:*

- The spatial lattice is $\Lambda = \mathbb{Z}/L\mathbb{Z}$ (`Ch01.Lattice L`).

- The dual momentum band is $\Lambda^* = \{k \in \mathbb{Z} \mid -L < 2k \le L\}$ (`Ch01.Band L`). For $L = 2h$ even ($h > 0$), $\Lambda^* = \{-h+1, \dots, h\}$, retaining the positive Nyquist mode $h = L/2$.

- The state space is the fermionic Fock space over the band (`Ch05.FockSpace L`):
  $$
  \mathcal{F}(L) := \ell^2(\mathcal{P}(\Lambda^*)) \equiv \mathrm{EuclideanSpace} \ \mathbb{C} \ (\mathrm{Finset} \ (\Lambda^*))
  $$

- The operator algebra is $\mathrm{Operators}(L) := \mathrm{End}_{\mathbb{C}}(\mathcal{F}(L))$.

- The momentum CAR generators are $c_k := \mathrm{annihilation}(k)$ and $c_k^\dagger := \mathrm{creation}(k)$ as established in Chapter 4.

---

#### 5.1 Definitions

**Definition 5.1 (Position Fermions via Unitary Fourier Transform).**
Using the unitary Fourier normalization scalar $a = (\sqrt{L})^{-1}$ satisfying $L a^2 = 1$ (`A01.normalization L`), we define the spatial annihilation and creation operators by finite linear combinations over the momentum band:

$$
\forall x \in \Lambda, \quad c_x := a \sum_{k \in \Lambda^*} \chi_{\mathrm{band}}(k, x) c_k \tag{5.1}
$$

$$
\forall x \in \Lambda, \quad c_x^\dagger := a \sum_{k \in \Lambda^*} \chi_{\mathbb{Z}}(-k.\mathrm{val}, x.\mathrm{val}) c_k^\dagger \tag{5.2}
$$

where $\chi_{\mathrm{band}}(k, x) = \zeta^{k.\mathrm{val} \cdot x.\mathrm{val}}$ and $\chi_{\mathbb{Z}}(-k.\mathrm{val}, x.\mathrm{val}) = \zeta^{-k.\mathrm{val} \cdot x.\mathrm{val}}$ with canonical primitive root $\zeta = \exp(2\pi i / L)$.
The local spatial density operator is defined as:
$$
n_x := c_x^\dagger c_x^{\phantom{\dagger}} \tag{5.2a}
$$

*Adjoint Compatibility (`position_creation_eq_adjoint`):*
Because $\overline{\chi_{\mathrm{band}}(k, x)} = \chi_{\mathbb{Z}}(-k.\mathrm{val}, x.\mathrm{val})$, $\overline{a} = a$, and $(c_k)^\dagger = c_k^\dagger$, taking the Hilbert adjoint of $c_x$ yields:
$$
(c_x)^\dagger = \overline{a} \sum_{k \in \Lambda^*} \overline{\chi_{\mathrm{band}}(k, x)} (c_k)^\dagger = a \sum_{k \in \Lambda^*} \chi_{\mathbb{Z}}(-k.\mathrm{val}, x.\mathrm{val}) c_k^\dagger = c_x^\dagger
$$

---

**Definition 5.2 (Dirac Sea Configuration & Hamiltonians).**

1. **Total Particle Number Operator:**
   $$
   \hat{N}_{\mathrm{tot}} := \sum_{k \in \Lambda^*} n_k = \sum_{k \in \Lambda^*} c_k^\dagger c_k^{\phantom{\dagger}} \tag{5.3a}
   $$

2. **Bare Linearized Momentum Hamiltonian:**
   $$
   H_0 := \sum_{k \in \Lambda^*} k c_k^\dagger c_k^{\phantom{\dagger}} = \sum_{k \in \Lambda^*} k n_k \tag{5.3}
   $$
   Here $k \in \Lambda^*$ acts via its integer value coerced to complex scalars $(k.\mathrm{val} : \mathbb{C}) \bullet n_k$.

3. **The Dirac Fermi Sea Configuration (`seaConfiguration`):**
   In the centered band $\Lambda^*$, the half-filled Fermi sea occupies all nonpositive momentum modes:
   $$
   S_{\Omega} := \{k \in \Lambda^* \mid k \le 0\} = \{-h+1, -h+2, \dots, 0\} \tag{5.4a}
   $$
   The Dirac vacuum state is the corresponding occupation basis vector:
   $$
   |\Omega\rangle := \mathrm{ket}(S_{\Omega}) \in \mathcal{F}(L)
   $$

4. **Sea Energy and Shifted Hamiltonian:**
   The bare ground-state energy $E_\Omega := \sum_{k \in S_\Omega} k$ sums the negative momentum modes:
   $$
   E_\Omega = \sum_{j=-h+1}^0 j = -\frac{h(h-1)}{2} \tag{5.4}
   $$
   The physical shifted (normal-ordered) Hamiltonian is defined by:
   $$
   \hat{P} := H_0 - E_\Omega \cdot I \tag{5.5}
   $$
   so that $\hat{P} |\Omega\rangle = 0$.

---

#### 5.2 Theorems & Formal Proof Mechanics

**Theorem 5.3 (Exact Position CAR Inheritance).**
The position operators strictly inherit the Canonical Anticommutation Relations without any scalar distortion:
$$
\{c_x^{\phantom{\dagger}}, c_y^\dagger\} = \delta_{xy} I, \qquad \{c_x^{\phantom{\dagger}}, c_y^{\phantom{\dagger}}\} = 0, \qquad \{c_x^\dagger, c_y^\dagger\} = 0 \tag{5.6}
$$

*Proof (`position_mixed_car`, `position_annihilation_car`, `position_creation_car`):*
Expanding the mixed anticommutator using bilinearity:
$$
\{c_x^{\phantom{\dagger}}, c_y^\dagger\} = a^2 \sum_{k \in \Lambda^*} \sum_{p \in \Lambda^*} \chi(k, x) \chi(-p, y) \{c_k^{\phantom{\dagger}}, c_p^\dagger\}
$$
Applying the momentum CAR $\{c_k, c_p^\dagger\} = \delta_{kp} I$:
$$
= a^2 \sum_{k \in \Lambda^*} \chi(k, x) \chi(-k, y) I = a^2 \left( \sum_{k \in \Lambda^*} \zeta^{k(x - y)} \right) I
$$
By dual character orthogonality (`dual_character_orthogonality`, Theorem 3.3):
$$
\sum_{k \in \Lambda^*} \zeta^{k(x - y)} = L \cdot \delta_{xy}
$$
Therefore:
$$
\{c_x^{\phantom{\dagger}}, c_y^\dagger\} = a^2 (L \cdot \delta_{xy}) I = (a^2 L) \delta_{xy} I = \delta_{xy} I
$$
since $a = 1/\sqrt{L} \implies a^2 L = 1$. Similarly, $\{c_k, c_p\} = 0$ implies $\{c_x, c_y\} = 0$.

---

**Theorem 5.4 (Inverse Fourier Transform for Operators).**
The momentum operators are recovered exactly from position operators (`fourier_inversion_annihilation`):
$$
\forall k \in \Lambda^*, \quad c_k = a \sum_{x \in \Lambda} \chi_{\mathbb{Z}}(-k.\mathrm{val}, x.\mathrm{val}) c_x \tag{5.7}
$$
$$
\forall k \in \Lambda^*, \quad c_k^\dagger = a \sum_{x \in \Lambda} \chi_{\mathrm{band}}(k, x) c_x^\dagger \tag{5.7a}
$$

*Proof:*
Substituting $c_x = a \sum_{p} \chi(p, x) c_p$ into the RHS and interchanging sums:
$$
a \sum_{x \in \Lambda} \chi(-k, x) \left( a \sum_{p \in \Lambda^*} \chi(p, x) c_p \right) = a^2 \sum_{p \in \Lambda^*} \left( \sum_{x \in \Lambda} \chi(p - k, x) \right) c_p
$$
By spatial character orthogonality (`character_orthogonality`), $\sum_{x \in \Lambda} \chi(p-k, x) = L \cdot \delta_{pk}$.
Multiplying by $a^2 = 1/L$ leaves exactly $c_k$.

---

**Theorem 5.5 (Invariance of the Total Particle Number).**
The sum of local position densities equals the sum of momentum mode occupations (`sum_position_number_eq_total`):
$$
\sum_{x \in \Lambda} n_x = \sum_{x \in \Lambda} c_x^\dagger c_x^{\phantom{\dagger}} = \sum_{k \in \Lambda^*} c_k^\dagger c_k^{\phantom{\dagger}} = \hat{N}_{\mathrm{tot}} \tag{5.8}
$$

*Proof:*
Expanding $c_x^\dagger c_x$ into double momentum sums:
$$
\sum_{x \in \Lambda} c_x^\dagger c_x^{\phantom{\dagger}} = a^2 \sum_{k, p \in \Lambda^*} c_k^\dagger c_p^{\phantom{\dagger}} \left( \sum_{x \in \Lambda} \chi(-k, x) \chi(p, x) \right) = a^2 \sum_{k, p \in \Lambda^*} c_k^\dagger c_p^{\phantom{\dagger}} (L \cdot \delta_{kp}) = \sum_{k \in \Lambda^*} c_k^\dagger c_k^{\phantom{\dagger}}
$$

---

**Theorem 5.6 (Spectrum and Commutators of $H_0$ and $\hat{P}$).**

1. **Exact Eigenvalues on Basis States (`bare_hamiltonian_ket`):**
   For any subset configuration $S \subseteq \Lambda^*$:
   $$
   H_0 |S\rangle = \left( \sum_{k \in S} k \right) |S\rangle \tag{5.9}
   $$

2. **Vacuum Eigenvalues (`sea_ket_bare_energy`, `sea_ket_shifted_energy`):**
   $$
   H_0 |\Omega\rangle = E_\Omega |\Omega\rangle, \qquad \hat{P} |\Omega\rangle = 0
   $$
   For $L = 2h$ with $h > 0$, Lean verifies algebraically (`even_sea_energy`):
   $$
   E_\Omega = -\frac{h(h-1)}{2}
   $$

3. **Exact Commutators (`bare_hamiltonian_creation_commutator`, `bare_hamiltonian_annihilation_commutator`):**
   For all $k \in \Lambda^*$:
   $$
   [H_0, c_k^\dagger] = [\hat{P}, c_k^\dagger] = k c_k^\dagger, \qquad [H_0, c_k^{\phantom{\dagger}}] = [\hat{P}, c_k^{\phantom{\dagger}}] = -k c_k^{\phantom{\dagger}} \tag{5.10}
   $$
   *Proof:* In Lean, $[H_0, c_p^\dagger] = \sum_k k [n_k, c_p^\dagger]$. Applying the pure-algebraic CAR commutator $[n_k, c_p^\dagger] = \delta_{kp} c_p^\dagger$ (Lemma 4.1a) collapses the sum to $p c_p^\dagger$. Since $\hat{P} = H_0 - E_\Omega I$ differs by a central scalar multiple of the identity, $[\hat{P}, c_p^\dagger] = [H_0, c_p^\dagger]$.
