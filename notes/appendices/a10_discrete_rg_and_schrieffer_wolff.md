# Appendix A10: Discrete Energy-Shell Partitioning and Schrieffer-Wolff Perturbation Theory

## Algebraic Energy-Shell Filtering vs. Mode Decimation

In continuum field theory, Renormalization Group (RG) flow integrates out infinitesimal high-momentum shells. On a discrete finite lattice with a strict energy budget $K$, infinitesimal momentum integration is impossible.

We formalize discrete energy-shell projection and the **Schrieffer-Wolff Transformation (SWT)** as a purely algebraic method on finite-dimensional subspaces.

> [!IMPORTANT]
> **Energy Shell vs. Mode Decimation:**
> The decomposition $\mathcal{B}_K = \mathcal{B}_{K-1} \oplus \mathcal{H}_K$ is an **energy-shell** decomposition, *not* single-mode decimation.
> For example, with weighted boson modes 1 and 2 at $K=2$, the budget $\mathcal{B}_2$ has basis $\{1, X_1, X_1^2, X_2\}$.
> - The energy-shell projection to $\mathcal{B}_1$ keeps $\{1, X_1\}$, discarding both $X_1^2$ and $X_2$ because their partition energy is 2.
> - Decimating mode 2 alone would keep $\{1, X_1, X_1^2\}$, which is a different subspace and a different projection.

---

### Step 1: Subspace Partitioning of the Budget

**Definition (Energy Budget Subspaces):**
The energy budget space $\mathcal{B}_K$ splits into an orthogonal direct sum of energy shells:
$$
\mathcal{B}_K = \mathcal{P} \oplus \mathcal{Q}
$$
* $\mathcal{P} := \mathcal{B}_{K-1}$ is the low-energy target subspace (retained states of total energy $\le K-1$).
* $\mathcal{Q} := \mathcal{H}_K$ is the maximal-energy boundary shell (states with excitation energy exactly equal to $K$).

Let $P$ and $Q$ be the corresponding orthogonal projectors ($P + Q = I$, $PQ = 0$, $P^\dagger = P$, $Q^\dagger = Q$).

*Lean 4 Proof Strategy:*
Formalize $\mathcal{B}_K$ as an orthogonal direct sum of submodules using `DirectSum` or `Submodule.orthogonal`. Since $\mathcal{B}_K$ is finite-dimensional, use `FiniteDimensional`. Formalize $P$ and $Q$ as orthogonal projections, proving $P + Q = I$ and $P Q = 0$.

---

### Step 2: Solvable Baseline and Perturbation

**Definition (Solvable Baseline and Block Decomposition):**
Consider a self-adjoint Hamiltonian $H = H_0 + t V$ on $\mathcal{B}_K$, where:
1. $H_0$ is a solvable baseline that commutes with the projectors:
$$
[P, H_0] = 0, \quad [Q, H_0] = 0.
$$
   Because $\mathcal{P}$ and $\mathcal{Q}$ are $H_0$-invariant, there exists an orthonormal eigenbasis $\{|\lambda\rangle\}$ of $H_0$ adapted to the direct sum $\mathcal{P} \oplus \mathcal{Q}$ (each basis vector $|\lambda\rangle$ lies entirely in either $\mathcal{P}$ or $\mathcal{Q}$, even across degenerate eigenspaces of $H_0$), with real eigenvalues $E_\lambda$.
2. $V$ is a self-adjoint perturbation, partitioned into block-diagonal and block-off-diagonal parts:
$$
V_{\text{diag}} := PVP + QVQ, \quad V_{\text{off}} := PVQ + QVP.
$$
3. *Non-resonance hypothesis:* For all pairs $|\lambda\rangle \in \mathcal{P}$ and $|\mu\rangle \in \mathcal{Q}$, if the coupling is non-zero ($\langle \lambda | V_{\text{off}} | \mu \rangle \neq 0$), the spectral gap is non-zero:
$$
E_\lambda \neq E_\mu.
$$
   (Uncoupled cross-block pairs with $\langle \lambda | V_{\text{off}} | \mu \rangle = 0$ are permitted to have $E_\lambda = E_\mu$.)

> [!WARNING]
> *Baseline Solvability:*
> When inter-branch forward scattering $g_2 \neq 0$, the pairing Hamiltonian $H_{\text{pair}}$ contains $C_R C_L$, which creates pairs from the bare vacuum and is **not** diagonal on the bare Haldane partition basis.
> Therefore, $H_0$ cannot simply be chosen as bare $H_{\text{Lutt}}$ while assuming it is simultaneously diagonal on the bare partition basis. A valid baseline must be independently block-diagonalized, or chosen as the free Sugawara Hamiltonian $H_0 = H_{\text{sug}}$.

---

### Step 3: The Generator Equation

**Theorem (First-Order Generator Solution):**
Under the non-resonance hypothesis, there exists an anti-Hermitian operator $S_1 \in \mathrm{End}_{\mathbb{C}}(\mathcal{B}_K)$ ($S_1^\dagger = -S_1$) satisfying:
$$
[S_1, H_0] = -V_{\text{off}}.
$$
In the adapted eigenbasis of $H_0$, $S_1$ has the piecewise matrix elements:
$$
\langle \lambda | S_1 | \mu \rangle = \begin{cases}
\dfrac{\langle \lambda | V_{\text{off}} | \mu \rangle}{E_\lambda - E_\mu} & \text{if } (|\lambda\rangle \in \mathcal{P}, |\mu\rangle \in \mathcal{Q} \text{ or vice versa}) \text{ and } \langle \lambda | V_{\text{off}} | \mu \rangle \neq 0, \\
0 & \text{otherwise}.
\end{cases}
$$
Defining $\langle \lambda | S_1 | \mu \rangle = 0$ whenever $\langle \lambda | V_{\text{off}} | \mu \rangle = 0$ avoids any undefined $0/0$ division when uncoupled cross-block pairs are degenerate ($E_\lambda = E_\mu$).

Because $V_{\text{off}}^\dagger = V_{\text{off}}$ and $E_\lambda, E_\mu \in \mathbb{R}$, $S_1$ is strictly anti-Hermitian. Direct evaluation of the commutator yields:
$$
\langle \lambda | [S_1, H_0] | \mu \rangle = (E_\mu - E_\lambda) \langle \lambda | S_1 | \mu \rangle = - \langle \lambda | V_{\text{off}} | \mu \rangle,
$$
which holds identically whether $\langle \lambda | V_{\text{off}} | \mu \rangle$ is non-zero (via cancellation of the non-zero difference) or zero ($0 \cdot (E_\mu - E_\lambda) = 0 = -0$).

*Lean 4 Proof Strategy:*
Formalize the generator equation on the adapted eigenbasis. State anti-adjointness as `LinearMap.adjoint S₁ = -S₁` (or `S₁ᴴ=-S₁` for matrices), using self-adjointness of Voff. Require distinct real energies only on nonzero coupled entries; define uncoupled entries as zero. Check an adjoint predicate name before using it.

---

### Step 4: Effective Hamiltonian Modulo $t^3$

**Theorem (Second-Order Schrieffer-Wolff Effective Hamiltonian):**
For $H(t) = H_0 + t V$, unitary rotation by $e^{t S_1}$ eliminates off-diagonal coupling at first order in $t$.
Projecting onto the low-energy subspace $\mathcal{P} = \mathcal{B}_{K-1}$, the effective Hamiltonian is given **modulo $t^3$** (in formal perturbation theory) by:
$$
H_{\text{eff}}(t) = P H_0 P + t P V P + \frac{t^2}{2} P [S_1, V] P + O(t^3).
$$

> [!CAUTION]
> **SWT is Not an Exact Finite-Matrix Equality:**
> The second-order expression $P H_0 P + t P V P + \frac{t^2}{2} P [S_1, V] P$ is **not** the exact transformed Hamiltonian $P e^{t S_1} (H_0 + t V) e^{-t S_1} P$.
> Higher-order nested commutators contribute at $O(t^3)$ and beyond.
>
> **Counterexample Witness (2×2 Matrix):**
> Consider:
> $$
> H_0 = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}, \quad
> V = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}, \quad
> S_1 = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}, \quad
> P = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}.
> $$
> Here $[S_1, H_0] = -V$, and $S_1^\dagger = -S_1$. Direct matrix expansion yields:
> $$
> P e^{t S_1} (H_0 + t V) e^{-t S_1} P = (-t^2 + t^4 + \cdots) P.
> $$
> The exact lower eigenvalue of $H_0 + t V$ at $t = 2/3$ is $-1/3$, whereas the second-order truncation provides $-t^2 = -4/9$. Moreover, the remaining off-diagonal block at order $t^3$ has coefficient $-4/3 \neq 0$.
> Thus, the second-order formula is valid only modulo $t^3$ (or with an explicit norm remainder bound), not as an unconstrained operator equality.

**Corollary (Forward Implication on Off-Block Vanishing):**
If the perturbation satisfies $P V Q = Q V P = 0$, then $V_{\text{off}} = 0$, which implies $S_1 = 0$ and $P [S_1, V] P = 0$. In this case, the second-order cross-block correction vanishes identically, and $H_{\text{eff}} = P (H_0 + t V) P$ is exact for the identity rotation S₁=0; no higher-order rotation terms occur in this case.

> [!WARNING]
> **No "If and Only If" Equivalence for the Second-Order Correction:**
> The vanishing of the second-order correction $P [S_1, V] P = 0$ does **not** imply $P V Q = 0$.
>
> **Counterexample Witness ($3\times 3$ Matrix):**
> Consider the 3-dimensional system partitioned into $\mathcal{P} = \operatorname{span}(e_1)$ and $\mathcal{Q} = \operatorname{span}(e_2, e_3)$:
> $$
> H_0 = \begin{pmatrix} 0 & 0 & 0 \\ 0 & -1 & 0 \\ 0 & 0 & 1 \end{pmatrix}, \quad
> P = \begin{pmatrix} 1 & 0 & 0 \\ 0 & 0 & 0 \\ 0 & 0 & 0 \end{pmatrix}, \quad
> V = \begin{pmatrix} 0 & 1 & 1 \\ 1 & 0 & 0 \\ 1 & 0 & 0 \end{pmatrix}.
> $$
> Here $P V P = 0$, $Q V Q = 0$, so $V_{\text{off}} = V$, and $P V Q = \begin{pmatrix} 0 & 1 & 1 \\ 0 & 0 & 0 \\ 0 & 0 & 0 \end{pmatrix} \neq 0$.
> All non-zero cross-block couplings are non-resonant ($E_1 - E_2 = 1 \neq 0$, $E_1 - E_3 = -1 \neq 0$). The anti-Hermitian generator $S_1$ has matrix elements:
> $$
> \langle 1 | S_1 | 2 \rangle = \frac{1}{0 - (-1)} = 1, \quad \langle 1 | S_1 | 3 \rangle = \frac{1}{0 - 1} = -1 \implies S_1 = \begin{pmatrix} 0 & 1 & -1 \\ -1 & 0 & 0 \\ 1 & 0 & 0 \end{pmatrix}.
> $$
> Computing the matrix product:
> $$
> (S_1 V)_{11} = 1 \cdot 1 + (-1) \cdot 1 = 0, \quad (V S_1)_{11} = 1 \cdot (-1) + 1 \cdot 1 = 0 \implies (P [S_1, V] P)_{11} = 0.
> $$
> Thus $P [S_1, V] P = 0$ holds identically, yet $P V Q \neq 0$. The two opposite energy denominators ($+1$ and $-1$) in the intermediate sum cancel out. Therefore, only the forward implication $P V Q = 0 \implies S_1 = 0 \implies P [S_1, V] P = 0$ is valid; asserting an "if and only if" equivalence is mathematically false.

---

## Physical Applications and Motivational Status

The following applications provide physical motivation and context from condensed matter theory; they are distinct from the exact finite-algebraic identities established above.

### 1. Non-Linear Dispersion Curvature (Physical Motivation)
If a non-linear band dispersion $\varepsilon(k) = v_F k + \frac{k^2}{2m^*}$ introduces cubic mode couplings $V_{\text{cubic}} \propto \sum \rho_p \rho_q \rho_{-(p+q)}$:
* The second-order term $\frac{1}{2} P [S_1, V_{\text{cubic}}] P$ generates effective 4-mode interactions in the continuum limit.
* In physical scaling theory, this leads to mode-dependent sound velocities and finite plasmon lifetimes. On a finite lattice, Hermitian Hamiltonians have purely real spectra; defining an actual decay lifetime requires an operational or thermodynamic continuum formulation.

### 2. Umklapp Scattering and Mott Transition (Physical Motivation)
For the half-filling Umklapp perturbation $H_U \propto \sum_x (O_U(x) + O_U^\dagger(x))$:
* In continuum bosonization, $O_U \sim \cos(\sqrt{8\pi}\phi_c)$, and second-order operator product expansions yield the Kosterlitz-Thouless (KT) flow equations, predicting the opening of a charge Mott gap.
* On the discrete finite lattice, revised Theorem 21.7 requires a nonzero outward component outside the chosen budget. Lemma 21.8 supplies a direct occupation-coefficient witness family with exact sign and coefficient `−g_U/L²`. Charge shifts or nonzero total HU action alone do not establish leakage, KT flow, or a Mott gap.
