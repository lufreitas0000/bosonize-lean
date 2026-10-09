### Chapter 21: Gaps & Spin-1/2 Generalizations

By expanding our multi-species index set, we will formalize **Spin-Charge Separation**. We will also formalize Umklapp scattering, sector leakage, and discrete RG flow following [Appendix A09](../appendices/a09_duality_spin_and_umklapp.md) and [Appendix A10](../appendices/a10_discrete_rg_and_schrieffer_wolff.md).

#### 21.1 The Spinful Index Set and Parity Sublattice

**Definition 21.1 (Spinful Species Index).**
The complete multi-species index set is $\mathcal{C} = \{R, L\} \times \{\uparrow, \downarrow\}$.

*Lean 4 Proof Strategy:*
Define an inductive type or an enum `Species` with constructors `R` and `L`, and an enum `Spin` with constructors `up` and `down`. Then define the `Index` type as the Cartesian product `Species × Spin`. This allows for structural induction and exhaustive pattern matching on the species indices.

**Definition 21.2 (Raw Charge and Spin Density Modes).**
To avoid irrational coefficients like $\sqrt{2}$ in the algebra, we define the raw integer charge ($c$) and spin ($s$) currents:
$$
R_{m, \nu}^c := \rho_{m, \nu, \uparrow} + \rho_{m, \nu, \downarrow} \tag{21.1}
$$
$$
R_{m, \nu}^s := \rho_{m, \nu, \uparrow} - \rho_{m, \nu, \downarrow} \tag{21.2}
$$
The zero-mode charges satisfy $Q_c \equiv Q_s \pmod 2$. The physical states are strictly confined to this parity-constrained charge sublattice.

*Lean 4 Proof Strategy:*
Define these combinations as linear maps or functions of the individual spin-species density modes. Ensure the definition uses exact integer coefficients to preserve computability. Define a predicate `IsParityConstrained` over the zero-mode charges ensuring $Q_c \equiv Q_s \pmod 2$.

**Lemma 21.3 (Algebraic Spin-Charge Decoupling).**
Because $[\rho_{\uparrow}, \rho_{\downarrow}] = 0$, evaluating $[R^c, R^s]$ on the budget subspace requires the difference between the up and down edge commutators to vanish. Within the uniform frozen-margin regime, the cross-commutator is strictly zero. The self-CCR coefficients evaluate to exactly $2m$:
$$
[R_{m, \nu}^c, R_{n, \nu'}^s] = 0 \tag{21.3}
$$
$$
[R_{-m, \nu}^c, R_{m, \nu}^c] = [R_{-m, \nu}^s, R_{m, \nu}^s] = 2m \tag{21.4}
$$

If the Hamiltonian is spin-symmetric, it algebraically factorizes into $H_{\text{charge}}[R^c] + H_{\text{spin}}[R^s]$, producing distinct algebraic eigenvalues $u_c \neq u_s$ provided the parameters are non-degenerate.

*Lean 4 Proof Strategy:*
1. **Auxiliary Lemma 1:** Prove that density operators for distinct spins commute, $[\rho_{m,\nu,\uparrow}, \rho_{n,\nu',\downarrow}] = 0$.
2. **Auxiliary Lemma 2:** Expand the commutators $[R^c, R^s]$ using bilinearity of the commutator and apply Auxiliary Lemma 1.
3. For the self-CCR (Eq 21.4), use the known CCR for the individual spin species $[\rho_{-m,\nu,s}, \rho_{m,\nu,s}] = m$ and bilinearity to show the cross terms cancel or sum to $2m$. The proof will rely heavily on the `ring` or `abel` tactic for simplification of commutators.

#### 21.2 The Spin-Singlet Cooper Pair

**Definition 21.4 (Singlet Cooper Pair).**
The macroscopic singlet pairing operator is:
$$
O_{SSC}(x) := c_{(R, \uparrow, x)} c_{(L, \downarrow, x)} - c_{(R, \downarrow, x)} c_{(L, \uparrow, x)} \tag{21.5}
$$

The first term lowers charges $(R\uparrow, L\downarrow)$, while the second lowers $(R\downarrow, L\uparrow)$. Because these target distinct charge vectors, each term requires its own Klein zero-mode product:
$$
K_1 := F_{R,\uparrow} F_{L,\downarrow} Z_{R,\uparrow} Z_{L,\downarrow}, \quad K_2 := F_{R,\downarrow} F_{L,\uparrow} Z_{R,\downarrow} Z_{L,\uparrow} \tag{21.6}
$$
Reconstructing the single-species fields via $\rho_\uparrow = \frac{1}{2}(R^c + R^s)$ and $\rho_\downarrow = \frac{1}{2}(R^c - R^s)$, both terms share the collective charge phase fields, while carrying distinct Klein and spin-phase factors:
$$
O_{SSC}(x) = \frac{1}{L} \operatorname{expNil}\left[\frac{1}{2}(W^-_{c,R} + W^-_{c,L})\right] \operatorname{expNil}\left[\frac{1}{2}(W^+_{c,R} + W^+_{c,L})\right] \left( K_1 \mathcal{E}_{s,1}(x) - K_2 \mathcal{E}_{s,2}(x) \right) \tag{21.7}
$$
where $\mathcal{E}_{s,1}(x) = \operatorname{expNil}[\frac{1}{2}(W^-_{s,R}-W^-_{s,L})]\operatorname{expNil}[\frac{1}{2}(W^+_{s,R}-W^+_{s,L})]$ and $\mathcal{E}_{s,2}(x)$ has opposite relative spin-phase signs.

*Lean 4 Proof Strategy:*
Define `O_SSC` directly in terms of the fundamental fermion annihilation operators. To formalize the factorized form, define the collective charge and spin phase fields $W^c$ and $W^s$, proving that each of the two terms in the difference receives its own verified Klein factor ($K_1, K_2$) shifting into the appropriate target sector.

#### 21.3 Umklapp Scattering, Sector Leakage, and Discrete RG

**Definition 21.5 (The Exact Umklapp Operator).**
The Umklapp scattering operator destroys two $R$ particles and creates two $L$ particles of opposite spins:
$$
O_{U}(x) := c^\dagger_{(L, \uparrow, x)} c^\dagger_{(L, \downarrow, x)} c_{(R, \downarrow, x)} c_{(R, \uparrow, x)} \tag{21.8}
$$

*Lean 4 Proof Strategy:*
Define $O_U(x)$ explicitly as a product of four creation/annihilation operators. It will be represented as an element in the established operator algebra.

**Lemma 21.6 (Charge Sector Shifts).**
Each fundamental creator adds exactly 1 to its species charge. Evaluated via the exact CAR commutators, the branch shifts are strictly:
$$
\Delta \vec{N} = e_{L,\uparrow} + e_{L,\downarrow} - e_{R,\downarrow} - e_{R,\uparrow} \tag{21.9}
$$
*(Note: Each species shifts by exactly 1, not 2; the total branch shift is $\pm 2$)*.

*Lean 4 Proof Strategy:*
1. **Auxiliary Lemma:** Show that commutators of number operators with creation/annihilation operators yield shifted charges, e.g., $[N_{\nu, s}, c^\dagger_{\nu', s'}] = \delta_{\nu, \nu'} \delta_{s, s'} c^\dagger_{\nu', s'}$.
2. Apply the commutator derivation over the four-fermion product $O_U(x)$ sequentially using the Leibniz rule for commutators. The resulting vector shift will exactly match the stated branch shifts.

**Theorem 21.7 (Charge Sector Non-Conservation and Conditional Budget Leakage Criterion).**
The Umklapp operator generates non-zero charge-sector shifts $\Delta \vec{N} = (+1, +1, -1, -1)$:
$$
[\hat{N}_{\nu,s}, O_U(x)] = (\Delta \vec{N})_{\nu,s} O_U(x). \tag{21.10}
$$
1. *Conditional Leakage Criterion:* Let $\mathcal{B}_{K, \vec{N}_{\max}}$ be an energy-and-charge budget space. Given coupling $g_U \neq 0$, if there exists an occupation state $|\psi\rangle \in \mathcal{B}_{K, \vec{N}_{\max}}$ located at the charge boundary (e.g., $N_{L,\uparrow} = N_{\max}$) such that the spatially summed action $H_U |\psi\rangle = \frac{g_U}{L} \sum_{x \in \Lambda} (O_U(x) + O_U^\dagger(x)) |\psi\rangle \neq 0$ (i.e. not annihilated by Pauli exclusion and satisfying lattice momentum conservation), then $H_U |\psi\rangle$ carries non-zero component in target charge sector $\vec{N} + \Delta \vec{N} \not\le \vec{N}_{\max}$, proving:
$$
H_U |\psi\rangle \notin \mathcal{B}_{K, \vec{N}_{\max}}.
$$
2. *Non-block-diagonality:* Under this criterion, the budget projection $P_{K,\vec{N}_{\max}}$ does not commute with $H_U$; $H_U$ cannot be diagonalized within a single fixed-charge budget space.

> [!NOTE]
> *Physical Motivation (KT Flow and Mott Gap):* In continuous field theory, Umklapp scattering generates second-order loop corrections described by Kosterlitz-Thouless (KT) scaling equations, driving the opening of a charge Mott gap. On the finite discrete lattice, budget leakage establishes the algebraic non-invariance of the truncated budget space; deriving the thermodynamic Mott gap or KT flow equations requires a separate asymptotic scaling construction.

*Lean 4 Proof Strategy:*
1. **Auxiliary Lemma 1:** Formalize the charge commutator $[\hat{N}_{\nu,s}, O_U(x)] = (\Delta \vec{N})_{\nu,s} O_U(x)$ from CAR.
2. **Auxiliary Lemma 2:** State the conditional leakage theorem: assuming a boundary state $|\psi\rangle$ with non-zero spatial sum $H_U |\psi\rangle \neq 0$, deduce $H_U |\psi\rangle \notin \mathcal{B}_{K, \vec{N}_{\max}}$ by evaluating the charge observable $\hat{N}_{L,\uparrow}$.
3. Separate the discrete algebraic non-invariance result from continuous Wilsonian RG flow or thermodynamic gap claims.
4. Separate the discrete algebraic non-invariance result from continuous Wilsonian RG flow or thermodynamic gap claims.

#### 21.4 Technical Notes for the Lean 4 Formalization

1. **Parity Sublattice Constraints:**
   * Enforce the condition $Q_c \equiv Q_s \pmod 2$ strictly when defining the available ground states in Lean.
2. **Raw Integer Fields:**
   * Do not normalize $R^c$ or $R^s$ with $\sqrt{2}$. Keep all coefficients rational/integer, accepting the explicit factors of $2m$ in the CCR evaluation.
3. **Leakage Witnesses:**
   * Formalize leakage by constructing a specific non-zero state on the boundary and demonstrating that applying $H_U$ violates the budget type bounds exactly.
