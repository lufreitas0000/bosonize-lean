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

For a quadratic current Hamiltonian whose spin-index coupling matrices have the exchange-symmetric form $\begin{pmatrix}a&b\\b&a\end{pmatrix}$, substitution $\rho_\uparrow=(R^c+R^s)/2$ and $\rho_\downarrow=(R^c-R^s)/2$ gives charge/spin blocks with coefficients $(a+b)/2$ and $(a-b)/2$ in the raw-current convention. This is a block decomposition, not a claim about every spin-symmetric interacting Hamiltonian or a tensor product of independent truncated budgets. In a stable pairing model, unequal positive velocities require the explicit condition $v_{1,c}^2-v_{2,c}^2\ne v_{1,s}^2-v_{2,s}^2$; the free spin-independent case can have equal velocities.

*Lean 4 Proof Strategy:*
1. **Auxiliary Lemma 1:** Prove that density operators for distinct spins commute, $[\rho_{m,\nu,\uparrow}, \rho_{n,\nu',\downarrow}] = 0$.
2. **Auxiliary Lemma 2:** Expand the commutators $[R^c, R^s]$ using bilinearity of the commutator and apply Auxiliary Lemma 1.
3. For the self-CCR (Eq 21.4), use the known CCR for the individual spin species $[\rho_{-m,\nu,s}, \rho_{m,\nu,s}] = m$ and bilinearity to show the cross terms cancel or sum to $2m$. Expand products with distributivity and the proved CAR/CCR rules. Use `abel` for additive rearrangement, `noncomm_ring` for polynomial identities preserving factor order, and `ring` only for scalar coefficients.

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
**Lemma 21.4a (Two Typed Singlet Channels with Residuals).** Let $V_s$ have charge $N$. For channel $j=1$ use $(a,b)=(R\uparrow,L\downarrow)$ and for $j=2$ use $(R\downarrow,L\uparrow)$. Let $V_{m,j}$ have charge $N-e_b$ and $V_{t,j}$ have charge $N-e_a-e_b$, with separately specified cutoffs. Put
$$
B_{b,j}=p_{m,j}c_b i_s,\quad B_{a,j}=p_{t,j}c_a i_{m,j},\quad
\mathcal R_j=p_{t,j}c_a(I-P_{m,j})c_b i_s.
$$
Choose a common target $W$ containing the orthogonal sum of the two target budgets, with inclusions $j_1,j_2$ and projection $p_W$. Then the exact projected singlet is
$$
p_W O_{SSC}(x)i_s=
 j_1(B_{a,1}\circ B_{b,1}+\mathcal R_1)
 -j_2(B_{a,2}\circ B_{b,2}+\mathcal R_2). \tag{21.7}
$$
Here $W$ is exactly that target sum for the displayed equality; a larger $W$ requires retaining its extra projected components as well. When using Chapter 14 candidate maps for $B$, verify each single-field criterion first. Distinct Klein products $K_1,K_2$ preserve the distinct target charge shifts. Reconstructing phases by $\rho_{\uparrow/\downarrow}=(R^c\pm R^s)/2$ is algebraic; combining compressed exponentials into a common charge factor requires an additional commutation/cutoff theorem and is not part of (21.7).

*Lean 4 Proof Strategy:*
Define O_SSC directly by CAR words. Prove each channel by the Chapter 20/A03 intermediate-projection insertion, then include the results into the common orthogonal target. Prove target charge orthogonality and the explicit Klein phases. No unidentified spin exponentials or subtraction of maps with distinct codomains is used.

#### 21.3 Umklapp Scattering, Sector Leakage, and Discrete RG

**Definition 21.5 (The Exact Umklapp Operator).**
The Umklapp scattering operator destroys two $R$ particles and creates two $L$ particles of opposite spins:
$$
O_{U}(x) := c^\dagger_{(L, \uparrow, x)} c^\dagger_{(L, \downarrow, x)} c_{(R, \downarrow, x)}^{\phantom{\dagger}} c_{(R, \uparrow, x)}^{\phantom{\dagger}} \tag{21.8}
$$

For real coupling $g_U\in\mathbb R$, fix the Hamiltonian normalization
$$
H_U:=\frac{g_U}{L}\sum_{x\in\Lambda}\left(O_U(x)+O_U(x)^\dagger\right).
$$
The real coupling and adjoint sum make $H_U$ self-adjoint. The selected coefficients in the leakage examples use exactly this convention.

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
1. *Conditional Leakage Criterion:* Let $|\psi\rangle$ have definite charge $\vec N$ and lie in $\mathcal B_{K,\vec N_{\max}}$, with $g_U\ne0$. Require the **outward component** $\sum_{x\in\Lambda}O_U(x)|\psi\rangle\ne0$ and $\vec N+\Delta\vec N$ outside the specified charge box. The adjoint sum has charge $\vec N-\Delta\vec N$, a different sector, so it cannot cancel this component. Consequently:
$$
H_U |\psi\rangle \notin \mathcal{B}_{K, \vec{N}_{\max}}.
$$
2. *Non-invariance:* Under this criterion, the ambient $H_U$ does not preserve the chosen budget and its projection does not commute with $H_U$. The compressed operator $P H_U P$ is a separate operator on that budget and may still be diagonalized.

> [!WARNING]
> Nonzero total $H_U\psi$ is insufficient: it may consist entirely of the inward adjoint action. For $h=2,L=4$, take both R species occupied only at $-1$ and both L species full. The charges are $(-1,-1,2,2)$ in the box with bounds $(1,1,2,2)$ and energy cutoff 16. The outward action vanishes by Pauli exclusion; the adjoint spatial sum has a nonzero coefficient $g_U/16$ into charges $(0,0,1,1)$, and its entire image remains in the budget. This is a proper charge box, not the full carrier.

> [!NOTE]
> *Physical Motivation (KT Flow and Mott Gap):* In continuous field theory, Umklapp scattering generates second-order loop corrections described by Kosterlitz-Thouless (KT) scaling equations, driving the opening of a charge Mott gap. On the finite discrete lattice, budget leakage establishes the algebraic non-invariance of the truncated budget space; deriving the thermodynamic Mott gap or KT flow equations requires a separate asymptotic scaling construction.

*Lean 4 Proof Strategy:*
1. **Auxiliary Lemma 1:** Formalize the charge commutator $[\hat{N}_{\nu,s}, O_U(x)] = (\Delta \vec{N})_{\nu,s} O_U(x)$ from CAR.
2. **Auxiliary Lemma 2:** Use the charge projections to isolate the outward spatial sum; prove it is nonzero with one occupation coefficient outside the box. An outside-component witness also gives a general criterion when leakage is due to energy rather than charge.
3. Separate the discrete algebraic non-invariance result from continuous Wilsonian RG flow or thermodynamic gap claims.

**Lemma 21.8 (Explicit Zero-Charge Leakage Witness).**
Fix the occupation order $(L\uparrow,L\downarrow,R\uparrow,R\downarrow)$, with ascending integer momenta inside each species. For $h\ge1,L=2h,K=0$, all charge bounds zero, and $g_U\ne0$, let $\Omega$ be the four seas $\{1-h,\ldots,0\}$. Let $T$ add momentum $1$ to each $L$ species and remove momentum $1-h$ from each $R$ species. Its charges are $(+1,+1,-1,-1)$, so it lies outside the budget. With Definition 21.5's normalization,
$$
\langle\delta_T,H_U\Omega\rangle=-\frac{g_U}{L^2}\ne0.
$$
In right-to-left operator order the preceding occupation counts are $2h$ for $R\uparrow$ removal, $3h-1$ for $R\downarrow$ removal, $2h$ for $L\downarrow$ insertion, and $h$ for $L\uparrow$ insertion. Their total $8h-1$ is odd, giving sign $-1$ for every $h$. The selected four Fourier factors contribute $L^{-2}\zeta^{-Lx}=L^{-2}$ at each site; summing $L$ sites and multiplying $g_U/L$ gives the displayed coefficient. Each removed/added occupation fixes its momentum index uniquely, and the adjoint term has opposite charge, so no other word cancels this coefficient. This proof uses only CAR and Fourier character laws; no current-CCR margin is required.

*Lean 4 Proof Strategy:*
Prove membership/nonmembership of the four distinguished momenta, the four preceding-count formulas with prior insertions/erasures, and odd parity of their sum. Evaluate the selected occupation coefficient, use $\zeta^L=1$ to sum the constant character, and isolate its charge projection. Conclude budget non-invariance from the nonzero outside coefficient.

#### 21.4 Technical Notes for the Lean 4 Formalization

1. **Parity Sublattice Constraints:**
   * Enforce the condition $Q_c \equiv Q_s \pmod 2$ strictly when defining the available ground states in Lean.
2. **Raw Integer Fields:**
   * Do not normalize $R^c$ or $R^s$ with $\sqrt{2}$. Keep all coefficients rational/integer, accepting the explicit factors of $2m$ in the CCR evaluation.
3. **Leakage Witnesses:**
   * Formalize leakage by constructing a specific non-zero state on the boundary and demonstrating that applying $H_U$ violates the budget type bounds exactly.
