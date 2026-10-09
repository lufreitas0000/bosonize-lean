# BOSONIZE-LEAN: Mathematical Reference Notes

## Part II: Phase 2 The Density Sector

### Chapter 10: Heisenberg Algebra and the Exact Schwinger Term

To understand how fermionic bilinears can perfectly mimic bosonic operators, it is crucial to establish a clear mental visualization of the many-body states.

**Visualizing the Fermi Sea and the Anomaly:**
Imagine the single-particle momentum states as a vertical ladder. The Dirac vacuum $\vert{}\Omega\rangle$ corresponds to all rungs on the lower half of the ladder (negative momentum) being occupied by solid black dots (fermions), while the upper half is completely empty.
Applying a density mode $\rho_m$ (for $m > 0$) grabs a particle from below the "waterline" (the Fermi surface) and lifts it $m$ rungs higher, creating a particle-hole excitation.

In standard continuum quantum field theory, this ladder extends infinitely downwards (the infinite Dirac sea) and infinitely upwards. Because it is infinite, subtracting the reversed process (the commutator $[\rho_{-m}, \rho_m]$) leads to mathematically ill-defined $\infty - \infty$ expressions. Regularizing this yields a central extension known as the Schwinger term (or chiral anomaly).

In our strict finite-lattice AQFT, the ladder has a hard "floor" (the bottom of the band at $-h+1$) and a hard "ceiling" (the top of the band at $h$).
When we evaluate the commutator algebraically, most of the shifts in the deep "bulk" of the ladder cancel out perfectly. However, the shifts that hit the absolute floor and ceiling fail to cancel. Thus, the anomaly emerges purely as an **exact finite boundary effect**.

How do we formalize the "low-energy assumption" to recover the exact scalar anomaly? We use the Energy Budget $\mathcal{B}^N_K$. If a state only has a small amount of excitation energy $K$, the dynamics are entirely confined to a narrow window near the Fermi surface. The particles at the very bottom of the ladder are "frozen" in place because lifting them would require vastly more energy than the budget allows. Similarly, the top of the ladder is frozen empty. By proving that the un-cancelled boundary terms lie deep inside these frozen zones, the operators evaluate to exact scalar constants ($1$ for full, $0$ for empty), successfully formalizing the anomaly without any limits.

#### 10.1 The Exact Diagonal Commutator and Edge Formula

We begin by evaluating the pure algebraic commutator of opposing density modes, $[\rho_{-m}, \rho_m]$ for an integer $m \ge 1$, across the entire finite-dimensional Fock space $\mathcal{F}$, without any budget restrictions.

**Proof Approach and Domain Partitioning:**
To prove exact operator identities in Lean, we expand the commutator into a double sum using the definition of raw truncated density modes, and apply the pure CAR identities (Lemma 4.7). For opposing modes, the net momentum shift is zero, so the resulting two-fermion terms are exactly the number operators $n_q = c^\dagger_q c_q$.

The resulting operator is a difference of two sums over two different shifted index sets. We partition these sets into their intersection (the "Bulk") and their relative differences (the "Edges"). Because our band is the strictly bounded integer interval $\Lambda^* = [-h+1, h]$, we can explicitly calculate these domains:

1. **The Right-Acting Domain (**$\Omega_R$**):** The set of valid starting momenta $q$ if we apply $\rho_m$ *first*. This requires the particle to exist at $q$ and have room to move up to $q+m$.
   Condition: $q \in \Lambda^*$ and $q+m \le h$.
   Result: $\Omega_R = [-h+1, h-m]$.

2. **The Left-Acting Domain (**$\Omega_L$**):** The set of valid starting momenta $q$ if we apply $\rho_{-m}$ *first*. This requires the particle to exist at $q$ and have room to move down to $q-m$.
   Condition: $q \in \Lambda^*$ and $q-m \ge -h+1$.
   Result: $\Omega_L = [-h+1+m, h]$.

We partition these sets. The **Bulk Domain** is their intersection: $\Omega_{Bulk} = [-h+1+m, h-m]$. The sums over the bulk perfectly cancel each other out identically.
We are left only with the boundary terms on the **Edge Domains**:

* **The Bottom Edge:** $\Omega_R \setminus \Omega_{Bulk} = [-h+1, -h+m]$.

* **The Top Edge:** $\Omega_L \setminus \Omega_{Bulk} = [h-m+1, h]$.

Subtracting the Top Edge from the Bottom Edge isolates the exact extremes of the band, yielding the exact residual operator.

**Lemma 10.1 (The Exact Diagonal Edge Formula).**
Let the band size $L = 2h$ be even. For any integer $1 \le m \le h$, evaluating the algebraic commutator $[\rho_{-m}, \rho_m]$ on the full Fock space $\mathcal{F}$ yields exactly the difference in occupation between the bottom $m$ modes and the top $m$ modes:

$$
\forall 1 \le m \le h, \quad [\rho_{-m}, \rho_m] = \sum_{q = -h+1}^{-h+m} n_q - \sum_{q = h-m+1}^{h} n_q \tag{10.1}
$$

*Physical Note:* This operator identity is exact on the entire $2^L$-dimensional Fock space. If applied to a highly excited state (e.g., where a particle has been excited all the way to the top of the band), this commutator is *not* a scalar. It remains a dynamical operator. The algebra only becomes bosonic (scalar) when the physics is restricted to low-energy states.

#### 10.2 The Schwinger Term on the Energy Budget

**Physical Intuition for the Diagonal Buffer Zone (M1):**
To recover the scalar Schwinger term, we must restrict the evaluation of the edge formula to the budget subspace $\mathcal{B}^N_K$. We need the top $m$ modes and the bottom $m$ modes to be mathematically frozen.

On the budget subspace, the highest possible particle excitation can only reach depth $N+K$, and the deepest possible hole can only reach depth $N-K$. Therefore, we require the total band half-width $h$ to be sufficiently large to provide a "buffer." If the distance from the Fermi surface to the absolute band edge $h$ is strictly greater than the maximum particle excursion plus the shift $m$, the edge zones will be totally undisturbed by the dynamics.

Under this specific inequality, the operator $\sum n_q$ over the Bottom Edge will simply count $m$ fully occupied modes, and the sum over the Top Edge will count $m$ completely empty modes.

**Lemma 10.2 (Regime M1: The Diagonal Buffer Zone).**
Let $\psi \in \mathcal{B}^N_K$ be an arbitrary state in the energy budget. If the parameters satisfy the **M1 Margin Condition**:

$$
m + K + \vert{}N\vert{} \le h \tag{10.2}
$$

Then, by the Frozen Margins theorem (Lemma 7.9), every mode in the Bottom Edge interval $[-h+1, -h+m]$ is identically full ($n_q = 1$), and every mode in the Top Edge interval $[h-m+1, h]$ is identically empty ($n_q = 0$) on the support of $\psi$. Therefore, the sums in the Edge Formula evaluate exactly to $m(1) - m(0) = m$. The operator evaluates to an exact scalar, known as the Schwinger term:

$$
\forall \psi \in \mathcal{B}^N_K, \quad [\rho_{-m}, \rho_m] \psi = m \psi \tag{10.3}
$$

#### 10.3 Anti-Vacuity and Sharp Margins (Diagonal Case)

**Physical Intuition for Green-Washing Prevention:**
In formal verification, restricting a theorem to a subspace $\mathcal{B}^N_K$ under a complex inequality carries a severe risk: if the inequality is physically impossible to satisfy alongside non-trivial energy states, the subspace might be identically the zero vector, making the theorem vacuously true ("green-washing"). We must rigorously prove that the mathematical buffer zone can actually contain physical, excited bosonic modes.

**Lemma 10.3 (Witness Lemma for M1).**
The margin condition M1 is physically satisfiable by non-trivial operator actions.

1. The ground state $\psi = \vert{}\Omega\rangle$ with $m=1$, $K=0$, $N=0$ satisfies M1 for all $h \ge 1$, proving $[\rho_{-1}, \rho_1] \vert{}\Omega\rangle = \vert{}\Omega\rangle$.

2. For a sufficiently large lattice ($h \ge 3$), the excited state $\psi = \rho_1 \vert{}\Omega\rangle \neq 0$ lies in $\mathcal{B}^0_1$. Evaluating M1 yields $1 + 1 + 0 = 2 \le h$, proving that the commutator identity holds strictly on dynamically excited states, not just the vacuum.

#### 10.4 The General Kac-Moody Algebra and Off-Diagonal Suppression

**Physical Intuition for Off-Diagonal Suppression (M2):**
To establish the full bosonic algebra, we must also consider the cross-commutators $[\rho_m, \rho_n]$ where $m+n \neq 0$. In this case, the net momentum shift is non-zero, and the resulting residual operator from the CAR expansion evaluates to a sum of hopping terms $c^\dagger_{q+m+n} c_q$.

To ensure this evaluates to exactly $0$ (matching the bosonic CCR $[a_m, a_n] = 0$), the operator must attempt an impossible action. It must either try to create a particle where one already exists (deep in the frozen bottom) or destroy a particle where none exists (high in the frozen top). Because the particle travels a net distance of $\vert{}m+n\vert{}$, our buffer zone must be large enough to contain the absolute maximum possible excursion of *both* shifts combined. If this conservative margin holds, the boundary operators strictly annihilate the low-energy state.

**Lemma 10.4 (Regime M2: Off-Diagonal Suppression).**
Let $\psi \in \mathcal{B}^N_K$ be an arbitrary state in the energy budget. If the parameters $m, n \in \mathbb{Z}$ satisfy the **M2 Margin Condition**:

$$
\vert{}m\vert{} + \vert{}n\vert{} + K + \vert{}N\vert{} \le h \tag{10.4}
$$

Then every hopping operator in the residual edge domains strictly annihilates $\psi$. Consequently:

$$
\forall \psi \in \mathcal{B}^N_K, \quad \forall m+n \neq 0, \quad [\rho_m, \rho_n] \psi = 0 \tag{10.5}
$$

**Physical Intuition for Normal Ordering the Zero Mode:**
To unify the diagonal and off-diagonal rules into a single algebraic statement, we must handle the zero mode $\rho_0 = \hat{N}_{tot}$. In standard macroscopic systems, the raw number of particles scales with $L$, which diverges in the thermodynamic limit. By using the normal-ordered density $:\!\rho_m\!: \ := \rho_m - \delta_{m0} h I$ (Definition 9.3), we zero out the infinite background charge. Because normal ordering only shifts the zero mode by a scalar, it does not affect any commutators.

**Theorem 10.5 (The U(1) Kac-Moody Algebra on the Budget).**
Combining the diagonal evaluation (Lemma 10.2), the off-diagonal suppression (Lemma 10.4), and the exact covariance $[\hat{N}, \rho_m] = 0$ (Lemma 9.6), we conclude that under the conservative M2 margin condition, the normal-ordered density modes form an exact $U(1)$ Kac-Moody algebra on the budget subspace:

$$
\forall \psi \in \mathcal{B}^N_K, \quad [:\!\rho_m\!:, :\!\rho_n\!:] \psi = -m \delta_{m+n, 0} \psi \tag{10.6}
$$

*Note: The negative sign arises because the normal ordering of the Kac-Moody central extension is typically written as* $[J_m, J_n] = m \delta_{m+n,0}$*, but in our conventions,* $\rho_m$ *for* $m > 0$ *acts as a creation operator (raising energy), physically mapping it to the lowering current* $J_{-m}$*.*

**Lemma 10.6 (Witness Lemma for M2).**
The conservative M2 margin condition is physically satisfiable. For $h \ge 4$, taking $m=1, n=2, K=1, N=0$ yields $1 + 2 + 1 + 0 = 4 \le h$, successfully providing a non-vacuous, dynamically excited test space for off-diagonal commutators.

#### 10.5 Technical Notes for the Lean 4 Formalization (Chapter 10)

1. **Set Symmetric Difference and `Finset` API:**

   * The domains $\Omega_R$ and $\Omega_L$ should be defined using `Finset.filter` on `univ : Finset (LambdaDual L)`.

   * The proof of Lemma 10.1 in Lean will rely on Mathlib's `Finset` API for intersections (`∩`) and set differences (`\`). The cancellation of the bulk relies on rewriting the sums over the respective domains into sums over their intersection and their relative differences.

   * Since `Finset.sum_union` requires disjoint sets (which these are by definition), the split is mathematically clean and the intersection sum cancels exactly.

2. **Explicit Integer Intervals:**

   * Lean's `Finset.Icc` (Integer closed interval) API is perfectly suited for evaluating the Top and Bottom edges. The equivalence between the filtered domains and `Finset.Icc` should be established via `ext` (set extensionality) lemmas before evaluating the sum.

3. **Formulating Margin Hypotheses:**

   * Do not hardcode the budget limits into the definitions of the operators. The operators must remain globally defined on `End (FockSpace _)`.

   * The conditions M1 (`m.natAbs + K + N.natAbs ≤ h`) and M2 (`m.natAbs + n.natAbs + K + N.natAbs ≤ h`) must be explicit hypotheses in the theorem signatures (e.g., `(h_margin : m.natAbs + K + N.natAbs ≤ L/2)`).

4. **Equality on Subspaces (`Submodule`):**

   * Theorem 10.5 should be stated as an operator equality restricted to the `Submodule`. In Lean, this is expressed by stating that for all vectors `(psi : BudgetSpace L K Nmax)`, the action of the operators evaluates to the same vector:
     `comm_density_modes m n psi.val = (if m + n = 0 then -m else 0) • psi.val`

5. **Rigorous Anti-Vacuity Tests:**

   * The witness lemmas (10.3 and 10.6) must be formulated as explicit `example` blocks in Lean 4 that instantiate the theorem for concrete values of $L$, proving that `finrank` of the specific `BudgetSpace` is strictly greater than 1. This prevents logical collapse in the automated prover.
