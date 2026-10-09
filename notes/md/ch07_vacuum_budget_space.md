

### Chapter 7: Vacuum, Sectors, Energy, Budget

*Assumption:* From this chapter onward, we strictly require the lattice size $L = 2h$ to be an even integer. This guarantees the existence of a symmetric Fermi sea in the dual band $\Lambda^* = \{-h+1, \dots, h\}$.

**Intuition for the "Energy Budget":**
In continuum quantum field theory, the Dirac sea has infinite depth. Taking the limit $L \to \infty$ naively results in unbounded operators (like total energy) and divergences. To formalize this rigorously on a finite computer without resorting to limits or topology, we use a truncation scheme called the **Energy Budget**.
Just like a financial budget caps spending, this restricts our operators and states to a finite-dimensional subspace where the total excitation energy ($K$) and net charge deviation ($N_{\max}$) are strictly capped. As long as our "budget" $K$ is smaller than the depth of the finite sea $h$, the particles deep at the bottom of the band simply do not have enough energy to hop above the Fermi level. Thus, the bottom of the band is "frozen," mimicking an infinitely deep sea exactly, but keeping all matrices finite.

---

#### 7.1 Definitions

**Definition 7.1 (Dirac Vacuum).**
The vacuum state subset $S_\Omega \subseteq \Lambda^*$ corresponds to the completely filled left-half of the momentum band (the Dirac sea):

$$
S_\Omega := \{k \in \Lambda^* \mid k \le 0\} \tag{7.1}
$$

The exact cardinality is $\#S_\Omega = h$. The vacuum state vector is defined on the Fock basis as $|\Omega\rangle := \delta_{S_\Omega}$.

**Definition 7.2 (Charge and Number Operator).**
For any particle configuration subset $S \subseteq \Lambda^*$, the relative sector charge counts particles added or holes created relative to half-filling:

$$
N(S) := \#S - h \tag{7.2}
$$

The self-adjoint physical number operator relative to the vacuum acts on all modes $k \in \Lambda^*$:

$$
\hat{N} := \sum_{k \in \Lambda^*} (n_k - \chi_{\le 0}(k) I) \tag{7.3}
$$

where $\chi_{\le 0}(k)$ is the indicator function for $k \le 0$.

**Definition 7.3 (Normal Ordering).**
For any dual momentum modes $p, q \in \Lambda^*$, the normal-ordered fermionic bilinear systematically subtracts the finite vacuum expectation:

$$
:\!c_p^\dagger c_q\!: \ := c_p^\dagger c_q - \delta_{pq}\chi_{\le 0}(p)I \tag{7.4}
$$

**Definition 7.4 (Sector Ground States).**
For any integer charge sector $N \in \{-h, \dots, h\}$, the sector ground state subset bounds the Fermi level up to $N$:

$$
S_{N,0} := \{k \in \Lambda^* \mid k \le N\} \tag{7.5}
$$

The associated state vector is $|N\rangle_0 := \delta_{S_{N,0}}$. Note that $|0\rangle_0 = |\Omega\rangle$.

**Definition 7.5 (Energies).**
For any configuration $S \subseteq \Lambda^*$, the bare momentum energy evaluates to the sum of occupied momenta minus the vacuum momentum:

$$
P(S) := \sum_{k \in S} k - \sum_{k \le 0} k \tag{7.6}
$$

The true excitation energy relative to the sector minimum is:

$$
e(S) := P(S) - \frac{1}{2}N(S)(N(S)+1) \tag{7.7}
$$

**Definition 7.6 (Energy Budget Subspace).**
Let $K \in \mathbb{N}$ be the maximum allowed excitation energy, and $N_{\max} \in \mathbb{N}$ be the maximum allowed absolute charge sector. The budget subspace is a specific vector subspace of $\mathrm{Fock}(\Lambda^*)$:

$$
\mathcal{B}_{K,N_{\max}} := \mathrm{span}_{\mathbb{C}} \{ \delta_S \mid e(S) \le K \land |N(S)| \le N_{\max} \} \tag{7.8}
$$

---

#### 7.2 Properties of the Vacuum, Energy, and the Budget Subspace

To prove that the energy budget successfully regularizes the theory without artifacts, we must prove that excitation energies are strictly non-negative and that bounding the energy mathematically freezes the margins of the Fermi sea.

**Lemma 7.7 (Vacuum Expectation & Sector Grounds).**
For all $p, q \in \Lambda^*$, the normal-ordered expectation vanishes cleanly: $\langle \Omega \mid :\!c_p^\dagger c_q\!: \mid \Omega \rangle = 0$.
Furthermore, the basis states $\{|N\rangle_0\}$ form an orthonormal family, and for all $-h \le N \le h$, $\hat{N} |N\rangle_0 = N |N\rangle_0$.

**Physical Context for the Rank Formula (Lemma 7.8):**
How do we rigorously prove that $e(S) \ge 0$ for *all* configurations? Physically, a many-body state is a collection of identical fermions occupying distinct momentum orbitals. If we sort the occupied momenta of configuration $S$ from lowest to highest ($s_1 < s_2 < \dots < s_{h+N}$), we are organizing the particles by depth, from the bottom of the Dirac sea up to the Fermi surface. If we sort the unexcited ground state identically, we get $g_1 < g_2 < \dots < g_{h+N}$.
The Rank Formula pairs these up one-to-one. The mathematical difference $s_i - g_i$ represents the exact physical energy cost (in momentum quanta) to lift the $i$-th deepest particle from its ground-state orbital to its current excited orbital. Because of the Pauli exclusion principle, the ordering is strictly preserved. No particle can be "pushed down" below the perfectly packed ground state because those lower states are already full. Therefore, $s_i \ge g_i$ universally for every single particle, proving the total excitation energy must be strictly non-negative.

**Lemma 7.8 (Rank Formula).**
For any arbitrary configuration $S \subseteq \Lambda^*$ with $\#S = h+N$, let its elements be sorted such that $s_1 < s_2 < \dots < s_{h+N}$. Let $g_i := -h+i$ (the sorted elements of the ground state $S_{N,0}$). Then the excitation energy factorizes into independent, non-negative particle depth differences:

$$
e(S) = \sum_{i=1}^{h+N} (s_i - g_i) \tag{7.9}
$$

It directly follows algebraically that $e(S) \ge 0$ for all configurations $S$, and $e(S) = 0 \iff S = S_{N,0}$.

**Physical Context for Frozen Margins (Lemma 7.9):**
This is the payoff of the budget. If the system only has $K$ units of energy to spend, a particle sitting at depth $K+1$ below the Fermi surface cannot be excited—it's frozen.

**Lemma 7.9 (Frozen Margins).**
For any configuration $S \subseteq \Lambda^*$ governed by $N(S) = N$ and constrained by the budget $e(S) \le K$:
1. For all $k \le N-K$, the mode is forced full ($k \in S$).
2. For all $k > N+K$, the mode is forced empty ($k \notin S$).

---

#### 7.3 Technical Notes for the Lean 4 Formalization (Chapter 7)

1. **Evenness of $L$:**
   - Represent this cleanly in Lean. Do not use an unconstrained `L` and a random variable `h`. Either require `[Fact (Even L)]` or define the lattice using $h$ directly, where $L = 2 * h$. The latter is highly recommended to avoid arithmetic friction with division by 2 in integer contexts.
2. **Normal Ordering (`:c_p^\dagger c_q:`):**
   - The subtraction of $\delta_{pq}\chi_{\le 0}(p)I$ is an algebraic operation in `Module.End ℂ (FockSpace _)`.
3. **The Rank Formula (Sorting Finsets in Lean):**
   - This is the most technically demanding proof of Phase 1.
   - While one might intuitively try converting a `Finset` to a `List` using `Finset.sort (· < ·)` and pairing them with `List.zip`, this introduces heavy friction with list lengths, index bounds, and proof maintenance.
   - **The standard, idiomatic Mathlib approach:** Use `Finset.orderIsoOfFin`. For any finite set $S$ with cardinality $c$, `S.orderIsoOfFin` provides a strict order isomorphism `Fin c ≃o S`. This maps an index $i \in \{0, \dots, c-1\}$ directly to the $i$-th smallest element of $S$ while maintaining the strict monotonicity strictly by type: $i < j \implies s(i) < s(j)$.
   - Define $s(i) := \text{S.orderIsoOfFin } i$ and $g(i) := \text{S}_{N,0}\text{.orderIsoOfFin } i$.
   - The many-body energy then translates beautifully to a sum over the `Fin c` index type: $\sum_{i : \text{Fin } c} (s(i) - g(i))$.
   - The proof that $s(i) \ge g(i)$ proceeds by induction on the index $i$, leveraging the fact that $S$ is bounded from below by the bottom of the band $-h+1$, and $S_{N,0}$ is perfectly packed without gaps.
4. **Frozen Margins & Bounded Sums:**
   - To prove Lemma 7.9, rely on the Rank Formula. Since $e(S) \le K$, and $e(S) = \sum (s(i) - g(i))$ where every $(s(i) - g(i)) \ge 0$, Lean's standard library `Finset.sum_le` properties imply that each individual term $s(i) - g(i) \le K$.
   - This strict bound forces the lowest indices of $S$ to identically match the lowest indices of the ground state, locking the deep modes.
5. **The Budget Subspace (`Submodule.span`):**
   - Define $\mathcal{B}_{K,N_{\max}}$ as a `Submodule ℂ (FockSpace (LambdaDual L))` using `Submodule.span` over the set of basis vectors $\{\delta_S\}$ that satisfy the condition. This allows natural coercion to a Hilbert space and makes projection operators $P_K$ well-defined in Lean's linear algebra API.
