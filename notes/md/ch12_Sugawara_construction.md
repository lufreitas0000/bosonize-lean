### Chapter 12: Algebraic Equivalence of Energy Observables (The Sugawara Construction)

**Physical and Algebraic Motivation:**
We are asking a purely algebraic question: *Can the observable that measures fermionic excitation energy be constructed entirely out of bosonic density blocks?* We are proving that the energy operator $\hat{E}$ is algebraically equivalent to a specific quadratic sum of density modes on the budget subspace. The logic sequence strictly follows [Appendix A04](../appendices/a04_density_partitions_and_sugawara.md).

#### 12.1 Definitions and Normal Ordering

**Definition 12.1 (Bosonic Sugawara Hamiltonian).**
The Sugawara kinetic energy operator is defined as the normal-ordered sum of density bilinears, explicitly parametrized by a cutoff $M$:

$$
H_{\text{sug}}^{(M)} := \sum_{m=1}^{M} \rho_m \rho_{-m} \tag{12.1}
$$

Because any lowering mode $\rho_{-m}$ with $m > K$ identically annihilates a state in the energy budget $B(N,K)$, selecting a cutoff $M \ge K$ captures the entire non-zero action. The sum is not bounded by $h-1$; nonzero density modes can exist up to $L-1$.

#### 12.2 The Equivalence Theorem

**Physical Intuition for the Equivalence Proof:**
Attempting to prove the Sugawara equivalence by directly substituting commutators into a global equation leads to circular dependencies or unresolvable edge cases (e.g., the $h=1$ case is famously anomalous if evaluated blindly). Instead, the safest, non-circular proof path uses Haldane completeness (Chapter 11) to evaluate the action exactly on the known basis states.

**Lemma 12.2 (Action on Partition States).**
By commuting the lowering operators $\rho_{-m}$ through the creation word defining a partition state $|\lambda; N\rangle$, one calculates its exact eigenvalue. Under the conservative R2 Margin condition, the energy of the partition state is exactly recovered:

$$
H_{\text{sug}}^{(M)} |\lambda; N\rangle = K |\lambda; N\rangle \tag{12.2}
$$

where $K = \sum m \cdot r_m$ is the total excitation energy, and $M \ge K$.

**Theorem 12.3 (Sugawara Equivalence on the Budget).**
Because both the true fermionic excitation energy operator $\hat{E}$ and $H_{\text{sug}}^{(M)}$ correctly measure the energy of every basis state $|\lambda; N\rangle$ as $K$, and because these partition states completely span $B(N,K)$ (Haldane Completeness), the two operators are identical on the subspace.
Under the R2 Margin condition ($2K + \vert{}N\vert{} \le h$) and $M \ge K$:

$$
\forall \psi \in B(N,K), \quad \hat{E} \psi = H_{\text{sug}}^{(M)} \psi \tag{12.3}
$$

Equivalently, substituting the exact normal-ordered free Hamiltonian $\hat{P} = H_0 - E_\Omega I$:

$$
\forall \psi \in B(N,K), \quad \hat{P} \psi = \left( H_{\text{sug}}^{(M)} + \frac{1}{2}N(N+1)I \right) \psi \tag{12.4}
$$

*(Note: The zero-mode shift is explicitly $\frac{1}{2}N(N+1)$, arising from the asymmetric Fermi level at 0. It must not be artificially symmetrized to $\frac{1}{2}N^2$ without a corresponding chemical potential shift).*

#### 12.3 The Commutator Corollary

Rather than using commutation to prove equivalence, we derive commutation as a safe corollary *from* the equivalence theorem, ensuring it is only evaluated on valid budgets.

**Corollary 12.4 (Commutation with the Modes).**
To prove $[H_{\text{sug}}^{(M)}, \rho_n]\psi = n \rho_n \psi$ for a raising mode $n > 0$ acting on $\psi \in B(N,K)$, both the input $\psi$ and the output $\rho_n \psi$ must lie in budgets where the equivalence theorem holds. Therefore, we require the enlarged margin $2(K+n) + |N| \le h$ and cutoff $M \ge K+n$. Under these strict conditions:

$$
\forall \psi \in B(N,K), \quad [H_{\text{sug}}^{(M)}, \rho_n] \psi = n \rho_n \psi \tag{12.5}
$$
