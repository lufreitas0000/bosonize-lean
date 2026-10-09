### Chapter 14: The Mattis-Mandelstam Formula

We have arrived at the core dictionary of bosonization: constructing the localized fermionic destruction operator $c_{(\nu, x)}$ purely out of bosonic components.
Because formal infinite-dimensional identities break down on finite-budget truncations, our goal is strictly to formulate and test a projected mapping of matrix elements between specified finite budgets, following the corrections in [Appendix A05](../appendices/a05_exponentials_klein_and_vertex_scope.md).

#### 14.1 Bosonic Phase Fields and Boundary Conditions

We exponentiate the unnormalized integer-weighted currents $\rho_{m, \nu}$, replacing the standard non-algebraic $1/\sqrt{q}$ with a rational $1/m$ factor.

**Definition 14.1 (Chiral Phase Operators).**
Let $\zeta = e^{2\pi i / L}$ be the primitive root of unity. Fix an independent mode cutoff $M \ge 1$ with $2M<L$. For each species $\nu \in \mathcal{C}$ and spatial position $x \in \Lambda$:

$$
W^+_{\nu}(x) := \sum_{m=1}^{M} \frac{\zeta^{m x}}{m} \rho_{-m, \nu} \tag{14.1}
$$

$$
W^-_{\nu}(x) := -\sum_{m=1}^{M} \frac{\zeta^{-m x}}{m} \rho_{m, \nu} \tag{14.2}
$$

*Lean 4 Proof Strategy:*
Formalize `W_plus` and `W_minus` as functions of type `Species → Λ → Operator HilbertSpace`. The primitive root of unity `ζ` should be defined using `Complex.exp` or a specialized cyclotomic extension if exact arithmetic is needed. `ρ_{-m, \nu}` and `ρ_{m, \nu}` are operators. Use one definition throughout, summing over positive modes at most `M`. Finite sums define ambient linear maps; restriction to a budget separately requires preservation, and compressed raising uses its own endomorphism.
Auxiliary lemmas needed:
1. `W_plus_adjoint`: Prove that `W_plus` and `W_minus` are related by Hermitian conjugation.
2. `comm_W_plus_minus`: Evaluate the commutator `[W_plus, W_minus]` using the current algebra.

**Definition 14.2 (Source Zero-Mode Phase).**
The overall baseline momentum of the sector must be shifted when a particle is removed. A naive formula $\omega^{2xN - x}$ is anti-periodic under $x \to x+L$. To strictly maintain lattice periodicity matching $c_x$, we define the zero-mode phase operator acting diagonally on the source charge sector $\vec{N}$:

$$
Z_\nu(x) \vert{}\vec{N}\rangle := \zeta^{x N_\nu} \vert{}\vec{N}\rangle \tag{14.3}
$$

Because $Z_\nu(x)$ acts on the source state *before* the charge is lowered by $F_\nu$, it contributes the exact eigenvalue $\zeta^{x N_\nu}$, matching the physical matrix element ${}_0\langle \vec{N}-e_\nu \mid c_{(\nu, x)} \mid \vec{N}\rangle_0 = \frac{1}{\sqrt{L}} P(\nu, \vec{N}) \zeta^{x N_\nu}$.
(If $Z_\nu$ were placed after $F_\nu$, it would evaluate on the shifted target charge $N_\nu - 1$, producing an erroneous extra $\zeta^{-x}$ phase).

*Lean 4 Proof Strategy:*
Formalize `Z_nu(x)` as a linear map on the Hilbert space which acts diagonally on the charge basis `|N>`. Define the operator by its action on the basis elements.
Auxiliary lemmas:
1. `Z_nu_commute_W`: Prove that `Z_nu` commutes with `W_plus` and `W_minus` because the latter operators do not change the total charge `N_nu`.
2. `Z_nu_Klein_intertwine`: Prove $F_\nu Z_\nu(x) |\vec{N}\rangle_0 = P(\nu, \vec{N}) \zeta^{x N_\nu} |\vec{N}-e_\nu\rangle_0$, correctly reproducing the ground-to-ground CAR matrix element.

#### 14.2 Compressed Nilpotent Phase Exponentials and Cutoff Typing

Use exactly the phase operators (14.1)–(14.2), including the minus sign in $W^-$. The discarded difference phases $(\zeta^{\pm mx}-1)/m$ vanished at $x=0$ and had the wrong adjoint sign.

> [!WARNING]
> **Revision check (2026-10-09):** With $h=4,L=8,M=1,N=0,K_{\mathrm{in}}=0,K_{\mathrm{out}}=1,x=0$, the physical coefficient of the hole at momentum $-1$ is $1/\sqrt{8}$. The discarded phases produced zero, despite satisfying the former margin (14.6). A ground-to-ground scalar test alone did not detect this error.

To define the composite vertex operator between source budget $B_{\text{in}} = B(\vec{N}, K_{\text{in}})$ and target budget $B_{\text{out}} = B(\vec{N}-e_\nu, K_{\text{out}})$, first inherit the admissibility and all-species Klein completeness contract of Chapter 13 at K*=max(Kin,Kout). Each factor then has its explicit typing, transition map, and nilpotency degree:
1. **Source Zero-Mode:** $Z_\nu(x): B(\vec{N}, K_{\text{in}}) \to B(\vec{N}, K_{\text{in}})$ acts diagonally with eigenvalue $\zeta^{x N_\nu}$.
2. **Sector Shift:** $F_\nu: B(\vec{N}, K_{\text{in}}) \to B(\vec{N}-e_\nu, K_{\text{in}})$ shifts charge with ground phase $P(\nu, \vec{N})$ and preserves excitation energy.
3. **Lowering Exponential:** Because each mode $\rho_{-m,\nu}$ ($m \ge 1$) lowers excitation energy by at least 1, $W^+_\nu(x)$ is strictly nilpotent on $B(\vec{N}-e_\nu, K_{\text{in}})$ with nilpotency degree at most $K_{\text{in}} + 1$. Its unprojected action remains within $B(\vec{N}-e_\nu, K_{\text{in}})$, so its exact finite polynomial exponential is:
$$
\operatorname{expNil}_{\text{in}}(W^+_\nu(x)) := \sum_{j=0}^{K_{\text{in}}} \frac{\left( W^+_\nu(x) \right)^j}{j!} \in \mathrm{End}_{\mathbb{C}}(B(\vec{N}-e_\nu, K_{\text{in}})).
$$
4. **Cutoff Transition:** The transition map $\Pi_{\text{trans}}: B(\vec{N}-e_\nu, K_{\text{in}}) \to B(\vec{N}-e_\nu, K_{\text{out}})$ is defined as orthogonal projection $P_{K_{\text{out}}}$ if $K_{\text{out}} \le K_{\text{in}}$, or canonical inclusion if $K_{\text{out}} > K_{\text{in}}$.
5. **Compressed Raising Exponential:** The raising operator $W^-_\nu(x)$ increases excitation energy. On the target space $B(\vec{N}-e_\nu, K_{\text{out}})$, the compressed raising operator is defined by $W^-_{\nu,\text{comp}}(x) := P_{K_{\text{out}}} W^-_\nu(x) P_{K_{\text{out}}}$. Because each step strictly raises energy, $W^-_{\nu,\text{comp}}$ is strictly nilpotent on $B(\vec{N}-e_\nu, K_{\text{out}})$ with degree at most $K_{\text{out}} + 1$. Its compressed exponential is:
$$
\operatorname{expNil}_{\text{out}}(W^-_\nu(x)) := \sum_{j=0}^{K_{\text{out}}} \frac{\left( W^-_{\nu,\text{comp}}(x) \right)^j}{j!} \in \mathrm{End}_{\mathbb{C}}(B(\vec{N}-e_\nu, K_{\text{out}})).
$$

#### 14.3 The Vertex Map Equivalence

**Definition 14.3 (The Projected Bosonized Vertex Map).**
For each species $\nu \in \mathcal{C}$ and position $x \in \Lambda$, the composite bosonized vertex operator $B_\nu(x): B(\vec{N}, K_{\text{in}}) \to B(\vec{N}-e_\nu, K_{\text{out}})$ is defined by:

$$
B_\nu(x) := \frac{1}{\sqrt{L}} \operatorname{expNil}_{\text{out}}(W^-_{\nu}(x)) \circ \Pi_{\text{trans}} \circ \operatorname{expNil}_{\text{in}}(W^+_{\nu}(x)) \circ F_\nu \circ Z_\nu(x) \tag{14.4}
$$

*(Operator sequence from right to left: $Z_\nu$ evaluates the source phase $\zeta^{x N_\nu}$; $F_\nu$ shifts charge with phase $P(\nu, \vec{N})$; $\operatorname{expNil}_{\text{in}}(W^+)$ lowers energy on the input cutoff; $\Pi_{\text{trans}}$ transitions to cutoff $K_{\text{out}}$; and compressed $\operatorname{expNil}_{\text{out}}(W^-)$ raises within the target cutoff).*

*Lean 4 Proof Strategy:*
Define `B_nu(x)` as a composition of linear maps between explicitly typed finite budget spaces `Budget(N_in, K_in) → Budget(N_out, K_out)`.
`expNil` is defined as a finite polynomial sum.
Auxiliary lemmas:
1. `expNil_W_minus_well_defined`: Nilpotency degree bounds on both lowering and compressed raising polynomials.
2. `B_nu_linearity`: Linearity of the composite map.

**Lemma 14.4 (Adjoint Properties).**
Taking the Hilbert adjoint reverses operator order, mapping $B^\dagger_\nu(x): B(\vec{N}-e_\nu, K_{\text{out}}) \to B(\vec{N}, K_{\text{in}})$. Because $(W^+_\nu)^\dagger = -W^-_\nu$ and $(W^-_\nu)^\dagger = -W^+_\nu$, the adjoint factors are:
$$
\left(\operatorname{expNil}_{\text{out}}(W^-_\nu(x))\right)^\dagger = \operatorname{expNil}_{\text{out}}(-W^+_\nu(x)), \quad \left(\operatorname{expNil}_{\text{in}}(W^+_\nu(x))\right)^\dagger = \operatorname{expNil}_{\text{in}}(-W^-_{\nu,\text{in-comp}}(x))
$$
Here $W^-_{\nu,\mathrm{in-comp}}=P_{K_{\mathrm{in}}}W^-_\nu P_{K_{\mathrm{in}}}$ acts on the shifted input carrier. The output $W^+$ is restricted to the output carrier. These are adjoints of the actual compressed/restricted factors, rather than ambient endomorphisms with mismatched domains. The adjoint vertex map is:

$$
B^\dagger_\nu(x) = \frac{1}{\sqrt{L}} Z^\dagger_\nu(x) \circ F^\dagger_\nu \circ \operatorname{expNil}_{\text{in}}(-W^-_{\nu,\text{in-comp}}(x)) \circ \Pi_{\text{trans}}^\dagger \circ \operatorname{expNil}_{\text{out}}(-W^+_{\nu}(x)) \tag{14.5}
$$

*(Note: $\operatorname{expNil}(-W^-)$ precedes $\operatorname{expNil}(-W^+)$ in the adjoint; because raising and lowering phases do not commute, swapping this order is an algebraic error).*

*Lean 4 Proof Strategy:*
State and prove this using the adjoint rule $(ABCD)^\dagger = D^\dagger C^\dagger B^\dagger A^\dagger$.
Auxiliary lemmas:
1. `expNil_adjoint`: Prove `(expNil(W^+))^\dagger = expNil(-W^-)` and `(expNil(W^-))^\dagger = expNil(-W^+)`.
2. `Klein_adjoint`: $F_\nu^\dagger = F_\nu^{-1}$ on the budget subspace.
3. `Z_nu_adjoint`: $Z_\nu(x)^\dagger = Z_\nu(x)^{-1}$ (unitarity of zero-mode phase).

**Proposed Theorem 14.5 (Projected Mattis-Mandelstam Equivalence; proof contract pending).**
The unprojected equation $c_x = B_x$ fails as a global algebraic identity on finite systems (e.g., at $K=0$, the physical $c_x |\vec{N}\rangle_0$ contains deep hole states of excitation energy $>0$). Therefore, the exact bosonization theorem is strictly a **projected matrix-element equivalence**.
Let $K_* = \max(K_{\mathrm{in}},K_{\mathrm{out}})$. To construct the Klein maps used here, require the completeness regime for every species in both charge sectors:
$$
\forall \eta,\quad 2K_*+\max(|N_\eta|,|N_\eta-\delta_{\nu\eta}|)\le h.
$$
Mode coverage must also be proved. The conservative candidate $M\ge K_*$ covers the positive energy increments visible in these budgets, but does not by itself prove the field identity. For example, with $h=6,L=12,N=0,K_{\mathrm{in}}=0,K_{\mathrm{out}}=2,M=1,x=0$, restoring (14.1)–(14.2) still gives coefficient $-1/(2\sqrt{12})$ for the hole at $-2$, whereas the physical coefficient is $-1/\sqrt{12}$. The missing mode 2 matters.

The former numerical margin remains a candidate wrapper to derive the actual right-suffix action bounds:
$$
2M + \max(K_{\text{in}}, K_{\text{out}}) + \max(|N_\nu|, |N_\nu - 1|) \le h \tag{14.6}
$$
but it has not been proved sufficient. The intended equality, pending the full projected ground-state calculation and typed intertwining induction, is:

$$
P_{\text{out}} c_{(\nu, x)} P_{\text{in}} = B_\nu(x) \tag{14.7}
$$

In particular, between sector ground states ($K_{\text{in}} = K_{\text{out}} = 0$), both $\operatorname{expNil}$ operators reduce to $I$, yielding:
$$
{}_0\langle \vec{N}-e_\nu \mid c_{(\nu,x)} \mid \vec{N} \rangle_0 = \frac{1}{\sqrt{L}} P(\nu, \vec{N}) \zeta^{x N_\nu}
$$
matching the exact physical CAR ground matrix element.

*Lean 4 Proof Strategy:*
Formalize the theorem as an exact equality of operators `P_{out} ∘ c_{nu, x} ∘ P_{in} = B_nu(x)` acting on `Budget(N_in, K_in)` into `Budget(N_out, K_out)`.
Proof strategy: Proceed by induction on the basis states (or the total energy $K$). First, explicitly calculate the action on the lowest-weight state (vacuum of the sector) to show the base case. Then, show that the intertwining relation holds with the creation operators (currents) to inductively generate the equality on all higher states within the truncated budget.
Auxiliary lemmas:
1. `base_state_equivalence`: Prove `P_out (c_{nu, x} |N>) = B_nu(x) |N>` as a complete vector equality, including every retained hole coefficient. Matching only the ground-to-ground scalar is insufficient.
2. `intertwining_rho`: Prove each typed commuting square with its actual right-suffix input budget. Retain projection remainders until a separate range lemma makes them zero; then extend over the joint partition basis.
