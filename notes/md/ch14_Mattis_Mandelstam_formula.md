### Chapter 14: The Mattis-Mandelstam Formula

We have arrived at the core dictionary of bosonization: constructing the localized fermionic destruction operator $c_{(\nu, x)}$ purely out of bosonic components.
Because formal infinite-dimensional identities break down on finite-budget truncations, our goal is strictly to establish a proven mapping of matrix elements between explicitly verified finite budgets, following the corrections in [Appendix A05](../appendices/a05_exponentials_klein_and_vertex_scope.md).

#### 14.1 Bosonic Phase Fields and Boundary Conditions

We exponentiate the unnormalized integer-weighted currents $\rho_{m, \nu}$, replacing the standard non-algebraic $1/\sqrt{q}$ with a rational $1/m$ factor.

**Definition 14.1 (Chiral Phase Operators).**
Let $\zeta = e^{2\pi i / L}$ be the primitive root of unity. For each species $\nu \in \mathcal{C}$ and spatial position $x \in \Lambda$:

$$
W^+_{\nu}(x) := \sum_{m=1}^{h-1} \frac{\zeta^{m x}}{m} \rho_{-m, \nu} \tag{14.1}
$$

$$
W^-_{\nu}(x) := -\sum_{m=1}^{h-1} \frac{\zeta^{-m x}}{m} \rho_{m, \nu} \tag{14.2}
$$

*Lean 4 Proof Strategy:*
Formalize `W_plus` and `W_minus` as functions of type `Species → Λ → Operator HilbertSpace`. The primitive root of unity `ζ` should be defined using `Complex.exp` or a specialized cyclotomic extension if exact arithmetic is needed. `ρ_{-m, \nu}` and `ρ_{m, \nu}` are operators. Because of the finite sum, these operators are well-defined. We'll need a finite sum lemma over the range `1` to `h-1`.
Auxiliary lemmas needed:
1. `W_plus_adjoint`: Prove that `W_plus` and `W_minus` are related by Hermitian conjugation.
2. `comm_W_plus_minus`: Evaluate the commutator `[W_plus, W_minus]` using the current algebra.

**Definition 14.2 (Periodic Zero-Mode Phase).**
The overall baseline momentum of the sector must be shifted when a particle is removed. A naive formula $\omega^{2xN - x}$ is anti-periodic under $x \to x+L$. To strictly maintain lattice periodicity matching $c_x$, we define the zero-mode phase mapped onto the integer charge $N_\nu$:

$$
Z_\nu(x) \vert{}\vec{N}\rangle := \zeta^{x N_\nu} \vert{}\vec{N}\rangle \tag{14.3}
$$

(A corresponding fixed parity boundary twist or momentum shift must absorb the half-integer offset if exact ground-state phases are tracked, depending on whether periodic or anti-periodic boundaries are chosen for the physical fermions).

*Lean 4 Proof Strategy:*
Formalize `Z_nu(x)` as a linear map on the Hilbert space which acts diagonally on the charge basis `|N>`. Define the operator by its action on the basis elements.
Auxiliary lemmas:
1. `Z_nu_commute_W`: Prove that `Z_nu` commutes with `W_plus` and `W_minus` because the latter operators do not change the total charge `N_nu`.
2. `Z_nu_Klein_commute`: Prove the specific commutation relations between `Z_nu` and the Klein factors `F_nu` (since Klein factors shift `N_nu`).

#### 14.2 Projected Truncated Exponentials

**Physical Intuition (Nilpotency vs. Projection):**
A common misconception is that raising operators on a finite budget are natively nilpotent. Applying $W^-$ to a state in $B(N,K)$ maps it strictly into higher budgets; it does not naturally equal zero unless a projection $P_{K'}$ is inserted.

For a truly nilpotent, compressed endomorphism $A$ with $A^{d+1}=0$ on its restricted carrier, we define its finite algebraic exponential $\mathrm{expNil}(A) = \sum_{j=0}^d A^j/j!$. We define the vertex map component as explicitly projected into the target budget $K_{out}$.

#### 14.3 The Vertex Map Equivalence

**Definition 14.3 (The Bosonized Vertex Map).**
For each species $\nu \in \mathcal{C}$ and position $x \in \Lambda$, the composite bosonized map $B_\nu(x)$ acts from a source budget $B_{in}$ to a target budget $B_{out}$:

$$
B_\nu(x) := \frac{1}{\sqrt{L}} \mathrm{expNil}_{out}(W^-_{\nu}(x)) \mathrm{expNil}_{in}(W^+_{\nu}(x)) Z_\nu(x) F_\nu \tag{14.4}
$$

*(Note the operator ordering: annihilation phases lower the energy, the Klein map changes the sector, and the creation phase raises the energy, all explicitly tracked between valid finite budgets).*

*Lean 4 Proof Strategy:*
Define `B_nu(x)` as a composition of linear maps between explicitly typed finite budget spaces `Budget(N_in, K_in) → Budget(N_out, K_out)`.
`expNil` needs to be defined as a finite Taylor series projection.
Auxiliary lemmas:
1. `expNil_W_minus_well_defined`: Prove that the truncated exponential applied to the specific budget size terminates or is correctly projected.
2. `B_nu_linearity`: Prove the operator is linear.

**Lemma 14.4 (Adjoint Properties).**
Because $(W^+_{\nu})^\dagger = -W^-_{\nu}$, the adjoint exponentials carry minus signs and reverse order. The formal adjoint map is:

$$
B^\dagger_\nu(x) = \frac{1}{\sqrt{L}} F^\dagger_\nu Z^{-1}_\nu(x) \mathrm{expNil}_{in}(-W^+_{\nu}(x)) \mathrm{expNil}_{out}(-W^-_{\nu}(x)) \tag{14.5}
$$

*Lean 4 Proof Strategy:*
State and prove this using the definition of the adjoint for operators on finite-dimensional spaces.
Auxiliary lemmas:
1. `expNil_adjoint`: Prove `(expNil(A))^\dagger = expNil(A^\dagger)` for our projected exponentials.
2. `Klein_adjoint`: `F_nu^\dagger = F_nu^{-1}` (unitarity of Klein factors).
3. `Z_nu_adjoint`: `Z_nu(x)^\dagger = Z_nu(x)^{-1}` (unitarity of the zero-mode phase).

**Theorem 14.5 (Projected Mattis-Mandelstam Equivalence).**
The unprojected equation $c_x = B_x$ fails as a global algebraic identity on finite systems (e.g., at $K=0$, the vertex map produces only the ground ket, missing deep hole states). Therefore, the exact bosonization theorem is strictly a **projected matrix-element equivalence**.
If we select a target energy $K_{out}$ and boundary phases are consistently fixed, then on the verified prefix margins:

$$
P_{out} c_{(\nu, x)} P_{in} = B_\nu(x) \tag{14.6}
$$

This is proven via a cyclic-basis intertwining induction with typed maps. We do not infer Schur irreducibility of a finite slice on which creators do not act as true endomorphisms. We do not infer global CAR by multiplying restricted equalities without explicit target-domain proofs.

*Lean 4 Proof Strategy:*
Formalize the theorem as an exact equality of operators `P_{out} ∘ c_{nu, x} ∘ P_{in} = B_nu(x)` acting on `Budget(N_in, K_in)` into `Budget(N_out, K_out)`.
Proof strategy: Proceed by induction on the basis states (or the total energy $K$). First, explicitly calculate the action on the lowest-weight state (vacuum of the sector) to show the base case. Then, show that the intertwining relation holds with the creation operators (currents) to inductively generate the equality on all higher states within the truncated budget.
Auxiliary lemmas:
1. `base_state_equivalence`: Prove `c_{nu, x} |N> = B_nu(x) |N>` up to the necessary budget.
2. `intertwining_rho`: Show that the commutator `[ρ_{m, \nu}, c_x]` matches the corresponding commutator on the bosonic side, properly restricted to the finite budget spaces with projections.
