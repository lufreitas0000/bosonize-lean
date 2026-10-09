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

**Theorem 14.5 (Cyclic Verification Criterion for a Projected Field Map).**
Let V be the source budget and W the target budget. Let v₀ be the source sector ground ket, Gᵢ ∈ End(V) the compressed source creators, Tᵢ ∈ End(W) target maps, and Rᵢ : V → W the common residual maps. Assume that the span of all finite words in the Gᵢ applied to v₀ is V. Linear independence is not needed; partition completeness can supply this cyclic-span hypothesis for the chosen source budget. The criterion works over a semiring with additive commutative group modules, although this application uses ℂ.

For A,B : V → W, assume the complete vector equality Av₀=Bv₀ and, for every generating index i, the typed identities
$$
A\circ G_i=T_i\circ A+R_i,\qquad B\circ G_i=T_i\circ B+R_i. \tag{14.7}
$$
Then A=B. No global CCR, irreducibility, or arbitrary numerical margin is assumed by this criterion. For a sector-cutoff diagram with several carriers, use the analogous induction with each suffix assigned its actual carrier; do not silently replace that diagram by endomorphisms of one slice.

*Lean 4 Proof Strategy:*
Subtract the two recurrences to obtain `(A-B).comp Gᵢ = Tᵢ.comp (A-B)`. Induct on word length to show the word orbit lies in `LinearMap.ker (A-B)`, use `Submodule.span_le.mpr`, and conclude by extensionality when the span is `⊤`. A basis version follows by `Module.Basis.ext`. The word/span criterion was compiler checked with `autoImplicit=false` and `warningAsError=true`. With varying carriers, prove equality recursively in the typed diagram instead. The common residuals may be nonzero: keep exact CAR edge and projection terms until a range/margin lemma makes them vanish. Prove the ground vector and recurrences independently, rather than installing the desired field equality as a premise.

**Physical specialization and full ground-vector obligation.** Take A=Pout ∘ c_(ν,x) ∘ inclusion and B the candidate (14.4). In the fixed occupation order of A02, if S_N is the joint sector ground occupation, its physical ground image is exactly
$$
A\delta_{S_N}=\frac1{\sqrt L}
 \sum_{\substack{k\in S_{N,\nu}\\ S_N\setminus\{(\nu,k)\}\text{ retained in target}}}
 (-1)^{\#\{j\in S_N:j<(\nu,k)\}}\zeta^{kx}
 \delta_{S_N\setminus\{(\nu,k)\}}.
$$
Compute the entire candidate image in the same occupation basis. Matching only the ground-to-ground scalar $L^{-1/2}P(\nu,\vec N)\zeta^{xN_\nu}$ does not satisfy the hypothesis. Before using the partition basis, require all-species completeness in both sectors:
$$
\forall\eta,\quad 2K_*+\max(|N_\eta|,|N_\eta-\delta_{\nu\eta}|)\le h,
\qquad K_*=\max(K_{\mathrm{in}},K_{\mathrm{out}}).
$$

**Research candidate (excluded from an unconditional Phase A interface).** The equality `Pout ∘ c_(ν,x) ∘ inclusion = Bν(x)` under numerical margins alone is not established. Mode coverage and all the hypotheses of Theorem 14.5 remain separate physical proof obligations. The former candidate margin
$$
2M+K_*+\max(|N_\nu|,|N_\nu-1|)\le h \tag{14.6}
$$
is only a possible wrapper for actual right-suffix bounds, not a sufficient theorem hypothesis. With h=6,L=12,N=0,Kin=0,Kout=2,M=1,x=0 the candidate gives coefficient $-1/(2\sqrt{12})$ for the hole at −2, while CAR gives $-1/\sqrt{12}$; missing mode 2 matters. Do not use M≥K* as a substitute for proving the full ground expansion and recurrences. This separation supplies a valid useful conditional theorem without freezing an unsupported finite field dictionary.
