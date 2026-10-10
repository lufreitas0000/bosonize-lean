# Appendix A07 proposal: interaction domains and quadratic diagonalization

## Transfer domains and normal ordering

Chapter 17 must choose an integer transfer domain, e.g. $-M\le m\le M$, with every pair filtered by p=k+m in the band. A transfer m typed as a band residue does not define a nonwrapping target; its Nyquist boundary also fails closure under ordinary negation. Modular/wrapped scattering and truncated chiral currents are different models.

Only even species bilinears commute across different species. The fundamental fermions anticommute; the text's statement that species operators commute must be narrowed accordingly.

**Definition (Fermionic Normal Ordering):**
Define fermionic four-operator normal ordering before proving any contraction reduction. Reordering a middle creator past an annihilator uses an anticommutator, not the commutator formula claimed in the technical note. In particular $c^\dagger c^{\phantom{\dagger}}=\delta I-c^{\phantom{\dagger}}c^\dagger$ in the matched-index case. Ordinary `ring` cannot reorder endomorphisms; expand with distributivity and proved CAR/commutation rules, then normalize only scalar coefficients with `ring`.

*Lean 4 Proof Strategy:*
Specify sea quasiparticle creators and annihilators, then define full quartic Wick ordering on raw words with all contractions and fixed ordering. Bilinear vacuum subtraction does not define quartic ordering. Prove its evaluation lemmas before proposing any raw interaction reduction.
**Auxiliary Lemmas:** The canonical anticommutation relations (CAR), particularly $c_i^\dagger c_j^{\phantom{\dagger}}+c_j^{\phantom{\dagger}} c_i^\dagger=\delta_{ij}I$ and $c_i c_j+c_j c_i=0$.
**Strategy:** Use a well-founded word expansion with explicit CAR substitutions and decreasing length/inversion count. Expand noncommutative products in fixed order, use additive rearrangement for words, and normalize scalar coefficients separately.
**Carrier contract:** Evaluate words into the finite CAR `Module.End ℂ` carrier of A02, with $\delta I$ interpreted by complex scalar action on its identity. The sea occupation functional is the explicitly fixed vacuum expectation.

Chapter 17 now specifies vacuum subtraction and $\mu=\pi v_F/L$, which cancels the linear free zero-mode term. Its displayed coefficient is $(\pi v_F/L+g_4/(2L))(N_R^2+N_L^2)+(g_2/L)N_RN_L$. Chapter 17 now defines full sea-Wick ordering on raw words and states the exact correction $H_{4,\mathrm{raw}}=H_{4,\mathrm{current}}-\frac{g_4}{2L}\sum_\nu Q_{M,\nu}$ in Lemma 17.4a. Q counts sea holes and particles with the displayed finite-distance weights. Prove this ambient CAR identity before any physical use of the raw interaction; keep H4,current as the chosen quadratic model.

## Two different quadratic models

Let $C_R=\rho_{m,R}$, $A_R=\rho_{-m,R}$, and similarly for $L$, with $[A_\nu,C_\nu]=mI$ in the permitted action regime.

**Definition (Number-Conserving Mixing Form):**
*(Historical note: unoriented identical-branch representations produce this number-conserving hopping form)*:
$$
 H_{hop}=v_1(C_RA_R+C_LA_L)+v_2(C_RA_L+C_LA_R).
$$

*Lean 4 Proof Strategy:*
Formalize $H_{\mathrm{hop}}$ as an element of a non-commutative *-algebra representing the observables.
**Auxiliary Lemmas:** Verification that $H_{\mathrm{hop}}$ is self-adjoint ($H_{\mathrm{hop}}^\dagger=H_{\mathrm{hop}}$).
**Strategy:** Define $C_\nu$ and $A_\nu$ as formal symbols in an algebra modulo the relations $[A_\nu,C_\nu]=mI$. Represent $H_{\mathrm{hop}}$ directly as a linear combination of these bilinear generators.
**Adjoint contract:** In the finite model use A02 adjoints and $\rho_m^\dagger=\rho_{-m}$; in the abstract model use the star-compatible CCR quotient of A08. Do not derive global finite CCR from this quotient.

Its scalar mode matrix is `[[v1,v2],[v2,v1]]`. A sum/difference rotation diagonalizes it with coefficients $v_1+v_2$ and $v_1-v_2$. It does not yield two equal coefficients $\sqrt{v_1^2-v_2^2}$. For $v_1=5,v_2=3$, these are 8 and 2, whereas the common $u$ is 4.

**Definition (Pairing Form):**
The hyperbolic mixing of a right creator and left annihilator belongs instead to the pairing form:
$$
 H_{pair}=v_1(C_RA_R+C_LA_L)+v_2(C_RC_L+A_RA_L).
$$

*Lean 4 Proof Strategy:*
Define $H_{\mathrm{pair}}$ within the same *-algebra as $H_{\mathrm{hop}}$.
**Auxiliary Lemmas:** The action of the commutator $[H_{\mathrm{pair}},C_R]$ and similar generators.
**Strategy:** Construct the pairing Hamiltonian emphasizing that it creates and destroys pairs of excitations. We will map this quadratic form to a matrix representation over the Nambu spinor basis $(C_R,A_L)^T$ to facilitate Bogoliubov diagonalization.

With consistent computational creators Cν=ρm,ν on both branches, the raw opposite-transfer interaction factors into the hopping form. Chapter 17 chooses the distinct pairing form directly. An identification with a physical pairing/backscattering channel needs an explicit orientation/momentum dictionary and is not established by relabeling the computational currents.

## Scalar parameter package

**Lemma (Hyperbolic Parameter Existence):**
For the pairing model over real scalars, require $v_1>|v_2|$, not just $v_1^2>v_2^2$. The latter also permits negative v1 and does not guarantee positive energy. Specify u>0, u²=v1²−v2² and a real hyperbolic pair c,s with c²−s²=1. Prove existence once in the real scalar layer; downstream operator proofs should use only these algebraic relations.

*Lean 4 Proof Strategy:*
Formalize as a theorem in the real numbers: `∀ v1 v2 : ℝ, v1 > |v2| → ∃ u c s : ℝ, u > 0 ∧ u^2 = v1^2 - v2^2 ∧ c^2 - s^2 = 1 ∧ v1 = u*(c^2 + s^2) ∧ v2 = 2*u*c*s`.
**Auxiliary Lemmas:** Basic inequalities for real numbers, specifically relating squares and absolute values.
**Strategy:** Construct $u=\sqrt{v_1^2-v_2^2}$, $c=\sqrt{(v_1+u)/(2u)}$, $s=v_2/(2uc)$. Under `v1 > |v2|`, prove u>0 and c>0 before division, then prove the matching equations. This covers either sign of v2 and v2=0. Downstream operator lemmas use those equations without unfolding square roots.

Squaring an identity to obtain $(c^2-s^2)^2=1$ does not select c²−s²=+1. Supply its sign or make the desired identity a structure field. If scalars are complex, c²−s²=1 alone does not give a star-preserving transform; require real/self-adjoint scalars or use the appropriate conjugate relations.

**Theorem (Bogoliubov Transformation):**
For the plus-sign transform written in chapter 18,
$$
 \tilde C_R=cC_R+sA_L,\quad \tilde C_L=cC_L+sA_R,
$$
with adjoints tilde A, direct expansion gives
$$
 u(\tilde C_R\tilde A_R+\tilde C_L\tilde A_L)
 =u(c^2+s^2)(C_RA_R+C_LA_L)
 +2ucs(C_RC_L+A_RA_L)+2us^2mI.
$$
Thus v1=u(c²+s²), v2=2ucs for this direction of the plus-sign transform, and a vacuum constant must be subtracted to match H_pair. Other transformation directions can yield a minus sign; state the direction before choosing 2cs. The original matching signs cannot be adopted without this expansion.

*Lean 4 Proof Strategy:*
Formalize the substitution of the Bogoliubov transformed operators $\tilde C_ν$ and $\tilde A_ν$ into the target diagonalized Hamiltonian to recover the original $H_{\mathrm{pair}}$.
**Auxiliary Lemmas:** Expansion of bilinears: `(c C_R + s A_L)(c A_R + s C_L)`, and CCR application $A_L C_L=C_L A_L+mI$.
**Strategy:** This is a direct algebraic verification. Use `simp` with a configuration that unwraps the linear combinations, distributes the multiplication over addition, and applies the commutation relation $[A_\nu,C_\nu]=mI$ to properly align the normally-ordered cross terms. Finally, collect terms by $C_R A_R$, $C_L A_L$, etc., and equate their coefficients to `v1` and `v2`.
**Constant contract:** Subtract `2*u*s^2*m • 1` from the dressed number expression to match H_pair; sum it with the Chapter 18 prefactor `2π/L`. The bare finite ground vector and the constructed abstract dressed state of A08 are separate objects.

**Theorem (Restricted-Action CCR Preservation):**
The inverse two-by-two scalar transformation is global linear algebra. CCR preservation on a budget is a separate restricted-action theorem. Neither proves a unitary implementer or an algebra automorphism of all finite-Fock endomorphisms. The boundary commutator operators must still be present outside the permitted inputs.

*Lean 4 Proof Strategy:*
Define the "restricted action regime" as a specific subspace `V_m` of the Fock space where momentum/particle number cutoffs are strictly respected. State the theorem: $∀ |ψ⟩ ∈ V_m, [ \tilde A_ν, \tilde C_ν ] |ψ⟩ = mI |ψ⟩$.
**Auxiliary Lemmas:** The raw commutator $[ \tilde A_ν, \tilde C_ν ]$ expands to `mI + E_{boundary}`, where $E_{\mathrm{boundary}}$ are the error terms near the cutoff. A separate lemma showing $E_{\mathrm{boundary}}|\psi\rangle=0$ for strictly bounded states $|\psi\rangle$.
**Strategy:** Expand the commutator linearly. Apply the boundary lemma to annihilate the anomalous terms on the restricted subspace.

For v1>0 and v2≠0, u=√(v1²−v2²)<v1. Repulsive g2 alone does not guarantee a speed larger than the bare vF; the g4 contribution also matters. Correct the physical corollary accordingly.
