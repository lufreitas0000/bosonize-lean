# Appendix A07 proposal: interaction domains and quadratic diagonalization

## Transfer domains and normal ordering

Chapter 17 must choose an integer transfer domain, e.g. `−M≤m≤M`, with every pair filtered by p=k+m in the band. A transfer m typed as a band residue does not define a nonwrapping target; its Nyquist boundary also fails closure under ordinary negation. Modular/wrapped scattering and truncated chiral currents are different models.

Only even species bilinears commute across different species. The fundamental fermions anticommute; the text's statement that species operators commute must be narrowed accordingly.

**Definition (Fermionic Normal Ordering):**
Define fermionic four-operator normal ordering before proving any contraction reduction. Reordering a middle creator past an annihilator uses an anticommutator, not the commutator formula claimed in the technical note. In particular `c†c = δI − cc†` in the matched-index case. Ordinary `ring` cannot reorder endomorphisms; expand with distributivity and proved CAR/commutation rules, then normalize only scalar coefficients with `ring`.

*Lean 4 Proof Strategy:*
To formalize fermionic normal ordering, define a recursive function or inductive relation sorting products of creation/annihilation operators so all creators (`c†`) are left of annihilators (`c`). 
**Auxiliary Lemmas:** The canonical anticommutation relations (CAR), particularly `c_i† c_j + c_j c_i† = δ_{ij} I` and `c_i c_j + c_j c_i = 0`.
**Strategy:** Use structural induction on the operator word length, applying CAR rewrite rules. Standard `ring` cannot handle non-commutative operator algebras; instead, write a custom `simp` set (e.g., `simp only [CAR_rules]`) to push creators leftwards, followed by `abel` or `ring` only on the scalar coefficients of the resulting normally-ordered terms.
**Missing Framework Info:** Explicit typeclass boundaries for the CAR algebra and states in the Fock space need to be defined to ensure `δI` properly scales as an identity operator on the state space.

Fix the physical units and chemical potential once. The chapter 12 ground shift is N(N+1)/2; the chapter 17 N²/2 expression differs by N/2 per branch. That change is valid only with an explicit chemical-potential subtraction. With bare H₀=Σk n_k, the vacuum constant must also be removed or retained explicitly.

## Two different quadratic models

Let C_R=ρ_(m,R), A_R=ρ_(−m,R), and similarly for L, with `[Aν,Cν]=mI` in the permitted action regime.

**Definition (Number-Conserving Mixing Form):**
Chapter 17 currently defines a number-conserving mixing form
\[
 H_{hop}=v_1(C_RA_R+C_LA_L)+v_2(C_RA_L+C_LA_R).
\]

*Lean 4 Proof Strategy:*
Formalize `H_{hop}` as an element of a non-commutative *-algebra representing the observables.
**Auxiliary Lemmas:** Verification that `H_{hop}` is self-adjoint (`H_{hop}† = H_{hop}`).
**Strategy:** Define `C_ν` and `A_ν` as formal symbols in an algebra modulo the relations `[A_ν, C_ν] = mI`. Represent `H_{hop}` directly as a linear combination of these bilinear generators. 
**Missing Framework Info:** A robust definition of the adjoint `†` mapping `A_ν` to `C_ν` must be formally integrated so that we can structurally prove Hamiltonian hermiticity.

Its scalar mode matrix is `[[v1,v2],[v2,v1]]`. A sum/difference rotation diagonalizes it with coefficients v1+v2 and v1−v2. It does not yield two equal coefficients √(v1²−v2²). For v1=5,v2=3, these are 8 and 2, whereas the proposed common u is 4.

**Definition (Pairing Form):**
The hyperbolic mixing of a right creator and left annihilator belongs instead to a pairing form
\[
 H_{pair}=v_1(C_RA_R+C_LA_L)+v_2(C_RC_L+A_RA_L).
\]

*Lean 4 Proof Strategy:*
Define `H_{pair}` within the same *-algebra as `H_{hop}`.
**Auxiliary Lemmas:** The action of the commutator `[H_{pair}, C_R]` and similar generators.
**Strategy:** Construct the pairing Hamiltonian emphasizing that it creates and destroys pairs of excitations. We will map this quadratic form to a matrix representation over the Nambu spinor basis `(C_R, A_L)^T` to facilitate Bogoliubov diagonalization.

Opposite physical chiral momentum conventions can turn a spatial density interaction into this form, but that convention has not been implemented by merely calling two identical species R and L. Choose explicitly:

1. Keep H_hop and use an ordinary scalar rotation, with velocities v1±v2.
2. Construct the intended opposite-chirality dictionary and derive H_pair, then use the hyperbolic transform.

The second is likely the intended physical Luttinger model, but it requires revising the preceding chiral definitions and interaction factorization. Do not force the existing hopping form through a Bogoliubov proof.

## Scalar parameter package

**Lemma (Hyperbolic Parameter Existence):**
For the pairing model over real scalars, require `v1>|v2|`, not just `v1²>v2²`. The latter also permits negative v1 and does not guarantee positive energy. Specify u>0, u²=v1²−v2² and a real hyperbolic pair c,s with c²−s²=1. Prove existence once in the real scalar layer; downstream operator proofs should use only these algebraic relations.

*Lean 4 Proof Strategy:*
Formalize as a theorem in the real numbers: `∀ v1 v2 : ℝ, v1 > |v2| → ∃ u c s : ℝ, u > 0 ∧ u^2 = v1^2 - v2^2 ∧ c^2 - s^2 = 1 ∧ v1 = u*(c^2 + s^2) ∧ v2 = 2*u*c*s`. 
**Auxiliary Lemmas:** Basic inequalities for real numbers, specifically relating squares and absolute values.
**Strategy:** Construct witnesses `u = √(v1^2 - v2^2)`, `c = cosh(θ)`, `s = sinh(θ)` where `tanh(2θ) = -v2/v1`. The proof utilizes `positivity` to handle the square roots and `ring` / `linarith` coupled with `Real.cosh_sq_sub_sinh_sq` for the hyperbolic identities.

> [!WARNING]
> **Proof-review correction (2026-10-09):** The preceding `tanh(2θ) = −v2/v1` has the wrong sign for the displayed plus-sign transform and `v2 = 2*u*c*s`. An algebraic alternative is `u = √(v1²−v2²)`, `c = √((v1+u)/(2u))`, `s = v2/(2*u*c)`. Under `v1 > |v2|`, prove `u > 0` and `c > 0` before division. This covers negative and zero v2 without an inverse-hyperbolic construction.

Squaring an identity to obtain `(c²−s²)²=1` does not select c²−s²=+1. Supply its sign or make the desired identity a structure field. If scalars are complex, c²−s²=1 alone does not give a star-preserving transform; require real/self-adjoint scalars or use the appropriate conjugate relations.

**Theorem (Bogoliubov Transformation):**
For the plus-sign transform written in chapter 18,
\[
 \tilde C_R=cC_R+sA_L,\quad \tilde C_L=cC_L+sA_R,
\]
with adjoints tilde A, direct expansion gives
\[
 u(\tilde C_R\tilde A_R+\tilde C_L\tilde A_L)
 =u(c^2+s^2)(C_RA_R+C_LA_L)
 +2ucs(C_RC_L+A_RA_L)+2us^2mI.
\]
Thus v1=u(c²+s²), v2=2ucs for this direction of the plus-sign transform, and a vacuum constant must be subtracted to match H_pair. Other transformation directions can yield a minus sign; state the direction before choosing 2cs. The original matching signs cannot be adopted without this expansion.

*Lean 4 Proof Strategy:*
Formalize the substitution of the Bogoliubov transformed operators `\tilde C_ν` and `\tilde A_ν` into the target diagonalized Hamiltonian to recover the original `H_{pair}`.
**Auxiliary Lemmas:** Expansion of bilinears: `(c C_R + s A_L)(c A_R + s C_L)`, and CCR application `A_L C_L = C_L A_L + m I`.
**Strategy:** This is a direct algebraic verification. Use `simp` with a configuration that unwraps the linear combinations, distributes the multiplication over addition, and applies the commutation relation `[A_ν, C_ν] = mI` to properly align the normally-ordered cross terms. Finally, collect terms by `C_R A_R`, `C_L A_L`, etc., and equate their coefficients to `v1` and `v2`.
**Missing Framework Info:** The zero-point energy shift `2 u s^2 m I` must be physically interpreted and formally handled either by redefining the ground state energy explicitly or via normal-ordering the transformed Hamiltonian.

**Theorem (Restricted-Action CCR Preservation):**
The inverse two-by-two scalar transformation is global linear algebra. CCR preservation on a budget is a separate restricted-action theorem. Neither proves a unitary implementer or an algebra automorphism of all finite-Fock endomorphisms. The boundary commutator operators must still be present outside the permitted inputs.

*Lean 4 Proof Strategy:*
Define the "restricted action regime" as a specific subspace `V_m` of the Fock space where momentum/particle number cutoffs are strictly respected. State the theorem: `∀ |ψ⟩ ∈ V_m, [ \tilde A_ν, \tilde C_ν ] |ψ⟩ = mI |ψ⟩`.
**Auxiliary Lemmas:** The raw commutator `[ \tilde A_ν, \tilde C_ν ]` expands to `mI + E_{boundary}`, where `E_{boundary}` are the error terms near the cutoff. A separate lemma showing `E_{boundary} |ψ⟩ = 0` for strictly bounded states `|ψ⟩`.
**Strategy:** Expand the commutator linearly. Apply the boundary lemma to annihilate the anomalous terms on the restricted subspace.

For v1>0 and v2≠0, u=√(v1²−v2²)<v1. Repulsive g2 alone does not guarantee a speed larger than the bare vF; the g4 contribution also matters. Correct the physical corollary accordingly.
