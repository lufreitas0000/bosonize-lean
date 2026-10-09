# Appendix A07 proposal: interaction domains and quadratic diagonalization

## Transfer domains and normal ordering

Chapter 17 must choose an integer transfer domain, e.g. `−M≤m≤M`, with every pair filtered by p=k+m in the band. A transfer m typed as a band residue does not define a nonwrapping target; its Nyquist boundary also fails closure under ordinary negation. Modular/wrapped scattering and truncated chiral currents are different models.

Only even species bilinears commute across different species. The fundamental fermions anticommute; the text's statement that species operators commute must be narrowed accordingly.

Define fermionic four-operator normal ordering before proving any contraction reduction. Reordering a middle creator past an annihilator uses an anticommutator, not the commutator formula claimed in the technical note. In particular `c†c = δI − cc†` in the matched-index case. Ordinary `ring` cannot reorder endomorphisms; expand with distributivity and proved CAR/commutation rules, then normalize only scalar coefficients with `ring`.

Fix the physical units and chemical potential once. The chapter 12 ground shift is N(N+1)/2; the chapter 17 N²/2 expression differs by N/2 per branch. That change is valid only with an explicit chemical-potential subtraction. With bare H₀=Σk n_k, the vacuum constant must also be removed or retained explicitly.

## Two different quadratic models

Let C_R=ρ_(m,R), A_R=ρ_(−m,R), and similarly for L, with `[Aν,Cν]=mI` in the permitted action regime.

Chapter 17 currently defines a number-conserving mixing form

\[
 H_{hop}=v_1(C_RA_R+C_LA_L)+v_2(C_RA_L+C_LA_R).
\]

Its scalar mode matrix is `[[v1,v2],[v2,v1]]`. A sum/difference rotation diagonalizes it with coefficients v1+v2 and v1−v2. It does not yield two equal coefficients √(v1²−v2²). For v1=5,v2=3, these are 8 and 2, whereas the proposed common u is 4.

The hyperbolic mixing of a right creator and left annihilator belongs instead to a pairing form

\[
 H_{pair}=v_1(C_RA_R+C_LA_L)+v_2(C_RC_L+A_RA_L).
\]

Opposite physical chiral momentum conventions can turn a spatial density interaction into this form, but that convention has not been implemented by merely calling two identical species R and L. Choose explicitly:

1. Keep H_hop and use an ordinary scalar rotation, with velocities v1±v2.
2. Construct the intended opposite-chirality dictionary and derive H_pair, then use the hyperbolic transform.

The second is likely the intended physical Luttinger model, but it requires revising the preceding chiral definitions and interaction factorization. Do not force the existing hopping form through a Bogoliubov proof.

## Scalar parameter package

For the pairing model over real scalars, require `v1>|v2|`, not just `v1²>v2²`. The latter also permits negative v1 and does not guarantee positive energy. Specify u>0, u²=v1²−v2² and a real hyperbolic pair c,s with c²−s²=1. Prove existence once in the real scalar layer; downstream operator proofs should use only these algebraic relations.

Squaring an identity to obtain `(c²−s²)²=1` does not select c²−s²=+1. Supply its sign or make the desired identity a structure field. If scalars are complex, c²−s²=1 alone does not give a star-preserving transform; require real/self-adjoint scalars or use the appropriate conjugate relations.

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

The inverse two-by-two scalar transformation is global linear algebra. CCR preservation on a budget is a separate restricted-action theorem. Neither proves a unitary implementer or an algebra automorphism of all finite-Fock endomorphisms. The boundary commutator operators must still be present outside the permitted inputs.

For v1>0 and v2≠0, u=√(v1²−v2²)<v1. Repulsive g2 alone does not guarantee a speed larger than the bare vF; the g4 contribution also matters. Correct the physical corollary accordingly.
