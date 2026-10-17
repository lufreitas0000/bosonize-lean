# Independent theory prompt: What is the precise algebra/state duality, and can it act on finite CAR?

You are an independent mathematical physicist reviewing one open question in
Bosonize-Lean version 1. Work on mathematics and proof strategy only. Do not write
Lean code, shell commands, implementation patches or a proposed coding sprint.
Do not assume the desired identity is true. Derive it with explicit hypotheses,
or give a counterexample/no-go result and the strongest useful corrected target.
Ask clarifying questions only after extracting what can already be decided here.
Verify any references you use against primary papers/books; give exact title,
authors and DOI/arXiv or state uncertainty. Do not invent Mathlib APIs.

This prompt is self-contained mathematical context, not a claim that you can
access the local repository. If you need additional definitions, identify them
precisely. Distinguish established repository results from manuscript proposals
and from conclusions you derive in this answer. Your response will be independently
reviewed; it does not authorize coding or define the project's final scope.

## Verified baseline and notation

Source baseline: 40dea8bfbdc849417c072e490480d4f72536116a (2026-10-17 review).
CH01–18, CH19/A08 (62 contracts), and the finite CH20 package (64 contracts)
are promoted. There are 34 frozen Core modules. CH21 has an R&D proposal only.
CH20b is an internal name for the remaining Chapter 20 bridge, not a second
numbered chapter. The book has 21 chapters; inclusion is not Lean acceptance.
Version 1 must remain standalone. A future version 2 refactor on finiteQMB is
deferred and cannot be used to avoid this question.

Let h>0, L=2h, lattice positions x in Z/LZ, momentum representatives -h<n<=h,
and ζ=exp(2πi/L). There are finitely many fermion species, with a fixed linear
order and species twists. Their occupation CAR carrier is finite dimensional.
A charge label N is an integer for each species. B(N,K) is the span of actual
fermionic configurations in that sector with total excitation energy <=K.
P(N,K) is its coordinate orthogonal projection. Budgets are not independent
per-mode occupation cutoffs or unrestricted tensor products. h is not taken to
infinity. Operator multiplication is composition, rightmost factor acts first;
[A,B]=AB-BA and adjoints reverse products.

For positive bosonic mode m, C_{νm} raises and A_{νm} lowers. The unrestricted
relations [A_{νm},C_{ηn}]=m δ_{νη}δ_{mn}I, [A,A]=[C,C]=0 belong to the separate
uncompressed polynomial CCR carrier. Its variables are X_{νm}, 1<=m<=M, with
M finite but polynomial degree unbounded. C acts by multiplication, A=m∂/∂X.
The pairing is conjugate-linear in its first argument and
<X^α,X^β>=δ_{αβ} ∏_j α_j! m_j^{α_j}. Creation and annihilation are mutual
algebraic adjoints. A08 implements free words, their action and word-adjoint
identities, with state descent through CCR relations; do not assume a completed
Weyl C*-algebra or a pre-existing star quotient API.

ω0(a)=<1,π0(a)1>. For real c,s with c²-s²=1, define
β(C_Rm)=c C_Rm+s A_Lm, β(C_Lm)=c C_Lm+s A_Rm,
β(A_Rm)=c A_Rm+s C_Lm, β(A_Lm)=c A_Lm+s C_Rm.
The inverse substitution replaces s by -s. A08 constructs the normalized positive
linear functional ωP=ω0∘β^{-1}. It is not multiplicative. Dressed annihilators
are β(A); the vacuum equations have their actual order:
ωP(a β(A))=0 and ωP(β(C) a)=0.
ωP is not already a density matrix on End(B(N,K)). CH19 proves ordered finite
density kernels and a scalar finite-CAR ground-kernel comparison at s=0.
It does not identify all interacting states. A08 also proves a particular
three-dimensional compressed dressed-annihilator pair has common kernel {0}
when s≠0; this is a counterexample to a blanket finite squeezed-vacuum assumption,
not a theorem about every possible finite interacting Hamiltonian ground state.

Finite CAR density CCR require exact input/suffix margin hypotheses or explicit
edge operators. No nonzero finite-dimensional complex space supports global
[A,C]=mI for m≠0, by the trace identity. For typed source/middle/target projections,
P_t A B P_s - P_t A P_m B P_s = P_t A(1-P_m)B P_s.
The right side need not vanish. Do not infer product, state or star-algebra
transport just from a linear compression or agreement on one vector.

CH14 proves a conditional criterion for the actual projected field T and a
finite polynomial vertex candidate V: choose a cyclic ground vector v0 and
generators G_i on the source, H_i on the target, and common residual R_i.
If cyclicSpan(G,v0)=whole source, T v0=V v0 as full target vectors,
T G_i=H_i T+R_i and V G_i=H_i V+R_i, then T=V.
The full ground equality and common residuals are physical obligations, not
consequences supplied by the abstract theorem or by a single normalization.

Finite CH20 defines O_CDW(x)=c_R(x)† c_L(x) and O_SC(x)=c_R(x)c_L(x), with
charges (-1 in L,+1 in R) and (-1 in L,-1 in R), respectively. It proves charge,
adjoint and projected-product identities, a concrete nonzero discarded-channel
witness, parameter/phase transformations and properties of a finite scalar kernel.
It does not prove general interacting CAR vertex correlators or a finite-Fock
unitary duality. Those are precisely the kinds of gaps under discussion.
All analytic limits, substitution of t=1 into a formal series, thermodynamic
power laws, continuum QED3, entropy, RG beta functions and quench claims are
outside this question unless needed as a clearly labeled obstruction.

## Your one research question

Distinguish an algebraic model duality from a unitary symmetry of finite physical
fermions. Let P*=(c,-s), g(P*)=g(P)^{-1}. On oscillators the proposed map fixes
left C,A and negates right C,A. On charges let r(N_R,N_L)=(N_R,-N_L), with
U_r|N>=|rN> and charge conjugation by U_r. It sends F_L to F_L† and fixes F_R
under the given Klein convention. It fixes the central formal parameter t.

Use the candidate K_D,K_S,Q,X,W definitions specified here:
F_R|N>=|N-e_R>, F_L|N>=(-1)^{N_R}|N-e_L>,
Q_ν(x)=∑[ζ^{-ε_νmx}β_P(C_νm)+ζ^{ε_νmx}β_P(A_νm)]/m,
X_D=(c-s)(Q_R+Q_L), X_S=(c+s)(Q_R-Q_L),
K_D=F_R†F_L ζ^{(N_L-N_R-1)x}, K_S=F_RF_L ζ^{(N_R+N_L)x},
W_J=L^{-1}K_J Exp_f(itX_J), source phases acting before charge shifts.
The manuscript proposes D W_D(P,t,x)=ζ^x W_S(P*,t,x)† and the analogous
exchange D W_S=ζ^x W_D(P*)†. Audit the sign automorphism, involutivity,
star preservation, all charge shifts and phases. Derive the exact transport
law for the family ω_{P,N}; decide whether one state is invariant or the family
is transformed. Verify full ordered products, not only scalar g↔1/g.

Then investigate whether any corresponding map exists on the actual finite CAR
carrier and, separately, on chosen charge/budget sectors. Examine a left-species
particle-hole transformation with explicit fermionic parity strings and boundary
twists; this is a candidate to test, not an assumed implementation. Derive its
effects on charges, sea energy, density edge terms, occupation capacity, dimensions,
Hamiltonian constants, source/target budgets and CDW/SC operators. A charge
reflection in the formal charge lattice does not by itself give a finite unitary.

Provide either a finite implementation under precise conditions, a counterexample,
or a smaller typed equivalence retaining residuals. State which formal and finite
claims are logically independent and a minimal defensible version-1 target.

## Required answer format

1. A precise verdict on the question, distinguishing proved-in-this-answer,
   conditional, contradicted and unresolved statements.
2. Exact mathematical objects, assumptions, domains and factor order.
3. A derivation with enough detail to audit; explicit counterexamples where useful.
4. A dependency map and a minimal theorem list, in ordinary mathematics only.
5. A small finite example or non-vacuity test and the limits of that example.
6. Remaining clarifying questions and references whose identifiers you verified.

Do not claim that a proposed theorem was checked by Lean. Do not move to coding.
