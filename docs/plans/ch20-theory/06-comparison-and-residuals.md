# Independent theory prompt: What controlled finite comparison would close the Chapter 20 program?

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

Find a useful, falsifiable finite comparison target if global finite CAR/CCR
vertex or vacuum equality is unavailable. Do not redefine the physical operator
to make its error zero. For physical A,B and actual charge/budget projections,
R=P_t A(1-P_m)B P_s is a concrete discarded-channel operator; finite CH20 has
a nonzero example. Distinguish an intermediate projection residual from a
finite-mode truncation error, a wrong normal-order prefactor, a state-comparison
error and a dispersion error. They have different sources and hypotheses.

For fixed finite regulator, propose either: exact cancellation of R on a proven
subspace, exact selected matrix-element/moment comparison, coefficient agreement
through degree d with explicit margins, or an operator-norm bound on a common
finite inner-product carrier. An exact algebraic theorem is acceptable without
analytic asymptotics. If a norm is used, explicitly construct the common carrier
and bounded maps, with constants depending on L,M,K,N,c,s and d as appropriate.
Do not subtract operators that act on different spaces, and do not use an
uncompressed polynomial creation operator as a bounded finite map.

Analyze total-energy (not Cartesian-product) budgets, nonzero full ground images,
species twists, finite-cutoff same-species exchange and the absence of a generic
finite squeezed-vacuum common kernel. Derive one concrete candidate estimate or
exact degree bound and a counterexample outside its hypotheses. If comparing
physical and polynomial expectations, give both an operator dictionary and a
state comparison, rather than assuming one follows from the other.

Conclude with a version-1 closure matrix: target, carrier, assumptions, accepted
baseline used, missing mathematical argument, possible obstruction and validation
example. Recommend a bounded Chapter 20 research scope for human review. Keep
formal coefficientwise correlators, finite physical statements and continuum
interpretations in separate rows. State whether any proposed requirement is
unnecessary for finite CH21. A reviewed no-go result can close a question; it
cannot silently count as a proof of the originally desired equality.

## Required answer format

1. A precise verdict on the question, distinguishing proved-in-this-answer,
   conditional, contradicted and unresolved statements.
2. Exact mathematical objects, assumptions, domains and factor order.
3. A derivation with enough detail to audit; explicit counterexamples where useful.
4. A dependency map and a minimal theorem list, in ordinary mathematics only.
5. A small finite example or non-vacuity test and the limits of that example.
6. Remaining clarifying questions and references whose identifiers you verified.

Do not claim that a proposed theorem was checked by Lean. Do not move to coding.

## Read-only source evidence for exact finite conventions

The following existing definitions are context for mathematical analysis, not a
request to write or run code. They disambiguate the exact candidate and model.
Source names not expanded here denote the occupation CAR construction and actual
partition states described below. If a further implementation detail is needed,
name it precisely rather than assigning a convenient alternative definition.

For a configuration S, each occupied mode has a fixed species/momentum order;
annihilating j gives zero if j is absent, otherwise (-1) to the number of occupied
modes before j times the ket with j removed. Creation is its adjoint.
The excitation energy is summed across species. The partition ket p_N is the
ordered product of positive raw currents on the actual sea with occupied n<=N;
its squared norm is z_p=∏_{species,m} m^{k_m} k_m!. The kleinKernel below sends
p_N to kleinPhase(N) p_{N-eν} on the complete partition basis under pairMargin.
The Gram-kernel formula specifies the ambient map even outside that regime.
A01.normalization(L)=1/sqrt(L); characters, twists and validPairs retain their
actual source definitions. The wPlus/wMinus order must not be replaced by the
Weyl-type formal vertex order from another question.

Source: Bosonize/Core/Ch07VacuumBudget.lean

```lean
def relativeCharge (h : ℕ) (S : Occupation h) : ℤ := (S.card : ℤ)-(h : ℤ)

def excitationEnergy (h : ℕ) (S : Occupation h) : ℤ :=
  relativeEnergy h S - groundEnergy (relativeCharge h S)

def groundConfiguration (h : ℕ) (N : ℤ) : Occupation h :=
  Finset.univ.filter (fun k => k.val ≤ N)
```

Source: Bosonize/Core/A05MultiSpecies.lean

```lean
def r2 (h K : ℕ) (Ns : σ → ℤ) : Prop := ∀ ν, 2*(K : ℤ)+|Ns ν| ≤ (h : ℤ)

noncomputable def rho (h : ℕ) (ν : σ) (m : ℤ) : Operators σ h :=
  ∑ z ∈ A04.validPairs (2*h) m, Ch04.hopping (ν,z.1) (ν,z.2)

noncomputable def liftedAnnihilation (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (ν : σ) (x : ℤ) : Operators σ h :=
  (A01.normalization (2*h) : ℂ) •
    ∑ k : Ch01.Band (2*h), Ch06Ext.twistedCharacter (2*h) (b ν) k x • annihilation h ν k

omit [Fintype σ] in
```

Source: Bosonize/Core/Ch13KleinFactors.lean

```lean
def phaseExponent (h : ℕ) (Ns : σ → ℤ) (ν : σ) : ℤ :=
  (∑ η ∈ Finset.univ.filter (· < ν), ((h : ℤ)+Ns η)) + ((h : ℤ)+Ns ν-1)

noncomputable def kleinPhase (h : ℕ) (Ns : σ → ℤ) (ν : σ) : ℂ :=
  (-1 : ℂ) ^ phaseExponent h Ns ν

def pairMargin (h K : ℕ) (Ns : σ → ℤ) (ν : σ) : Prop :=
  A05.r2 h K Ns ∧ A05.r2 h K (lowerCharge Ns ν)

noncomputable def kleinKernel (h : ℕ) (Ns : σ → ℤ) (ν : σ) (K : ℕ) : Operators σ h :=
  ∑ p : A05.JointPartitions σ K,
    (kleinPhase h Ns ν / (A05.jointNormalization p : ℂ)) •
      ((innerₛₗ ℂ (A05.partitionState h Ns p)).smulRight
        (A05.partitionState h (lowerCharge Ns ν) p))
```
