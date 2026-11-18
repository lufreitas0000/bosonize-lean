# Bosonize-Lean: Project-State Review and Quench-Dynamics Research Handoff

**Review date:** 2026-10-17  
**Primary source:** *Constructive 1+1D Lattice Bosonization: Finite Constructions and Algebraic Models*, manuscript dated 2026-10-17, supplied as `main(3).pdf` (239 PDF pages).  
**Purpose:** A mathematically critical review, a proposed Lean 4/Mathlib4 theorem architecture, and a self-contained planning prompt for a Google Antigravity agent.  
**Scope of inspection:** The supplied manuscript and independently verified bibliographic metadata. **The Git repository, Lean source tree, test results, and validation-note files were not supplied or executed.** Consequently, assertions below about what is “promoted” or “in Core” are *statements made by the manuscript*, not independent repository findings.

> **Operational boundary:** This is a research and strategy packet. All Lean excerpts below are **non-compiling pseudocode** specifying interfaces and proof obligations, not code ready to merge. Antigravity must first audit the installed Mathlib API and existing project declarations. No source edits should be initiated in the initial planning pass.

---

## Executive decision

**Recommended next milestone:** Construct a **finite-mode, discrete-time, uncompressed CCR quench action**, derive the time-evolved bare generators, and certify the **coefficientwise neutral CDW/SC vertex covariance** with its finite translated kernels. Preserve the existing separation of (i) exact abstract oscillator identities, (ii) formal vertex series, and (iii) finite-CAR budget identities. Treat lattice-dispersion corrections, causal inequalities, interacting finite-CAR comparison, and thermodynamic GGE claims as independent follow-on problems.

This choice is preferred because:

1. Chapter 18 already provides the Bogoliubov relations, but does **not** prove that finite energy budgets are invariant under the interacting Hamiltonian.
2. Chapter 19 provides the appropriate **uncompressed polynomial oscillator state** and documents a completed Phase-C/Core milestone within a restricted scope.
3. Chapter 20.1 has a **promoted finite-CAR** component, whereas Chapter 20.2's formal vertices and Chapter 20.3's duality remain **manuscript-level constructions**.
4. A discrete cyclotomic clock produces exact **algebraic phase automorphisms**; it does not require exponentiating the full fermionic Hamiltonian.
5. The Gaussian quench correlator reduces to elementary finite sums and Wick contraction identities, giving measurable acceptance criteria and explicit small-system counterexamples.

Do **not** begin with a theorem asserting an exact interacting evolution on a finite budget, a strict finite-cutoff causal cone, or convergence to a GGE. Each statement currently lacks essential hypotheses and/or a representation-theoretic bridge.

---

## A. Evidence ledger: what the project notes actually say

### A.1 Source-based status table

| Scope | Manuscript evidence | Status supported by document | Required Git audit |
|---|---|---|---|
| Chapters 1–15 | Finite lattice, CAR net, energy budgets, current margins, finite Fourier transform, oscillator polynomial carrier, projected vertices | Developed in the manuscript; no blanket certification of every declaration inferred | Inventory modules, theorem names, exact hypotheses, and tests |
| Chapter 16, §§16.3–16.5 | Exact dispersion weight, finite weighted Hamiltonian, error operator, single-mode witnesses | Mathematically stated on protected budgets; asymptotic/RG comments are explicitly interpretations | Locate Lean theorems, distinguish exact identities from expansions |
| Chapter 17 | Raw interaction and pairing-model distinction, current-bilinear formulas | Manuscript-level source of the model choice | Check which quadratic Hamiltonian the Lean declarations actually define |
| Chapter 18 | Hyperbolic pair, dressed modes and finite-budget action identity (18.17)–(18.18) | **Explicitly not** an invariant finite-budget Hamiltonian or dressed finite-state ground theorem | Check certified scope, mode indices, and transformation conventions |
| Chapter 19, final status paragraph | “CH19/A08 Phase C is complete”; polynomial state, contractions, spatial kernel, Wightman correlations and protected *free* comparison promoted and audited in Core | **Reported Core promotion**, not independently confirmed here | Find the recorded validation note and replay proof build |
| Chapter 20.1, opening | Promoted Chapter 20 Core module: charge commutators, projected product decompositions, adjoints, ground coefficients, four-site residual witness | **Reported Core promotion** for the finite-CAR subsection | Identify exact declaration paths and non-vacuous tests |
| Chapter 20.2, §20.2.8 | Weyl-type formal vertices, coefficientwise Gaussian correlations, charge factors; “mathematical drafts awaiting independent review and potential Lean formalization” | **Not certified** by the monograph | Decide whether to certify this prerequisite before the quench chapter |
| Chapter 20.3, §20.3.7 | Algebraic duality at the manuscript level; explicitly “no implemented Chapter 20 Lean module certifying its statements” in that subsection | **Not certified** in the stated scope | Keep duality out of the first quench dependency chain |
| Appendix E, §E.1 | “CH19 proof batch ... Phase-B complete”; “neither fact is Core promotion” | **Stale/conflicting record** relative to Chapter 19's later Phase-C statement | Resolve against timestamped validation logs, current Git commit and actual proofs |

**Critical documentary inconsistency:** Chapter 19's concluding “Verification boundary” explicitly claims Phase C/Core completion, while Appendix E §E.1 uses an earlier Phase-B/not-Core narrative. The agent must not silently pick one as authoritative. The repository state and `note/ch19_phase_c_validation_2026-10-16.md` (mentioned in a manuscript footnote but **not** supplied here) must arbitrate.

**A second documentation risk:** Chapter 20.3 describes mathematical proofs in its prose but ends by saying no corresponding Chapter 20 Lean implementation certifies them. Distinguish **proved on paper**, **formally verified in Lean**, and **verified against finite fermions**.

### A.2 Scope limitations already stated in the manuscript

The following are not new objections; the manuscript itself warns about them:

- **Finite-dimensional CCR trace obstruction:** no global \([A,C]=mI\), \(m>0\), on the finite fermionic Fock space or a finite truncated oscillator space (Chapter 19, Proposition 19.1; Appendix E §E.6).
- **Non-invariant bare energy budget:** Chapter 18, following (18.18), says Hamiltonian identities are maps *from the budget into the ambient Fock space*, and can leave the budget. Its explicit example includes a pairing term that raises total bare energy outside the input shell.
- **Formal is not analytic:** Chapter 20.2 and Appendix E §E.5 evaluate each formal-series coefficient; setting the vertex parameter to 1 is not licensed without convergence.
- **Finite-CAR residuals:** Chapter 20.1 keeps the operator difference produced by inserting an intermediate budget projection; it cannot be erased by replacing the physical product with a compressed vertex.
- **Free versus interacting states:** Chapter 19's protected finite-state bridge applies to specified *bare current words* and the finite free sea. It does not identify the abstract dressed Gaussian state with the finite interacting Hamiltonian's ground state.
- **No finite-CAR model duality:** Chapter 20.3 explicitly limits its duality construction to the abstract oscillator–charge algebra.

### A.3 Research note versus implementation provenance

Before assigning implementation work, Antigravity must produce a **claim-to-theorem matrix** with columns:

`Manuscript section / exact claim / expected Lean symbol / actual symbol found / carrier / imported axioms / proof dependencies / build status / trust status / discrepancy / next action`.

Do not mark a theorem “implemented” merely because a file, namespace, definition, comment, test name, or `by trivial` compiles. For every substantial claim, inspect its theorem type, assumptions, proof body, and dependency closure. Mark `not found`, `source-only`, `compiles`, `audited`, and `validated` separately. In particular, compilation alone does not certify agreement between the formal theorem statement and the intended physics.

---

## B. Conventions to freeze before extending the library

Preserve the project's established conventions; do not rename or reinterpret symbols without an explicit migration plan.

| Item | Required convention |
|---|---|
| Lattice length | \(L=2h\), positive and even; site labels \(x\in\mathbb Z/L\mathbb Z\) |
| Band | \(-h<k\le h\), with positive Nyquist representative |
| Species | `R`, `L` or the existing `Branch` type; distinguish branch `L` from lattice size \(L\) |
| Positive modes | \(1\le m\le M\), with no-wrap/margin assumptions only where required by the finite-CAR bridge |
| Bare oscillator generators | \(C_{m,\nu}\) (creator) and \(A_{m,\nu}\) (annihilator), \([A_{m,\nu},C_{n,\eta}]=m\delta_{mn}\delta_{\nu\eta}I\) |
| Dressed generators | \(\widetilde C_{m,R}=cC_{m,R}+sA_{m,L}\), \(\widetilde A_{m,R}=cA_{m,R}+sC_{m,L}\), similarly with \(R\leftrightarrow L\) |
| Hyperbolic pair | \(c^2-s^2=1\), \(c,s\) self-adjoint real scalars; \(g=(c-s)^2>0\), \(g^{-1}=(c+s)^2\) |
| Oscillator Hamiltonian | \(H_{\mathrm{osc}}=(2\pi u/L)\sum_{m,\nu}\widetilde C_{m,\nu}\widetilde A_{m,\nu}\), with charge zero modes separately |
| Heisenberg convention | \(\tau_t(A)=e^{+iHt}Ae^{-iHt}\), so dressed creators gain \(e^{+i\omega_m t}\) |
| Chiral oscillator fields | \(\widetilde Q_R(x)=\sum_m(\zeta^{-mx}\widetilde C_{m,R}+\zeta^{mx}\widetilde A_{m,R})/m\), and opposite orientation for \(\widetilde Q_L\) |
| Formal order-parameter phases | \(X_{\mathrm{CDW}}=(c-s)(\widetilde Q_R+\widetilde Q_L)\), \(X_{\mathrm{SC}}=(c+s)(\widetilde Q_R-\widetilde Q_L)\) |
| Neutral correlator | \(\omega_0(\tau_n(W_J(x)^*W_J(y)))\); do not silently omit the adjoint |
| Formal parameter | \(\lambda\), **not** the clock variable \(n\); evaluation is coefficientwise in \(\lambda\) |

**Design warning:** The Chapter 17 raw interbranch *hopping* interaction and the Chapter 18 chosen interbranch *pairing* model are distinct. Audit the Hamiltonian used in Lean before identifying either with the physical post-quench Luttinger model.

### B.1 Three different “times”

Use different names and types for:

1. \(n\in\mathbb Z/L\mathbb Z\): **finite cyclotomic clock** for exact algebraic evolution; corresponding physical samples obey \(ut=n\) with an integer lift.
2. \(t\in\mathbb R\): **physical real time**, introduced only in a separate analytic interpretation with positive velocity \(u\).
3. \(\lambda\): **formal vertex exponent parameter**, the variable in a power series \(R[[\lambda]]\).

Do not combine the three in one implicit coercion. The proposal \(\zeta^{umt}\) is well-typed algebraically only when \(ut\) has a specified integral residue, or after enlarging the root-of-unity order. If \(ut=p/q\), a root of order \(qL\) is needed; a fixed \(L\)-cyclotomic field cannot describe arbitrary real times.

### B.2 Two distinct evolutions

- **Oscillator quench action:** acts on the uncompressed oscillator algebra; may act trivially on charge factors at the first milestone.
- **Full Hamiltonian evolution:** includes \(H_{\mathrm{zero}}\) acting on charge shifts. Its phases are generally **not** automatically \(L\)-cyclotomic, and its recurrence period need not be \(L/u\).

The neutral products \(W_J(x)^*W_J(y)\) can commute with a diagonal charge Hamiltonian when their net charge shift is zero; prove this instead of assuming the individual charged vertices have the same discrete period.

---

## C. Proposed algebraic theorem architecture

### C.1 Algebraic object and morphism graph

```text
      scalar field with involution and primitive L-th root ζ
                         │
                         ▼
        abstract uncompressed CCR *-algebra A_M
           │                           │
           │ β : Bogoliubov *-equiv     │ d_n : phase *-equiv
           └──────────────┬────────────┘
                          ▼
                  τ_n = β ∘ d_n ∘ β⁻¹
                          │
                  τ : ZMod L → Aut_*(A_M)
                          │
         ┌────────────────┼─────────────────┐
         ▼                ▼                 ▼
     bare current      chiral fields     neutral vertex
     evolution          covariance       formal series
         │                │                 │
         └────────────────┴───────┬─────────┘
                                  ▼
                     ω₀ ∘ τ_n evaluation
                                  │
                  exact translated D_M kernels
                                  │
                 recurrence and symmetry lemmas
                                  │
                separately: finite-CAR bridge
                                  │
               separately: analytic estimates
```

**Categorical carrier discipline:** `StarAlgEquiv` for automorphisms; `LinearMap` for evaluation and comparison into finite-carrier spaces; explicit subtypes for protected bands/budgets; `PowerSeries`-type objects for coefficientwise vertices. Avoid a global `Star` instance on all polynomial-space endomorphisms: a general algebraic endomorphism need not have an adjoint with respect to the weighted polynomial inner product. Put the involution on the **operator algebra generated by admissible creation/annihilation words**, or on a presented quotient.

### C.2 Two viable CCR implementation strategies

**Option 1 — Reuse existing algebra (preferred if CH19/A08 really promoted):** Identify the already audited CCR carrier and its star structure. Define time and Bogoliubov automorphisms by generator images and reuse its relation-preserving extension theorem. *No new universal algebra* unless a concrete missing capability is demonstrated.

**Option 2 — Presented CCR algebra:** Generate a noncommutative free algebra on creation/annihilation symbols, quotient by CCR relations, define a compatible star, and establish the universal mapping property. This offers a clean abstract interface but may substantially increase quotient, relation-ideal, and well-definedness proof burden. A polynomial representation can prove nontriviality and provide a state, but must be shown to annihilate the relation ideal.

**Do not** silently replace the noncommutative CCR algebra by `MvPolynomial`: the latter is commutative and is suitable as the **representation carrier**, not as the noncommutative oscillator-operator algebra itself. The concrete operators on `MvPolynomial` form a noncommutative subalgebra of linear endomorphisms.

### C.3 Preferred coefficient policy

For the algebraic core, the minimal axioms are a characteristic-zero coefficient field (or a \(\mathbb Q\)-algebra with all positive mode integers invertible), an involution, a primitive \(L\)-th root \(\zeta\) satisfying \(\zeta^*=\zeta^{-1}\), and star-invariant \(c,s\) satisfying \(c^2-s^2=1\).

The existing complex coefficients may be **simpler** than constructing and maintaining a new cyclotomic number field: one can use an abstract \(\zeta\in\mathbb C\) subject to algebraic root conditions and never invoke `Real.exp` or `Real.cos`. Positivity of a state is then naturally expressed using \(\mathbb R\)-valued inequalities. A generic algebraic field without an order should **not** be asked to certify positivity.

If a fully intrinsic cyclotomic field is nevertheless desired, its involution, self-adjoint hyperbolic parameters, embeddings and scalar coercions must be separately designed. Compare the formalization cost before committing.

---

## D. Exact quench identities to target

### D.1 Discrete phase and dressed evolution

For \(n\in\mathbb Z/L\mathbb Z\), write \(q_m(n)=\zeta^{mn}\). The finite oscillator action is

\[
\tau_n(\widetilde C_{m,\nu})=q_m(n)\widetilde C_{m,\nu},\qquad
\tau_n(\widetilde A_{m,\nu})=q_m(n)^{-1}\widetilde A_{m,\nu}.
\]

Prove, in this order:

1. \(q_m(n_1+n_2)=q_m(n_1)q_m(n_2)\), \(q_m(0)=1\), \(q_m(n)^*=q_m(n)^{-1}\).
2. The images preserve every CCR relation and the involution.
3. \(d_n\) and \(\beta\) are genuine algebraic \(*\)-equivalences.
4. \(\tau_n=\beta\circ d_n\circ\beta^{-1}\) is a group action. **Composition orientation must be verified** against the chosen definition of \(\beta\).
5. \(\tau_L=\mathrm{id}\) on the oscillator algebra; this alone says nothing about charged zero-mode evolution.

### D.2 Evolved bare generator (regression theorem)

With \(q=\zeta^{mn}\), the right bare creator must obey

\[
\boxed{\tau_n(C_{m,R})=(c^2q-s^2q^{-1})C_{m,R}
            +cs(q-q^{-1})A_{m,L}.}
\]

The other branch is obtained by interchanging \(R,L\); annihilators follow by adjoint. Test that \(n=0\) yields \(C_{m,R}\), and \(s=0,c=1\) yields \(qC_{m,R}\). Establish the analogous formulas for all generators before any field correlation proof.

### D.3 Spatially translated dressed fields

With the Chapter 20 opposite branch orientations, prove

\[
\tau_n(\widetilde Q_R(x))=\widetilde Q_R(x-n),\qquad
\tau_n(\widetilde Q_L(x))=\widetilde Q_L(x+n).
\]

This is a precise **transport identity**, not a statement of strict finite-cutoff causality.

### D.4 Exact finite quench variance

Define the symmetric algebraic finite kernel (using only cyclotomic characters)

\[
D_M(d)=\sum_{m=1}^{M}
 \frac{1-\tfrac12(\zeta^{md}+\zeta^{-md})}{m}.
\]

All spatial arguments belong to \(\mathbb Z/L\mathbb Z\). Define

\[
\begin{aligned}
A_{\rm CDW}&=(c-s)^2(c^2+s^2)=\tfrac12(1+g^2),\\
B_{\rm CDW}&=2(c-s)^2cs=\tfrac12(1-g^2),\\
A_{\rm SC}&=(c+s)^2(c^2+s^2)=\tfrac12(1+g^{-2}),\\
B_{\rm SC}&=-2(c+s)^2cs=\tfrac12(1-g^{-2}).
\end{aligned}
\]

In each channel, \(A_J+B_J=1\). For \(d=y-x\), the **target exact covariance** is

\[
\boxed{
\begin{aligned}
V_J(d,n)&=4\Phi_J(d,n),\\
\Phi_J(d,n)&=A_JD_M(d)
+\frac{B_J}{2}\left[D_M(d+2n)+D_M(d-2n)-2D_M(2n)\right].
\end{aligned}}
\]

**Do not drop \(-2D_M(2n)\)**. It is necessary for \(V_J(0,n)=0\). The formula is a proposed next theorem, not yet claimed to be formally verified.

Useful sanity conditions:

- \(V_J(d,0)=4D_M(d)\) for both channels, recovering the bare initial state.
- \(V_J(0,n)=0\).
- For \(g=1\) (equivalently \(s=0\) under the stable real convention), \(V_J(d,n)=4D_M(d)\) at all times.
- \(V_J(d,n+L/2)=V_J(d,n)\) for even \(L\).
- \(V_J(-d,n)=V_J(d,n)\), \(V_J(d,-n)=V_J(d,n)\).
- Positivity \(V_J(d,n)\ge0\) should be proved from \(\omega_0(Y^*Y)\ge0\), *not* from termwise positivity of the displayed translated-kernel decomposition (individual \(B_J\) may be negative).

### D.5 Coefficientwise neutral vertex correlators

Following Chapter 20, take ordered charge factors \(K_J(x)\) and formal vertices

\[
W_J(\lambda,x)=L^{-1}K_J(x)
  \operatorname{Exp}_{\rm form}\!\bigl(i\lambda X_J(x)\bigr).
\]

At the oscillator-only quench level, the expected neutral result is

\[
\boxed{
\omega_{0,\vec N}\left(\tau_n(W_J(\lambda,x)^*W_J(\lambda,y))\right)
=L^{-2}\chi_J(\vec N;y-x)
\operatorname{Exp}_{\rm form}\bigl(-2\lambda^2\Phi_J(y-x,n)\bigr).
}
\]

Here \(\omega_{0,\vec N}\) denotes the bare oscillator vacuum tensored with the fixed charge-sector vector functional. The chapter's source charge phases are

\[
\chi_{\rm CDW}=\zeta^{(N_L-N_R-1)(y-x)},\qquad
\chi_{\rm SC}=\zeta^{(N_R+N_L)(y-x)}.
\]

These factors must be checked against existing implementation conventions, including ordered Klein cocycles. The theorem must be stated **in a formal series ring**, with equality meaning equality of coefficients. A complex-valued physical correlator evaluated at \(\lambda=1\) is **a separate analytic theorem**.

**Order-of-proof constraint:** certify the Chapter 20.2 formal vertex construction (if it is absent in Core) before treating this quench theorem as a consequence of existing Lean infrastructure.

### D.6 Revival statements: two different periods

1. The full **oscillator automorphism** has \(\tau_{n+L}=\tau_n\), hence at the sampled physical times \(T_{\rm osc}=L/u\).
2. The displayed **neutral equal-time covariance and correlators** obey \(V_J(d,n+L/2)=V_J(d,n)\), hence \(T_{\rm corr}=L/(2u)\) (possibly non-minimal for special observables).

They are not interchangeable. Charge-changing observables and the full zero-mode evolution can have another recurrence structure. The agent must explicitly classify *which algebra and observable* each claimed period applies to.

---

## E. What must **not** be asserted in Phase 1

### E.1 No strictly vanishing correlations outside a cone

The exact translated-kernel identity contains \(D_M(d\pm2n)\), but a finite Fourier cutoff produces nonlocal tails. A formal discrete equality is not an operator-norm Lieb–Robinson estimate. Initial equilibrium correlations are themselves spatially extended, so “before the light cone the correlator is zero” is especially inappropriate.

For any quantitative cone theorem, specify:

- The ring metric \(\mathrm{dist}_L(x,y)=\min(|\tilde d|,L-|\tilde d|)\), with an explicit integer lift \(\tilde d\).
- The observable to be bounded: commutator norm, change in connected correlator, or difference from an asymptotic reference.
- A cutoff scaling \(M(L)\), allowable tail/error \(\epsilon\), and the admissible time interval before wrap-around.
- Whether the theorem concerns the strictly local finite-CAR Hamiltonian (requiring a locality proof) or the nonlocal momentum-truncated effective Hamiltonian.

Cite Lieb–Robinson only when its locality assumptions actually hold for the chosen microscopic generator.

### E.2 No automatic finite-budget dynamics

The finite-CAR current identities can be exact on protected word domains, but products of the pairing Hamiltonian can exit the budget. The compressed map \(PHP\) generates a *different* effective dynamics from unrestricted \(H\) and is not an automorphism of the protected CCR algebra. If the project later needs a physical finite-CAR quench, define its ambient dynamics and compare specified matrix elements; never silently infer it from \(\tau_n\) on the uncompressed CCR algebra.

### E.3 No finite-volume GGE convergence

Exact recurrence excludes strict long-time convergence of nonconstant correlators at fixed finite \(L\). A formal mode-dephasing average of a variance also does not generally commute with exponentiation of that variance. A GGE comparison requires a thermodynamic sequence, order of limits, observable class, and a mode-occupation description of the candidate stationary state. “Modewise stationary covariance” and “stationary vertex expectation” are distinct propositions.

---

## F. Dispersion-error research track (separate from the first implementation gate)

### F.1 Exact input from Chapter 16

\[
\varepsilon_L(m)=\frac{L}{m^2}(\zeta^m-1)(\zeta^{-m}-1),\quad
 g_0=\varepsilon_L(1),
\]

\[
E_{\rm error}=4\sum_{m,\nu}(\varepsilon_L(m)-g_0)C_{m,\nu}A_{m,\nu}
\quad\text{on the protected budget},
\]

with single-mode error eigenvalue \(4m(\varepsilon_L(m)-g_0)\) on the specified bare states. These identities are **not** a proof that one may change only the dressed frequencies while keeping \(c,s\) fixed.

### F.2 Required research fork

**Track F1 — Effective diagonal dispersion (simpler but explicitly an approximation):** Postulate a dressed diagonal model with \(\Omega_m=\omega_m+\delta_m\). Derive phase-error bounds and characterize recurrence loss. Its per-mode dynamics can be represented algebraically by unit phase variables \(q_m\), independent of the fixed \(L\)-cyclotomic clock, until an analytic specialization is supplied.

**Track F2 — Add the actual Chapter-16 bare-current error (more faithful):** Add the operator with consistent energy normalization, recompute the modewise quadratic Bogoliubov matrix, check its stability, and derive **mode-dependent** parameters \(c_m,s_m,u_m\). The old single \((c,s)\) hyperbolic pair need not diagonalize the corrected Hamiltonian. Root extractions and full time phases generally leave the original cyclotomic field.

**Decision rule:** First derive the exact operator-level normal-form coefficients on paper from the conventions of Chapters 16 and 18; do **not** guess conversion prefactors. Only then select F1 or F2 for certification.

### F.3 Conditional error horizon

Under F1, \(\Omega_m=(2\pi um/L)\,\varepsilon_L(m)/\varepsilon_L(1)\), for \(m/L\ll1\),

\[
\delta_m=-\frac{2\pi^3u}{3L^3}m(m^2-1)
+O\!\left(\frac{u(m^5+m)}{L^5}\right).
\]

For a maximal relevant mode \(m_*\), a *sufficient uniform small-phase-error criterion* is

\[
|t|\max_{m\le m_*}|\delta_m|\ll1,
\qquad
 t^*\sim\frac{L^3}{u m_*^3}.
\]

This is **conditional analytic asymptotics for the chosen effective dispersion**, not a theorem of the current cyclotomic implementation. The meaning of \(m_*\) must be tied to the observable's spectral support and intermediate excursions; bare budget \(K\) by itself is not a universal quench horizon.

A useful exact intermediate estimate in the analytic layer is

\[
|e^{i(\omega_m+\delta_m)t}-e^{i\omega_m t}|
\le\min(2,|t\delta_m|).
\]

Then derive a weighted finite-mode variance bound. At \(t=L/u\), the leading modal phase defect is of order \(m_*^3/L^2\), so \(m_*^3\ll L^2\) is sufficient for uniformly small leading defects, not necessary for every observable.

---

## G. Lean interface sketches — **pseudocode, not compilable Lean**

**Naming discipline:** These examples are *semantic contracts*. The Antigravity agent must map them onto the actual repo names/types and verify the pinned Mathlib APIs before defining anything. Symbols such as `CCRAlgebra`, `Mode`, `StarAlgEquiv`, `FormalVertex`, and `CoeffwiseState` stand for existing or future carrier choices, not an assertion that the packages currently provide those exact declarations.

### G.1 Parameters and clock

```lean
-- NON-COMPILING PSEUDOCODE: mathematical interfaces only
structure QuenchDatum (L M : Nat) where
  h : Nat
  even_length : L = 2 * h
  mode_bound : M < h           -- only if needed by a chosen bridge
  zeta : Scalar
  zeta_primitive : PrimitiveRoot zeta L
  zeta_star : star zeta = zeta⁻¹
  c s : Scalar
  c_selfadjoint : star c = c
  s_selfadjoint : star s = s
  hyperbolic : c^2 - s^2 = 1

abbrev Clock (L : Nat) := ZMod L

abstract def phase (P : QuenchDatum L M)
    (m : PositiveMode M) (n : Clock L) : Scalar

claim phase_add : phase P m (n₁ + n₂) = phase P m n₁ * phase P m n₂
claim phase_star : star (phase P m n) = (phase P m n)⁻¹
```

Use exact positive-mode indices rather than accidentally including mode zero. Do **not** make the finite-CAR margin a global precondition for algebraic CCR dynamics if that layer does not need it.

### G.2 Automorphism interfaces and generator proofs

```lean
-- NON-COMPILING PSEUDOCODE
abstract def bogoliubovEquiv (P) : StarAlgEquiv Scalar CCRAlgebra CCRAlgebra
abstract def dressedPhaseEquiv (P) (n : Clock L)
    : StarAlgEquiv Scalar CCRAlgebra CCRAlgebra

-- Composition is MATHEMATICAL notation; inspect `.trans` direction locally.
abstract def heisenberg (P) (n : Clock L)
    : StarAlgEquiv Scalar CCRAlgebra CCRAlgebra :=
  bogoliubovEquiv P ∘ dressedPhaseEquiv P n ∘ (bogoliubovEquiv P)⁻¹

claim heisenberg_zero : heisenberg P 0 = identity
claim heisenberg_add : heisenberg P (n₁ + n₂)
    = heisenberg P n₁ ∘ heisenberg P n₂
claim evolves_dressed_creator :
    heisenberg P n (dressedCreator P m nu)
      = phase P m n • dressedCreator P m nu
claim evolves_bare_creator_R : ...   -- equation in §D.2
```

**Critical proof detail:** The *actual* automorphism extension must be justified by preservation of the CCR defining relations, scalar action, and star. Merely defining images on two generators does not produce an automorphism of the quotient.

### G.3 Finite kernel and covariance

```lean
-- NON-COMPILING PSEUDOCODE
abstract def cyclotomicCos (P) (m : PositiveMode M)
    (d : ZMod L) : Scalar :=
  (character P m d + (character P m d)⁻¹) / 2

abstract def D (P) (d : ZMod L) : Scalar :=
  sum (m : PositiveMode M),
    (1 - cyclotomicCos P m d) / (m : Scalar)

inductive Channel | CDW | SC

abstract def channelA (P) : Channel → Scalar
abstract def channelB (P) : Channel → Scalar

abstract def phi (P) (J : Channel) (d n : ZMod L) : Scalar :=
  channelA P J * D P d
    + (channelB P J / 2) *
        (D P (d + 2*n) + D P (d - 2*n) - 2*D P (2*n))

claim phi_initial : phi P J d 0 = D P d
claim phi_coincident : phi P J 0 n = 0
claim phi_half_period : phi P J d (n + L/2) = phi P J d n
claim field_variance : vacuum (differenceField(P,J,d,n)^2)
                        = 4 * phi P J d n
```

The notation `L/2` must become the integer \(h\) coerced into `ZMod L`; division by 2 *inside* `ZMod L` is not valid because 2 is not a unit when \(L\) is even.

### G.4 Formal power-series and neutral correlator

```lean
-- NON-COMPILING PSEUDOCODE
abstract def vertex (P) (J : Channel) (x : ZMod L)
    : PowerSeries CCRChargeAlgebra

abstract def coefficientwiseState (P) (charge : ChargeVector) (n : Clock L)
    : LinearMap Scalar (PowerSeries CCRChargeAlgebra) (PowerSeries Scalar)

claim neutral_vertex_quench (P) (J) (x y : ZMod L) (n : Clock L) :
  coefficientwiseState P charge n
    (star (vertex P J x) * vertex P J y)
    = (chargeCharacter P J (y-x) / L^2)
         • formalExp (-2 * phi P J (y-x) n * lambda^2)
```

The exact placement of `star`, `lambda`, ordered charge factors and multiplications must follow the **existing** formal-series representation. Verify that the pinned Mathlib `PowerSeries` instances support the intended noncommutative coefficient semiring and star operation; otherwise specify the coefficientwise construction explicitly. Treat this as a theorem shape, not a specification of Mathlib elaboration.

### G.5 Finite-CAR comparison (deferred)

```lean
-- NON-COMPILING PSEUDOCODE
structure CertifiedCurrentWord where
  word : List CurrentGenerator
  excursionBound : Nat
  validMargins : ProtectedDomainPredicate

abstract def physicalWordMap (w : CertifiedCurrentWord)
  : LinearMap Scalar FiniteCARCarrier FiniteCARCarrier

claim protected_word_comparison (w) (v w' : ProtectedBosonCarrier) :
  inner (embed v) (physicalWordMap w (embed w'))
    = inner v (abstractCCRWord w w')
```

Avoid the use of intermediate projectors unless the residual of Chapter 20.1 is explicitly retained. An all-orders vertex statement cannot be deduced from a fixed finite excursion bound.

---

## H. Proof DAG and implementation gates

The following sequence is intentionally modular. A gate is passed only when every required declaration compiles, the corresponding physical theorem statement has been audited, and the supplied verification artifacts exist.

| Gate | Deliverable | Dependencies | Acceptance / rejection criteria |
|---|---|---|---|
| **0 — Reconnaissance** | Repository map, exact git commit, pinned Lean/Mathlib versions, statement inventory, mismatch report | No code changes | No guessed modules; conflicts in Ch19/Appendix E resolved or flagged as unresolved |
| **1 — Mathematical specification** | Frozen definitions for clock, generator orientation, Hamiltonian normalization, charge action, covariance | Gate 0 | Signed modes, current normalization and positive-mode conventions written unambiguously |
| **2 — CCR phase action** | Root-of-unity lemmas, star-equivalence, group action | Approved CCR algebra | `identity`, `composition`, `star`, `CCR` and generator actions all proved |
| **3 — Bogoliubov conjugation** | Evolved bare creators/annihilators, chiral transport | Gates 1–2 | Correct \(n=0\), \(s=0\), inverse and adjoint identities |
| **4 — Gaussian covariance** | Two-channel exact \(V_J=4\Phi_J\) | Gate 3, CH19 Wick state | \(d=0\), \(n=0\), \(g=1\), half-period, positivity tests; no unproved cos rewrite |
| **5 — Formal vertices** | Chapter 20.2 prerequisite formalized, coefficientwise quench correlator | Gate 4 + verified charge algebra | Correct neutral product, ordered Klein factors, charge characters, no `lambda=1` evaluation |
| **6 — Recurrence classification** | Oscillator \(L\) period and neutral \(L/2\) period | Gates 2, 5 | Explicitly excludes unsupported claim about zero-mode/charged periodicity |
| **7 — Physical bridge research** | Bounded-word comparison plan and/or finite-CAR defects | Gates 0–6 | Hypotheses include word excursions and surviving projection remainders |
| **8 — Dispersion / causality / GGE research** | Separate mathematical requirements and conditional estimates | Gates 0–6 | No unproved finite-\(L\) GGE or strict light-cone assertion |

Suggested development arrangement is **one proof milestone per reviewable module**, aligned with existing naming conventions rather than inventing a parallel hierarchy. Candidate *conceptual* folders are `Quench/Clock`, `Quench/CCRAction`, `Quench/Covariance`, `Quench/Vertex`, `Quench/Recurrence`, `Quench/FiniteCARBridge`, and `Quench/Dispersion`. **These are not instructions to create folders yet.** First identify equivalent existing modules and prefer extending them or adding minimal new files.

### H.1 Non-vacuity/regression checks

Use the already documented **16-site witness**:

\[
L=16,\quad h=8,\quad M=2,\quad (c,s)=(5/4,3/4),\quad g=1/4.
\]

Choose budget \(K=2\), charge vector zero where relevant; the documented branch margin \(2M+K=6\le8\) holds. In the *abstract* CCR layer the margin need not be imposed; it becomes relevant only for the finite-CAR comparison.

- Prove that the nontrivial interaction produces a nonconstant time-dependent covariance for some \(d,n\) (find an explicit witness, not `True`).
- Prove exact agreement with bare correlations at \(n=0\).
- Prove the distinct oscillator and neutral-correlator periods.
- Check both right and left branch signs independently.
- Compare the cyclotomic formula against a separate **non-certifying** rational/numerical calculation for low modes. Independent computation is a regression aid, not a replacement for proof.
- Confirm a nonzero finite-CAR projection residual remains nonzero in the documented four-site witness; a new quench API must not erase this established obstruction.

**Adversarial acceptance:** Failure is mandatory if an agent uses `sorry`, `admit`, an unapproved new axiom, a hidden postulate of global finite-dimensional CCR, a tautological placeholder in place of a desired theorem, or a theorem statement weaker than the stated physics while labeling the task complete. Audit all transitive project-specific axioms and dependencies. Distinguish trusted Mathlib kernel axioms from newly introduced domain-specific assumptions.

---

## I. Research questions and decision register

**Must be answered before Gate 2:**

1. **Existing carrier:** What is the exact Lean type of the CH19 oscillator algebra and where are its universal generator/representation laws? Is there a reusable star-equivalence constructor?
2. **Clock versus full dynamics:** Is the initial goal restricted to oscillator time evolution and neutral correlators, or must the action also implement \(H_{\mathrm{zero}}\) on charge shifts? If the latter, is a cyclotomic clock still closed under the required phases?
3. **Order-parameter object:** Should the new theorem refer to formal Weyl-type vertices from Chapter 20.2 or finite-CAR products from 20.1? The default proposal is the former; the latter is a bridge problem.
4. **Dispersion model:** Is the aim the independently diagonal dressed-mode approximation F1 or the correctly re-diagonalized microscopic correction F2? No dispersion implementation before that decision.
5. **Success criterion for “causal horizon”:** What precise observable, topology, metric, cutoff scaling and error tolerance define it? An exact translated kernel alone is insufficient.

**Recommended defaults if the repo audit finds no contrary constraints:** use complex scalars with algebraic primitive-root hypotheses; `Clock := ZMod L`; uncompressed CH19 CCR carrier; Chapter 20.2 formal vertices; oscillator-only first; coefficientwise correlation theorem; postpone zero-mode/full physical time, causality, GGE and dispersion.

---

## J. Antigravity prompt — paste as a single research/planning instruction

The following block is deliberately self-contained. Attach this Markdown file and the source monograph if possible. Allow Antigravity to inspect the existing local repository, but **not** to edit it during this first response.

```text
ROLE
You are the repository auditor, mathematical-physics research architect, and Lean 4/
Mathlib4 formalization planner for the Bosonize-Lean project. Work critically and
produce an independently auditable implementation and research plan.

SOURCE AND TRUST PRIORITIES
1. First read the attached "Bosonize-Lean: Project-State Review and Quench-Dynamics
   Research Handoff" thoroughly.
2. Inspect the actual repository, its README/AGENTS.md policies, lakefile,
   lean-toolchain, manifest, active branch, Git commit, source hierarchy,
   notes, and existing tests.
3. If accessible, read the supplied manuscript "Constructive 1+1D Lattice
   Bosonization" (main(3).pdf), especially Chapters 16-20 and Appendix E.
4. Existing proved Lean declarations and reproducible validation logs determine
   the formalized status. The manuscript is authoritative about intended
   mathematics, but not automatically about what currently compiles.
5. Do not invent Lean declaration names, imported modules, files, references,
   arXiv IDs, DOIs, proof status, or an implementation that is not present.

FIRST-TURN MODE: RECONNAISSANCE AND PLANNING ONLY
Do not edit existing files, generate Lean implementation, change dependencies,
create new directory structures, or attempt a sweeping refactor. Read and report.
You may run read-only inspections and local build/tests if allowed by existing
project policy, and must record actual commands and exit statuses.
No source mutation without an explicit subsequent authorization.

MANDATORY AUDIT
A. Record current branch, commit hash, modified/untracked status, Lean version,
   Mathlib revision, and a minimal reproducible build/test report.
B. Identify the modules/theorems corresponding to Chapter 18's hyperbolic pair,
   dressed currents and budget-action identity, Chapter 19's vacuum and
   protected bridge, and Chapter 20's finite CAR products/formal vertices.
C. Resolve or explicitly flag the conflicting status of Chapter 19's Phase C
   Core promotion and Appendix E's earlier Phase B statement. Locate the
   validation note referenced as note/ch19_phase_c_validation_2026-10-16.md
   if it actually exists. Never assume the file exists.
D. Verify Chapter 20.1's promoted finite-CAR theorems and distinguish them
   from the unimplemented/draft Chapter 20.2 and 20.3 mathematics.
E. Produce a claim-to-theorem matrix: manuscript claim, file, declaration,
   formal carrier, assumptions, exact statement, axioms, dependencies,
   compilation/validation status, gaps.
F. Perform an adversarial proof audit: look for sorry/admit/new axioms,
   fake-green tests, circular dependency, tautological theorem statements,
   vacuous assumptions and unrecorded mathematical approximations.
   Kernel-valid constructive tactics are allowed but must prove the intended
   statement, not a weakened substitute.

MATHEMATICAL OBJECTIVES (IN ORDER)
1. Define the intended exact ZMod L cyclotomic oscillator clock on the
   uncompressed CCR algebra; distinguish it from real time and vertex
   formal-series parameter lambda.
2. Reuse the existing Bogoliubov equivalence if one exists; otherwise
   compare the cost of an abstract presented CCR algebra versus its concrete
   represented operator subalgebra. Do not assume `MvPolynomial` is the CCR
   operator algebra; it is a commutative polynomial representation carrier.
3. State a group action by star-algebra equivalences, prove generator
   transformations and CCR/star preservation, and check composition order.
4. Derive bare current evolution and opposite-orientation chiral transport.
5. Reuse/complete the CH19 Gaussian Wick state and formalize CH20.2
   coefficientwise vertices if they are not already verified.
6. Prove the two-channel exact quench covariance
      Phi_J(d,n) = A_J*D_M(d)
           + (B_J/2)*(D_M(d+2*n)+D_M(d-2*n)-2*D_M(2*n)).
   Preserve the subtraction term and verify A_J+B_J=1.
7. Prove the formal neutral vertex correlator only after fixing ordered
   charge/Klein factors and the action on charge zero modes.
8. Distinguish oscillator period L from neutral correlator half-period L/2.
   Do not assert the period of charged/full dynamics without extra proof.
9. Plan (do not yet implement) bounded-word finite-CAR comparison, actual
   Chapter-16 dispersion re-diagonalization, quantitative locality estimates,
   and thermodynamic GGE research as separate branches.

CRITICAL PHYSICS RESTRICTIONS
- The finite budget is not automatically invariant under H_Lutt.
- There is no global nonzero scalar CCR representation by finite matrices.
- Finite Fourier sums give propagation kernels but not a strict causal cone.
- Fixed finite size revivals preclude simple t->infinity GGE convergence.
- Adding E_error in bare modes generally changes mixing angles, not just
  frequencies; do not keep c,s unchanged without an effective-model assumption.
- Formal vertex coefficient identities are not convergent complex correlators
  at lambda=1 absent an analytic theorem.
- The Chapter 17 raw hopping and Chapter 18 pairing models must not be
  equated without proving the choice of Hamiltonian.

SOFTWARE ARCHITECTURE
Prefer generic pure morphisms: StarAlgEquiv, AlgEquiv, LinearMap,
explicit subtype/index types, and the existing formal power-series carrier.
Keep abstract CCR, charge algebra, finite-CAR bridge, and analytic asymptotics
separate. Avoid duplicate module hierarchies and unnecessary dependencies.
Verify actual Mathlib symbols from the pinned local checkout; any Lean sketches
in the attached handoff are conceptual and NOT guaranteed to compile.

REQUIRED PLANNING OUTPUT
Return a structured plan with these headings:
1. Repository snapshot and reproducible validation evidence.
2. Current implementation status (verified / partially verified / draft /
   not found / inconsistent) with file paths and Lean declarations.
3. Formal theorem dependency DAG and mathematically minimal carriers.
4. List of source-versus-implementation discrepancies and risk severity.
5. One small proposed module per implementation gate; imports and interfaces.
6. Each gate's theorem statements, assumptions, tests, and acceptance proof.
7. Counterexamples and adversarial tests to prevent fake green results.
8. Independent research tasks: charge zero modes, finite-CAR quench bridge,
   lattice dispersion, finite-cutoff cone bounds, GGE asymptotics.
9. Decisions required before code: give recommended defaults and alternatives.
10. Next authorized smallest implementation task (proposal only; no edits).

If file creation is authorized later, place the planning document in the
repository's existing notes/docs convention, rather than assuming new paths.
Report any missing input and continue with supported partial findings;
never silently invent unavailable project artifacts.

REFERENCE POLICY
Use the attached manuscript for internal project definitions, and cite only
bibliographically verified peer-reviewed literature/books for physical claims.
The published Cazalilla PRL title differs from the associated arXiv preprint
title: do not conflate them. Do not fabricate exact Mathlib API names or theorem
availability; inspect the installed version directly.
```

---

## K. Next-phase research program beyond the first formalization

The later research should be organized into **four independent result classes** instead of one oversized theorem.

**K1. Finite-CAR dynamical comparison:** For a finite family of current words and specified initial sea, formulate an intertwining/matrix-element defect between the abstract \(\omega_0\circ\tau_n\) and a chosen genuine finite-CAR Hamiltonian quench. The paper's existing protected-word theorem is a starting point for *static* word equality; dynamical powers and charge-changing vertices demand their own excursion bookkeeping. A useful first target is a bounded-order perturbative comparison, not an exact all-time vertex identity.

**K2. Exact algebraic dispersive normal form:** Reconcile the Chapters 16 and 18 Hamiltonian prefactors and diagonalize the corrected 2-by-2 modewise quadratic forms. Prove positivity/stability conditions. Characterize when the corrected phases form a finite cyclic subgroup; otherwise parameterize general unit phases algebraically and introduce analytic evolution only in a later layer.

**K3. Quantitative propagation:** Decide whether to prove a microscopic Lieb–Robinson-type estimate for the local finite-CAR model or a Fourier-tail bound for effective boson fields. These are different theorems, with different carriers and locality assumptions. State a theorem in terms of an explicit norm and cutoff regime rather than an unqualified causal horizon.

**K4. Thermodynamic GGE:** Define a system sequence \(L\to\infty\), mode cutoff \(M(L)\), physical separation/time scaling and a candidate quasifree stationary state. Prove a modewise covariance limit or a time-averaged statement first. Only then study nonlinear vertex expectation values and whether the limit interchanges with formal-series specialization.

**Stopping rule:** Do not launch K1–K4 implementation until the exact finite quench covariance and its formal-series interpretation pass the earlier proof gates.

---

## L. Verified peer-reviewed references

The following metadata were checked against journal/publisher records. Manuscript chapter/page references above are to the **user-supplied draft**, not peer-reviewed publication claims.

1. **M. A. Cazalilla**, “Effect of Suddenly Turning on Interactions in the Luttinger Model,” *Physical Review Letters* **97**, 156403 (2006). DOI: [10.1103/PhysRevLett.97.156403](https://doi.org/10.1103/PhysRevLett.97.156403). The associated preprint is **arXiv:cond-mat/0606236**, whose listed title is **“The Luttinger model following a sudden interaction switch-on”**; do not mistake the preprint title for the published title.
2. **A. Iucci and M. A. Cazalilla**, “Quantum quench dynamics of the Luttinger model,” *Physical Review A* **80**, 063619 (2009). DOI: [10.1103/PhysRevA.80.063619](https://doi.org/10.1103/PhysRevA.80.063619).
3. **E. H. Lieb and D. W. Robinson**, “The finite group velocity of quantum spin systems,” *Communications in Mathematical Physics* **28**, 251–257 (1972). DOI: [10.1007/BF01645779](https://doi.org/10.1007/BF01645779). Locality hypotheses must be checked before invoking it for a momentum-truncated model.

### Manuscript locations relevant to the audit

- Chapter 16, §§16.3–16.5 (printed pp. 105–108): exact dispersion and error operator.
- Chapter 18, §§18.1–18.6 (printed pp. 117–120): Bogoliubov transformation and budget-action limitation.
- Chapter 19, §§19.2–19.5 (printed pp. 123–133): polynomial state, contractions, finite-CAR bridge and Phase-C/Core status note.
- Chapter 20.1 (printed pp. 135–144): finite-CAR charge-product residuals and documented Core status.
- Chapter 20.2 (printed pp. 145–155): formal vertices and coefficientwise correlations, explicitly draft status.
- Chapter 20.3 (printed pp. 155–164): abstract duality and explicit warning against finite-CAR identification.
- Appendix E (printed pp. 218–220): oscillator state/formal vertices, including the stale status paragraph and compression counterexample.

---

## Final recommendation and first agent deliverable

**Authorize Antigravity to audit and plan, not to start coding.** The first response should be a repository-grounded theorem/status matrix and a detailed gate-by-gate implementation proposal that reuses the existing Chapter 19 machinery. Only after the exact types, charge conventions, and Chapter 20.2 prerequisites have been verified should a small `CCRAction` implementation be authorized.

The mathematical result driving this entire phase is the exact finite-mode identity

\[
\Phi_J(d,n)=A_JD_M(d)+\frac{B_J}{2}
[D_M(d+2n)+D_M(d-2n)-2D_M(2n)].
\]

It has a limited, precise scope and directly supports both oscillator recurrence and coefficientwise CDW/SC quench correlations. Claims of full finite-CAR dynamical equivalence, causal bounds, and GGE limits must retain separate explicit proof obligations.
