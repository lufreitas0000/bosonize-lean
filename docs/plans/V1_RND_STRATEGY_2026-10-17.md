# Version 1 R&D strategy and version 2 backlog

> **Current status — 2026-10-25:** S1–S6 are locally accepted in their exact
> scopes. S6 completed the reviewed physical-field obstruction/residual package.
> The [remaining strategy](V1_REMAINING_STRATEGY_2026-10-25.md) supersedes
> old readiness/next-action wording below. S7/S8 selection and comprehensive
> source coverage remain open; historical proposals are not acceptance receipts.


Current execution note (2026-10-20): the user has authorized S6's full A–B–C
cycle and instructed the work to stop after S6. Historical planning and stop
snapshots below describe their dated authorization state; they are not the
current execution instruction. S6 is in Phase A review, with the first draft
returned for revision and no interface lock yet established. S7, S8, CH21,
finiteQMB integration, push and release are outside this authorization.

Date: 2026-10-17. Status: **proposed mathematical strategy and planned sprints**.
The user requested this synthesis and roadmap update. No new Lean interface,
proof acceptance, mathematical source correction or external dispatch occurs in
this planning task. The baseline is `728987b`; the accepted finite CH20 package
and CH19/A08 remain complete within their existing scope.

## What the six replies resolve and leave open

All six `review: ...` notes in `notes/review/` were read. Exact filenames,
SHA-256 hashes, sizes and question assignments are recorded in the
[input catalog](V1_REVIEW_INPUTS_2026-10-17.json). Raw replies remain local research
inputs; citations, pseudocode and proposed calculations are not proof receipts.

| Reply, with the common `review: ` prefix omitted | Main contribution | Proposed disposition |
| --- | --- | --- |
| Complete ordered Wick theorem for the dressed oscillator state | Pull-through recurrence and ordered pairings for the actual oscillator functional | V1-S1; use existing contextual CCR descent rather than assume Gaussianity |
| Formal CDW-SC vertex correlators | Charge words, formal Gaussian series and normal-ordering factors | V1-S2; coefficientwise result on the auxiliary charge/oscillator carrier |
| Formal charge-oscillator vertex correlators | Independent charge-phase/normalization audit of the same formal problem | V1-S2; reconcile conventions and check reported defects against current sources |
| Algebraic duality versus finite-CAR symmetry | Gauge-sensitive formal duality; separate finite particle-hole candidate and implementability obstruction | V1-S3 and conditional V1-S7; do not identify these two transformations |
| Finite Interacting States and Their Comparison with omega | Finite compressed ground states; moment obstruction; small interacting example | V1-S5; independent construction and selected comparisons |
| Controlled finite comparison for Chapter 20 | Bounded current-word transport, typed product residuals and comparison error decomposition | V1-S4 and V1-S6; require a concrete estimate as well as abstract identities |

These are **six replies to five distinct questions**. The two formal-correlator
replies both address prompt 02. There is no dedicated answer to
[prompt 03, the physical finite field dictionary](ch20-theory/03-finite-field-dictionary.md).
The comparison reply supplies useful partial constraints, but does not replace
that missing reply. The focused local analysis now exists in the
[V1-S0 package](v1-s0/README.md), and identifies a finite full-ground-image
obstruction to unconditional equality. It remains pending independent review;
the physical-field theory gate is open. The original
[six-question register](ch20-theory/README.md) remains the question baseline.

The central recommendation is to complete Chapter 20 with separate, precisely
typed results: an oscillator Wick theorem, formal correlators and state-family
duality; finite current comparisons on justified word domains; a separately
constructed finite interacting state; and physical comparison results or proved
obstructions with explicit residuals. An auxiliary formal identity cannot stand
in for a physical finite-CAR equality.

## Source checks and findings requiring reconciliation

1. **The oscillator algebra in Lean is a free algebra.** In
   [A08OscillatorStates](../../Bosonize/Core/A08OscillatorStates.lean), CCR
   relations descend through `omegaP` in arbitrary contexts. Use those theorems
   or the polynomial representation; do not assume literal CCR equalities in
   `OscAlgebra`, or install an unjustified global adjoint on polynomial endomorphisms.
2. **The reported appendix SC sign defect is absent in the current source.**
   [Appendix A08](../../notes/latex/appendices/app_a08_states_correlations.tex)
   currently has the positive exponent `(N_R+N_L)(y-x)`, agreeing with
   [Section 20.2](../../notes/latex/chapters/sections/20.2.tex). The reply's
   negative-exponent finding concerns its supplied snapshot. No sign repair is
   scheduled on that assertion alone; preserve the charge-word derivation as a
   future acceptance check.
3. **Klein gauge determines the displayed duality sign.** The simplified
   charge-shift convention in the replies and the manuscript's finite-sea
   convention require an explicit diagonal gauge adapter. Under the simplified
   convention a bare left-charge reflection gives an extra minus sign; a phased
   reflection can change it. Preserve the existing CH13 convention as the
   reference and derive the transport before choosing a formula.
4. **Two different dualities are proposed.** The formal map negates the right
   oscillator generators. The finite particle-hole candidate complements and
   reflects left occupations and negates nonzero left currents. Even if both
   candidates are proved, this does not make one an implementation of the other.
5. **Moment order and compression placement matter.** For nonzero squeeze,
   sufficiently high normally ordered moments of a natural finite lowering
   current vanish on a fixed total-energy budget, while the oscillator moment
   is positive. This is a promising obstruction to an all-moment identification.
   A reverse-ordered ambient word can leave the budget and return: merely
   exceeding the budget is not enough to infer its vanishing. Specify final
   versus intermediate compression and derive the actual nilpotence bound.
6. **A10 needs an application bridge if a shell application is claimed.**
   [A10DiscreteSchriefferWolff](../../Bosonize/Core/A10DiscreteSchriefferWolff.lean)
   proves `lowShellProj + highShellProj = projection` in the ambient space,
   whereas `sw_compressed_bch_second_order` assumes `P + Q = 1` on its carrier.
   That theorem is currently specialized to `A05.Operators`, not an arbitrary
   restricted carrier. This is an application obligation, not a demonstrated
   defect in the accepted theorem.

## Proposed sprint sequence for standalone version 1

The [adaptive roadmap](../../adaptative_roadmap.md) owns the current queue.
Every sprint below is **planned**, not accepted or underway as proof work.
S0 is the next theory/documentation sprint. Complete its specification decisions
and independent mathematical review before new canonical implementation.
Each resulting proof package follows A–B–C; a sprint is not automatically a new
Core module, and several can share one reviewed additive interface.
Use one primary package at a time. No elapsed-time estimates are promised.

### V1-S0 — Reconcile theory, conventions and completion scope

The requested [S0 artifact package](v1-s0/README.md) is complete: it contains the
[claim/convention ledger](v1-s0/claim-convention-ledger.md),
[prompt-03 analysis](v1-s0/physical-field-dictionary.md), and
[completion contract/dependency graph](v1-s0/completion-contract.md). The S0
theory gate remains open pending independent review and the user's substantive
scope decisions. S1 has not begun.

For the completed analysis, the recommended Chapter 20 route is to establish
separate formal oscillator results, exact finite-current comparisons on proved
word domains, a separately constructed finite interacting state, and typed
physical comparisons with explicit residuals or reviewed obstructions. Do not
infer physical field equality from formal Gaussian correlators or current
moments. Prompt 03's focused local counterexample is documented, not independently
reviewed. Preserve the source-coverage ledger as a release obligation.

The completed ledger records carrier, adjoint, state, ordering, source/target
charges, twists, mode range, total budget, exact margins, claims, counterexamples
and evidence gates for all six questions. The focused field analysis checks the
full ground-image coefficients, cyclicity and common-residual criterion for the
actual finite fields. Numerical margins alone are not the accepted
[CH14](../../Bosonize/Core/Ch14Mandelstam.lean) equality criterion.

**Exit:** independently reviewed claim ledger and theorem dependency graph;
concrete V1 completion scope distinguishing constructions, obstructions and
unresolved research; resolve substantive scope choices with the user. In
particular decide whether CH21 includes a genuine A10 shell application and
whether the distinct finite particle-hole construction is required. No lock
until exact targets and nonvacuous hypotheses are reviewed.

### V1-S1 — Ordered Wick theorem and moments

Start from the existing vacuum annihilation and contextual CCR lemmas. Prove a
pull-through recurrence for ordered products of homogeneous linear forms, then
the odd/even moments and ordered pairing theorem. Contractions are bilinear
and order-sensitive; positivity alone does not prove Gaussianity.

The proposed recurrence is
`omegaP(Z_1 ... Z_n) = sum_{j=2}^n Q(1,j) * omegaP(Z_2 ... omit Z_j ... Z_n)`,
where `Q(i,j)=omegaP(Z_i Z_j)` and the remaining factors retain their order.
For one centered form with variance `q`, derive
`omegaP(Z^(2*k)) = (2*k)!/(2^k*k!) * q^k` and vanishing odd moments.

**Exit:** recurrence, pairing/moment consequences and representative nonzero
examples; cover empty mode sets, empty products and zero variance.
Prefer the minimal recurrence to a new general normal-ordering framework.
Depends on S0 and the accepted A08 state.

### V1-S2 — Charge words and coefficientwise formal vertices

Build the auxiliary integer-charge/polynomial carrier and charge-word evaluation
needed by the chosen formulas. Derive the Klein gauge adapter, phase ordering,
Hermitian oscillator fields and same-channel commutation. Use S1 to derive the
formal Gaussian correlators with `g_D=(c-s)^2` and `g_S=(c+s)^2`.
Specify whether the chosen vertex is Weyl-type, bare-normal-ordered or
dressed-normal-ordered, and prove the corresponding prefactor.

**Exit:** coefficientwise correlators, charge selection and phase/normalization
checks. Keep `t` formal; no evaluation at `t=1`. The physical equal-point
normalization mismatch is retained as a comparison obstruction, not removed by
silently rescaling the physical field. Depends on S1 and S0 conventions.

### V1-S3 — Formal algebra and state-family duality

Derive the charge/oscillator automorphism in the canonical gauge, including
source phase, adjoint and involution. Prove covariance between parameter/charge
families, with squeeze sign reversed as appropriate. Do not substitute fixed-state
invariance for a transported-state identity.

**Exit:** exact vertex transformation and state-family covariance on the
formal carrier. No finite unitary implementation claim. Depends on S2.

### V1-S4 — Exact finite current-word comparison

Define the free-word substitution by actual finite currents and compare selected
matrix elements with the oscillator functional. Track each right suffix of a
word and its energy/mode margin. For the proposed exact comparison use the
inverse Bogoliubov substitution in the observable dictionary and evaluate in
the free finite sea. This compares dressed observables in a free state; it is
not an interacting finite ground-state theorem.

**Exit:** a parameterized word theorem with proved path hypotheses, nonempty
examples and explicit word-length dependence. The proposed coarse bound
`2*d*M + |N_nu| <= h` is a candidate to derive from actual Core hypotheses,
not a reviewed universal margin. Prove range/onto conditions for the Haldane
map; a mode-truncated embedding need not cover the whole budget. Depends on
S1 and existing finite-current/Haldane results; S2/S3 need not be dependencies.

### V1-S5 — Finite interacting state and limits of moment matching

Compress a specified Hermitian finite CAR Hamiltonian to a nonzero budget
carrier and construct a ground vector/state there. Prove normalization,
positivity and a precisely typed extension by compression. State explicitly
that a ground state of the compressed Hamiltonian need not be a ground state
of the ambient Hamiltonian. Use existing finite spectral tools where possible;
do not make a generic density-matrix framework a prerequisite.

Prove the proposed high-order moment obstruction for nonzero squeeze, with
actual current nilpotence and compression placement. Independently verify the
reply's eight-dimensional example (`h=8`, `M=2`, `K=2`, zero charges,
`v_F=1`, `g_4=32*pi`, `g_2=30*pi`) using the existing partition basis. Check
completeness, all matrix entries, ground energy and selected moments before
using its claimed mismatch; it is currently a candidate, not evidence.

**Exit:** a finite state construction, a proved obstruction with its precise
domain, and a nontrivial selected comparison or rigorously checked small model.
No assumption that the finite state equals `omegaP`. Depends on S0; S4 supports
the moment comparison but state existence itself is independent.

### V1-S6 — Physical fields, product residuals and concrete control

Current S6 status: active under the 2026-10-20 user authorization. Its focused
physical-field entry review is recorded in
[`docs/plans/v1-s6/entry-review.md`](v1-s6/entry-review.md). The typed product
decomposition and quantitative comparison are proved, independently reviewed,
and scoped-locked. The two concrete operator norm lower bounds and all later
acceptance gates remain open.

Use the dedicated field analysis to select an exact restricted dictionary, the
existing conditional cyclic/common-residual criterion, or a proved obstruction
and corrected finite comparison. Do not mark this obligation resolved merely
because formal correlators or current moments have been proved.

For products specify source, intermediate and target charge/budget spaces.
Separate the ambient compressed product from the product of compressed factors.
If the intermediate Haldane map is only an embedding, include its missing-range
term. Bound the residual and dictionary errors on the stated spaces, and state
the finite-state comparison error separately.

Maintain five named error obligations: intermediate projection, mode truncation,
normal-ordering normalization, state comparison, and dispersion. An error may
be zero only with proof; otherwise provide an explicit bound or explain why it
remains uncontrolled. Reuse the accepted nonzero discarded-channel witness as
a baseline and check any new coefficient before claiming a sharper result.

**Exit:** at least one nontrivial, explicit finite comparison with computed
bounds or a sharp obstruction, plus the general typed residual statement and
claim ledger. A triangle inequality with unknown error terms is insufficient
as quantitative physical control. Depends on the S0 field decision and the
relevant outputs of S4/S5; formal-vertex comparisons additionally depend on S2.

### V1-S7 — Distinct finite particle-hole symmetry, if retained in scope

Independently derive the candidate map with band reflection `k -> 1-k` and
left occupation complementation. Check CAR signs, unitarity, involution,
zero-mode constants, budget transport, species twists and the spatial phase of
the CDW/SC exchange. Check the claimed current-Hamiltonian transport including
the chemical-potential correction; prove transported finite-state statements
only for an explicitly chosen state family.

**Exit:** either a reviewed finite symmetry with its own conventions and
residual covariance, or a documented obstruction/scope decision. Test the
proposed obstruction to implementing the different formal right-current sign
flip separately. Neither candidate is an accepted result today. S0 decides
whether this is mandatory V1 work; S3 is the comparison reference, not an
identification theorem.

### V1-S8 — Minimal A10 application bridge, if required

If CH21 claims shell reduction, supply a justified restricted-carrier adapter
or an additive theorem with the actual projectors. Prove partition, invariance,
off-diagonal and generator hypotheses rather than reuse an ambient `P+Q=1`
where only the budget projection was proved. Include all reachable shifted
species-charge sectors for virtual Umklapp paths. Prove the outer-buffer
condition or retain its exterior residual; separate nonresonance and the
different energy denominators.

**Exit:** the stated finite second-order application with all hypotheses and
remainders, or an explicit reviewed exclusion from the V1 CH21 claim. No
general RG engine. Depends on the S0 scope decision and the exact CH21 carrier
designed in Phase A; it can be developed with that interface before CH21 B.

### V1-S9 — Finite Chapter 21 through A–B–C

Reconcile the [existing CH21 proposal](CH21_PARALLEL_WEB_RND.md) into one
reviewed interface. Preserve species order `(L_up,L_down,R_up,R_down)`, raw
charge/spin currents, the parity sublattice, both singlet channels and the
Umklapp charge shift `(+1,+1,-1,-1)`. Prove an outward nonzero **spatial-sum**
leakage coefficient with all character/sign factors, not merely nonzero total
Hamiltonian action. Independently derive the candidate `-g_U/L^2` coefficient
before freezing it. Include S8 only if the chosen CH21 scope requires it.

**Exit:** accepted finite CH21/support interface, proofs, promotion and pedagogy
with fresh guards/build/axiom/independent-review evidence. No thermodynamic
Mott gap, KT flow or unrestricted charge/spin tensor factorization follows.
Full physical field equality, all-moment interacting equivalence and a finite
implementation of the formal duality are not mathematical prerequisites for
these finite results. Reorder CH21 earlier if S0's dependency review supports
it, without discarding unresolved Chapter 20 coverage obligations.

### V1-S10 — Coverage, book and release closure

Complete R6–R9: source-to-claim/model/Lean/book ledger, required support,
placeholder/axiom/dependency/lock audits, reviewed pedagogy, reproducible PDF
and exact release-commit Git/CI evidence. Record every excluded or obstructed
claim and its corrected scope. Chapter 21 is the last planned chapter; its
completion does not by itself satisfy these release gates.

## Version 2 backlog after finiteQMB refactoring

These are future research options, not all promised deliverables of V2. No
finiteQMB dependency, interface redesign or migration starts during V1.

| Priority | Backlog | First bounded deliverable / gate |
| --- | --- | --- |
| V2-0, first | Complete refactor on reviewed finiteQMB modules | Inventory actual APIs; preserve every V1 theorem's assumptions/carrier/meaning in a migration map; prove adapters and rerun the full acceptance suite. Do not assume finiteQMB already supplies the needed foundations. |
| V2-1, then select one | Local states and entanglement | Full/even local algebra and state restriction, grading/factorization conditions, selected finite charge moments; entropy/modular theory needs its own scope. |
| V2-2, alternative first application | Finite dynamics/quench | Explicit phase automorphism, covariance and finite/formal-time distinction; later physical finite-CAR comparison. No automatic budget invariance. |
| V2-3 | Refermionization/impurity | Typed relative-charge fibers, parity/Klein/twist conventions and a specific special-point finite impurity equivalence before spectral/TDOS claims. |
| V2-4 | General shell/RG tools | Reusable retention, virtual-charge buffers, Feshbach/SW and quantitative approximation after the small V1 application is settled. |
| V2-5 | Coupled wires and gauge extensions | Open-wire geometry, integral charge map and transported cocycle first; periodic seams, gauge constraints and QED3 comparisons later. |

A general local-state/CP-map library, universal word-certificate engine and
broad operator framework belong with the refactor only when actual applications
justify them. Analytic vertex evaluation, continuum limits, thermodynamic gaps,
CFT/KT conclusions and full QED3 remain separately scoped research, not hidden
requirements of the refactor. Necessary correctness repairs to existing V1
claims are handled in V1 even if discovered by a future-application review.

## Evidence required before calling a sprint complete

For mathematical development: record exact source and interface hashes,
independent specification review, nonvacuous examples, hypothesis/margin checks,
compiler/placeholder/warning/axiom evidence, strict scoped locks, unchanged prior
Core hashes and Phase C pedagogy/migration review. Accept external replies as
proposals only. Preserve local private inputs and unrelated work. No raw review
publication or worker dispatch is implied by this plan.

The immediate action is **S0's claim/convention/dependency ledger and targeted
field-dictionary review**, followed by S1 once its theoretical target is reviewed
and implementation is resumed. This document completes planning; it does not
declare the theory gate passed.
