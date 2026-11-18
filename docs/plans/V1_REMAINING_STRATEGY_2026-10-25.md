# Standalone V1 remaining strategy after S6

Date: 2026-10-25. Baseline: `9fbbdce`. Status: **S6 verified locally;
remaining sequence proposed, not authorization to implement another sprint**.
No Lean source, definition, theorem or lock is changed by this review.

## Verified completion boundary

[S6 acceptance](v1-s6/phase-c-acceptance-2026-10-25.md) is corroborated by
[fresh revalidation](v1-s6/revalidation-2026-10-25/README.md): full local CI,
warning-as-error source compilation, complete 74-declaration namespace axiom
audit, strict 1317-statement/1394-command lock and 44-file Core guard all pass.
The source matches the final independent-review hash; all 43 prior Core files
are byte-preserved. The v2 manifest has only the reviewed S6 path migration
relative to the accepted Phase B manifest. Remote CI/publication was not checked.

S1–S6 provide distinct results, not one universal physical dictionary:

| Accepted package | What can be reused | What does not follow |
| --- | --- | --- |
| S1 | Ordered oscillator Wick theorem and factorial moments | Finite interacting CAR Gaussianity |
| S2 | Auxiliary charge/oscillator coefficientwise vertex correlators | Evaluation at `t=1` or identification with physical fields |
| S3 | Formal duality and indexed-functional transport | Finite particle-hole implementation or Hamiltonian covariance |
| S4 | Path/length-restricted transformed-observable moments in a free finite sea | All-degree fixed-regulator equality or interacting-state matching |
| S5 | Compressed interacting ground state, positivity, raw-moment obstruction and full eight-state example | Ambient ground-state minimality or equivalence with `omegaP` |
| S6 | Typed product/range residuals; factor-error estimate; fixed-candidate h3 lower bound `1/(2 sqrt(6))`; CDW residual lower bound `1/4` | Global field equality, optimality of either bound, state/dispersion approximation or complete literature coverage |

The field-dictionary question is no longer awaiting an initial mathematical
review: S6 reviewed and proved an obstruction for the fixed CH14 candidate at
the stated parameters. CH14's conditional cyclic/common-residual theorem is
preserved. Stronger or differently restricted dictionaries need their own scope.
The original S0 documents remain dated research provenance, not current proof status.

## Recommended next sequence

Do not automatically start S7 because its number follows S6. It is conditional
and is not a prerequisite for finite CH21. The main remaining chapter is CH21.

| Order | Work package | Concrete exit gate |
| --- | --- | --- |
| 0 — Release-contract and coverage decisions | Reconcile the remaining S0 choices with S1–S6 acceptance. Build a source/claim/model/Lean/book ledger early. | Every proposed V1 claim is required, explicitly excluded by an approved scope decision, or openly unresolved. Formal helper, obstruction and physical realization are distinct statuses. No blanket declaration that all S0 or source coverage is closed. |
| 1 — S9 Phase A: finite CH21 | Reconcile the existing CH21 proposal into one actual reviewed carrier/interface and companion. | Four species, raw-current conventions, parity lattice, separate singlet channels, actual Umklapp and outward spatial-sum witness, with nonvacuous hypotheses. Independently review exact declarations before locking. |
| 2 — S9 proof batches | Prove current/parity/quadratic support, charge shifts, singlet residuals and the actual spatial-sum leakage result in dependency order. | All transitive dependencies of each accepted proof are placeholder-free; independently verify the general leakage coefficient. Do not infer leakage from total Hamiltonian action alone. |
| 3 — Conditional S8 application | If retained, prove the narrow A10 application on the actual CH21 carrier using the proved CH21 support. Design the application during CH21 Phase A. | Correct projector partition on the chosen carrier, admissible generator/nonresonance hypotheses, shifted intermediate charges and proved buffer inclusion or retained exterior residual. |
| 4 — S9/support Phase C | Audit, promote and synchronize all required CH21/support targets. | Warning/placeholder/axiom/lock/build/review gates; actual source-to-result mapping. If S8 is required, its application is accepted before claiming complete CH21 coverage. |
| 5 — S10 closure | Whole-project formal audit, detailed book/source ledger, editorial/reference/layout checks and reproducible release evidence. | Declared scope and source coverage agree; unresolved exclusions explicit; publication/Git checks separately authorized. |

S8 and S9 must not form a circular dependency. Freeze their carrier and ownership
boundaries together if S8 is selected. Prove the minimal charge/budget helpers
first, then the application. Do not promote an S8 module importing unaccepted
staging or inheriting `sorryAx`; promote the reviewed dependency group in order
or keep it together until the complete required group is accepted.

Book synchronization can follow stable results. The source ledger should start
before the remaining proofs, so missing applications are found before release.
This ordering is a proposal; no provider call, reviewer dispatch or new proof
work is started by the current review.

## Scope decisions still requiring acceptance

| Item | Recommendation | Consequence and decision boundary |
| --- | --- | --- |
| S7: distinct finite particle-hole map | Keep optional; defer for the shortest canonical V1 route unless the declared source scope requires it. | V1 then makes no finite-unitary implementation claim. S3 formal duality remains intact. If retained, review band reflection, CAR signs, twists, charge/budget transport, Hamiltonian correction and state covariance independently. This recommendation is not an approved exclusion. |
| S8: actual A10/CH21 shell application | Retain a narrow application as the preferred coverage target, conditional on the reconciled CH21 design. | Existing A10 is not already the required restricted-carrier application. If excluded, name the missing application/coverage row and obtain an explicit narrower scope decision. No generic RG engine is required. |
| Chapter 20 completion claim | Accept the bounded S1–S6 constructions and fixed-candidate obstructions as the implemented bridge; retain all stated limitations. | This is not approval of all-moment physical matching, a global field dictionary, arbitrary interacting correlators or exhaustive source coverage. Claims exceeding that boundary remain separately listed. |
| Comprehensive requested-source coverage | Keep a separate mandatory ledger and acceptance gate. | A canonical 21-chapter release can be defined more narrowly only by explicit scope agreement. Moving a source topic to V2 does not itself satisfy the earlier comprehensive objective. |

The source inventory in [the coverage plan](../BOOK_AND_SOURCE_COVERAGE_PLAN.md)
still names unresolved investigations: Miranda's microscopic/XXZ applications;
vDS time/temperature/point-splitting and impurity/refermionization claims;
Sénéchal's non-Abelian/CFT/application/RG material; and the exact selected
Giamarchi sections. These are **coverage investigations**, not a claim that
every topic needs a literal finite analogue or belongs in the current proof queue.
Record verified finite counterparts, conditional comparisons, proved obstructions
and genuine missing scope separately. Finite obstructions must not be counted
as proofs of the source's continuum statement.

## Finite CH21 mathematical contract to reconcile

Use the [existing proposal](CH21_PARALLEL_WEB_RND.md) as input, not a locked API.
No CH21 staging interface exists at this review baseline.

- Species order: `(L_up,L_down,R_up,R_down)` in `Fin 4`, with explicit
  branch/cross-distinctness data and actual occupation order.
- Raw charge/spin currents are sums/differences without hidden `sqrt(2)`;
  restricted self-CCR coefficient is `2m`. Preserve both-species margins and
  edge terms outside them.
- Integer charge/spin labels lie in the parity sublattice; prove its inverse
  and an excluded pair. Do not claim unrestricted tensor factorization.
- The two singlet terms have different target sectors. Preserve their own
  middle/target budgets and both discarded-channel residuals, using S6 only
  when the exact maps/types and hypotheses fit.
- Umklapp is `c†_Lup c†_Ldown c_Rdown c_Rup`, shifting charges
  `(+1,+1,-1,-1)`. Retain actual adjoints and real coupling hypotheses.
- The proposed spatial-sum coefficient `-g_U/L^2`, with `L=2h`, must be
  independently derived from ordered CAR signs, unique occupation support and
  Fourier cancellation before freezing. An `h=2` example supports nonvacuity
  but must not replace a reviewed parameterized target.
- Prove outward charge-box/budget leakage, not merely nonzero total action.
  A compressed operator is a separate finite operator and may still be
  diagonalized. Neither shift nor leakage proves a Mott gap or KT flow.

Prefer reviewed batches and surgical proof-body integration to monolithic
whole-file retries. Prepare helper dependencies before locking expensive witness
proofs. If a theorem is false, record the counterexample and reviewed correction;
never preserve a desired result by hiding an assumption or changing a field.

## A10 application gate

The present A10 theorem is on `A05.Operators` and assumes `P+Q=1` on that
carrier. Its physical low/shell projections sum only to the ambient budget
projection. A generic renamed projector pair is insufficient.

Choose and review a minimal valid restriction/extension or additive application
theorem. Include reachable charge sectors for virtual Umklapp paths, true
adjoints, baseline/generator hypotheses and energy denominators. Distinguish a
finite second-order polynomial identity from an analytic exponential/remainder
bound. Preserve any exterior excursion rather than calling the budget invariant
without proof. No new universal decimation or RG framework is implied.

## S10 and version boundary

Release requires the required CH21/support acceptance, full-project dependency
and axiom audits, strict locks and reproducible builds, plus the source-to-claim
ledger and reviewed detailed book. The monograph's compiled inclusion is not
theorem coverage; local acceptance is not remote CI or publication. Final Git,
GitHub and published PDF receipts must identify the exact release revision.

V1 remains standalone. V2 starts with the separately scoped finiteQMB-based
refactor and theorem/assumption/carrier migration map. Entanglement, quench,
refermionization, general RG and coupled-wire proposals remain future application
choices, subject to the source-coverage decision above. No finiteQMB dependency
or migration work begins during this remaining V1 plan.

**Recommended immediate action:** approve the bounded release-contract choices
and prepare CH21 Phase A, with the S8 application boundary designed alongside
it if retained. S7 is optional; S1–S6 should not be restarted. This document
prepares that decision and implementation route, without granting future sprint
authorization or declaring the whole research program complete.
