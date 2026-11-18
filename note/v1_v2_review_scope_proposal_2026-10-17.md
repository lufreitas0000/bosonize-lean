# Proposed version 1 / version 2 disposition of the new reviews

Date: 2026-10-17. Review source baseline: `814385a8832489d209d27b64ba670a3c696dde6c`.
Status: local research-scope proposal for discussion; the previously authorized
manuscript-status corrections are applied separately. No new mathematical scope is accepted,
no Lean implementation is started, and no worker is dispatched. The seven
supplied review files are unchanged. Subsequent commit `728987b` applies only
the three manuscript status corrections described below. Publication run
`39054320100` passed, and the latest published PDF receipt matches `728987b` exactly. This proposal does not amend frozen Core.

## Recommendation

Version 1 should finish the standalone 1+1D development through its agreed
Chapter 20 bridge and finite CH21, with source coverage and release audits.
Adopt the reviews' corrections to the meaning of existing results now. Include
small additional proof packages only where they are necessary to close that
existing scope. Defer the five new application programs to a separately prioritized
version-2 research backlog after the finiteQMB-based refactor.

Finite-dimensional or algebraic does not, by itself, make a proposed extension
a version-1 requirement. Conversely, a discovered correctness problem cannot
be deferred while continuing to claim the affected result in version 1.

Version 2 should first preserve the accepted version-1 mathematics on top of
reviewed finiteQMB interfaces. New entanglement, impurity, quench, RG and wire
applications should not be mixed into the acceptance criterion for that refactor.
Continuum limits and full QED3 are further research proposals, not guaranteed
deliverables of version 2.

## Inputs read

All seven files under `notes/review/` were read:

| Review or prompt | Role in this proposal |
| --- | --- |
| [Entanglement review](../notes/review/Bosonize_Lean_Entanglement_Next_Phase_Review_and_Antigravity_Plan.md) | State restriction, compression, charge zero modes and the boundary between oscillator Gaussianity and CAR quasi-free states. |
| [Refermionization review](../notes/review/Bosonize_Lean_Refermionization_Review_and_Agent_Plan.md) | Charge/parity typing, twisted fields, compressed CAR defects, special-point impurity and spectral-observable proposals. |
| [RG review](../notes/review/Bosonize_Lean_RG_Review_and_Antigravity_Planning_Packet_2026-10-17.md) | Restricted shell carriers, nonresonance, charge-changing virtual paths, buffers and perturbative scope. |
| [Quench review](../notes/review/Bosonize_Lean_Quench_Project_Review_and_Antigravity_Handoff.md) | Time/series distinction, budget invariance, Hamiltonian conventions and separate dynamical research targets. |
| [Coupled-wire review](../notes/review/Bosonize_Lean_Coupled_Wires_Review_and_Agent_Brief_2026-10-17.md) | Typed Klein arrows, integral charge maps, protected words and the additional geometry/gauge scope. |
| [Refermionization handoff](../notes/review/Antigravity_Bosonize_Refermionization_Planning_Prompt.md) | A planning prompt, not another independent source of mathematical evidence. |
| [General strategy handoff](../notes/review/Google_Antigravity_Bosonize_Lean_Strategy_Prompt.txt) | The coupled-wire planning brief repeated as an operator prompt; no authority to dispatch an agent. |

These are five substantive reviews and two handoff prompts. Most are manuscript
reviews rather than live repository audits. The RG review inspected an earlier
GitHub revision, `0d185df`; its book-inclusion findings are superseded by the
current main tree. Bibliographies and pseudocode are not wholesale certified by
this disposition. A few primary literature records were checked, not every
formula or reference in every review.

## Version 1: corrections to adopt in the existing scope

### V1-1 — Finish status and claim-to-source reconciliation

The README, roadmap, manuscript manifests, source indexes, workflow guides and
workspace allocation have been reconciled in commits `e6bf093` and `814385a`.
The seven active CH20–21 section entries are now checked by publication CI.
The published receipt for run `39053724508` matches `814385a` exactly.

The new reviews exposed remaining *manuscript* status prose. The narrow status
corrections below have now been applied under the earlier reconciliation request:

- `notes/latex/appendices/app_a08_states_correlations.tex:6–13` previously described
  CH19 as staging/Phase-B only and denied Core certification of an abstract
  state. A08/CH19's actual reviewed scope is promoted. Correct that historical
  status while preserving the open charge/formal-vertex and finite-CAR comparisons.
- The same appendix's closing status at the reviewed lines 196–200 now refers to the
  accepted A08/CH19 scope and the remaining extension obligations separately.
- Section 20.2's closing paragraph now distinguishes its draft mathematical
  construction from the accepted finite CH20 package; the phrase “as with
  Section 20.1” currently blurs editorial review and Lean acceptance.
- Section 20.3's closing text now says that its *formal algebra/state duality*
  lacks corresponding accepted Lean coverage. It should not imply that no
  Chapter 20 Core module exists, or that the already included section awaits
  first inclusion in the master.

Only those status paragraphs were changed; mathematical definitions, displayed
formulas and proofs were preserved. The earlier status commit changed no TeX
bodies; the follow-up correction is separate from accepting any research proposal.

### V1-2 — Complete Chapter 20's theoretical strategy first

Retain the six [independent theoretical prompts](../docs/plans/ch20-theory/README.md).
The reviews strengthen the reasons for that gate; they do not solve the open
questions by proposing new applications.

Proposed Chapter 20 completion targets are:

1. A complete ordered Wick/moment argument for the actual positive oscillator
   functional, without assuming it is already a finite CAR state.
2. Charge/Klein, zero-mode, formal-series and normalization arguments for the
   proposed formal vertices and their coefficientwise correlators.
3. A precise algebra-and-state duality with source phases and adjoints. Treat
   finite-CAR unitary implementation as a distinct question.
4. A defensible finite comparison: exact selected matrix elements, a restricted
   dictionary, a controlled residual, or a reviewed obstruction with a corrected
   target. Do not promise an unconditional field identity or interacting-state
   equivalence merely to call the chapter complete.

The user must settle the substantive completion scope after independent theory
responses are reconciled. A no-go result can close a research question with an
explicitly revised target; it cannot count as a proof of the original equality.

### V1-3 — Reuse compression and charge discipline, without a new framework

Carry into the existing CH20/CH21 work:

- Separate source, intermediate and target charge/budget carriers and true
  adjoints. Preserve all discarded-channel residuals.
- Distinguish a positive state/linear evaluator from a multiplicative algebra map.
- Keep current edge terms, input and right-suffix margins, source twist and Klein
  convention. Do not obtain global compressed CCR/CAR from ambient relations.
- Keep the charge/spin parity sublattice and the two singlet channels of CH21.
  They do not establish a tensor factorization into unrestricted charge/spin spaces.
- Use existing Ch06Ext boundary twists and Ch13 Klein maps. Do not introduce
  refermionization-specific charge coordinates or a new twist API into version 1
  unless a concrete CH20/CH21 obligation actually requires them.

A general compressed CAR defect is a reasonable *small helper candidate* if a
named accepted target needs it. A complete local-state/entanglement abstraction,
new generic word-certificate hierarchy or full completely-positive-map library
is not required just to restate the existing projection identity.

### V1-4 — A10/CH21: prove the application bridge or qualify the claim

This review finding is confirmed against the current source:

- `Bosonize/Core/A10DiscreteSchriefferWolff.lean:317` proves the ambient identity
  `lowShellProj + highShellProj = Ch14.projection h Ns K` for `K >= 1`.
- At line 237, `sw_compressed_bch_second_order` requires `P + Q = 1` on the
  carrier used in that theorem. The A10 companion explicitly preserves the
  distinction. No failure of the existing proof is established by this mismatch.

If version-1 CH21 claims an actual shell-reduction application, include the
small adapter/application theorem: restrict to the budget or use a justified
extension/complement, establish the partition and invariance conditions, and
retain any exterior-excursion term. The current theorem's parameters are
`A05.Operators σ h`; it is not already an arbitrary-Hilbert-space theorem that
can be instantiated on a different type by renaming its projectors.

For an Umklapp second-order application, also include reachable shifted species
charge sectors in the intermediate carrier. Prove the chosen outer buffer
contains the relevant virtual paths, or retain its complement. Keep shell
energy denominators and symmetrized SW denominators distinct.

If the agreed CH21 scope is only finite charge/current/leakage plus a description
of existing A10 support, label the unproved application precisely. Do not start
a generic decimation engine to fill an application not included in that scope.
This is a proposed scope decision before CH21 Phase A, not a silent deferral.

### V1-5 — Finish finite CH21 and the release audit

Retain the current finite plan: four-species conventions; raw charge/spin currents;
parity and quadratic block results with hypotheses; two singlet channels; actual
Umklapp charges; and a nonzero outward *spatial-sum* leakage witness.
Require the coefficient/sign/character derivation, not just a nonzero total
Hamiltonian action. Leakage does not establish an RG flow, Mott gap or phase diagram.

Close the agreed theorem/support set through A–B–C, source coverage, a full
dependency/axiom audit and a reproducible release. Any source section needed
for the declared version-1 coverage remains a recorded obligation: moving an
application below cannot silently erase a previously required literature claim.
If a narrower first-version coverage statement is adopted, say so explicitly.

## Version 2: defer the new programs, not the correctness requirements

| Review | Carry into version 1 | Defer to the version-2 research backlog after refactoring |
| --- | --- | --- |
| Entanglement | Correct state-carrier claims, compression semantics, zero-mode/wrap qualifications and any misuse of “quasi-free” or “relative entropy” in existing prose. | Full/even local-algebra state interfaces; partial trace and spatial factorization; local charge polynomials; replica/charged moments; quasi-free determinant benchmarks; modular/relative-entropy development. |
| Refermionization | Charge directions, finite Klein endpoints, twists, ordered field candidates and compression defects needed for CH20/CH21. | The special `g=1/2` impurity program; new relative-charge fibers; parity Majorana; resonant-level equivalence; Green functions and finite TDOS spectral measures. |
| RG | A10 application-carrier audit; charge-changing intermediate paths and buffers only where the accepted CH21 target needs them; no exact-RG overclaim. | General retention/decimation engine; independent mode elimination; Feshbach library; discrete OPE application; operator-basis coupling extraction and quantitative RG approximation. |
| Quench | Correct distinctions between budget action and invariance, bare/pairing Hamiltonians, formal parameter and physical time wherever the existing exposition discusses them. | Even the initial finite-clock CCR action is a new dynamics application: phase automorphisms, covariance, formal quench vertices, recurrence classification, finite-CAR dynamical comparisons and dispersion re-diagonalization. |
| Coupled wires | Reuse existing charge cocycle, typed Klein and word-margin discipline; correct any existing physical-duality overclaim. | Alternating open wire geometry; integral D matrix and transported cocycle; periodic seam/holonomy; inter-wire operators; gauge-link/constraint models; Dirac/QED3 comparison. |

The local-charge polynomial and finite-clock quench are mathematically bounded
first increments *within their own new programs*. Their simplicity is not a
reason to make them prerequisites for standalone version-1 completion.

## Suggested version-2 staging

1. **V2-A — Refactor with preserved results.** Audit available finiteQMB interfaces;
   choose which finite CAR/Fock, grading, projections, states and spectral pieces
   are suitable. Supply a migration/result map and prove the adapters. Preserve
   bosonization-specific current, charge, oscillator and vertex layers above it.
   Do not assume finiteQMB already supplies all needed APIs or matches the same
   occupation ordering and energy conventions.
2. **V2-B — Choose one application.** A finite physical-state/local-charge and
   entanglement benchmark would exercise the reusable finiteQMB foundation.
   The abstract finite-clock quench is another bounded option once the formal
   oscillator/vertex layer is accepted. Choose by scientific priority after
   refactor acceptance, rather than start both now.
3. **V2-C — Larger applications by separate scope.** Refermionization/impurity,
   controlled decimation and coupled wires need their own model choices and
   bridge theorems. This is a backlog, not a commitment to complete all three.
4. **Later analytic research.** Continuum entropy, KT limits, thermodynamic TDOS,
   GGE convergence, quantitative causal estimates and full QED3/anomaly claims
   need explicit model sequences, topologies and estimates. Do not use them as
   mandatory acceptance criteria for the refactor or infer them from finite algebra.

## Corrections needed before using the reviews as specifications

- The RG review's old GitHub book/provenance discrepancy is resolved by current
  main and its exact-commit published receipt. Its A10 carrier finding remains relevant.
- The refermionization review's illustrative assignment of raising/lowering to
  `W_+`/`W_-` does not match current CH14: `wPlus` lowers; `wMinus` is the signed
  raising phase; `(wPlus)† = -wMinus`. Copy the exact source definitions and
  product order, not the report's illustrative notation.
- The entanglement report's state-lifting formula is legitimate for a genuine
  budget state, but it does not construct the missing oscillator-to-CAR comparison.
  Its proposal to implement charge polynomials first belongs to that extension,
  not automatically to the canonical release.
- A full ordered-word/free-state comparison appearing in manuscript-based reviews
  must be mapped to an actual theorem. The existing scalar zero-squeeze kernel
  comparison is not evidence for every word or the interacting state.
- Do not adopt the sketches' suggested structures or APIs until checked locally.
  Legitimate kernel proofs using `decide`, classical axioms allowed by the project,
  or trivial base cases are not invalid merely because a handoff bans “fake green”
  tests. Audit the statement and dependencies rather than blacklist proof syntax.
- Names containing “Antigravity” are supplied prompt titles, not authorization
  to dispatch that backend or spend another provider's credits.

## Immediate next action

Keep implementation paused. Review the proposed version split; the remaining
identified manuscript status paragraphs have received a narrow correction. Then
collect the six independent Chapter 20 theory responses and reconcile their
claims, hypotheses, counterexamples and proposed completion targets. Decide the
minimal CH21 shell-application scope before freezing its interface. Do not run
the five extension roadmaps or the two handoff prompts as implementation jobs.

> **Portfolio Migration Note (2026-11-18):** Cross-repository Version 1 vs. Version 2 scheduling and next-project goals live in [`/home/lucas/Projects/HORIZON.md`](file:///home/lucas/Projects/HORIZON.md) and [`/home/lucas/Projects/docs/NEXT_PROJECTS_INCUBATOR.md`](file:///home/lucas/Projects/docs/NEXT_PROJECTS_INCUBATOR.md).
