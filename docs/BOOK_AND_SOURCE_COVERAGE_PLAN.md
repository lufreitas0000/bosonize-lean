# Detailed book and finite-regulator source coverage

Date: 2026-10-15. Status: planning only; no writing, proof work or external job
starts with this document. See the [adaptive roadmap](../adaptative_roadmap.md).

## Deliverables and present evidence

The primary publication is a detailed mathematical book, with all proofs written
out and prerequisites limited to undergraduate quantum mechanics and the linear
algebra/calculus taught alongside it. Introduce additional algebra, combinatorics,
operator language and finite AQFT explicitly when needed. More than 200 pages is
acceptable; clarity, completeness and logical dependence determine length.
Constructive means actual carriers, maps, hypotheses and witnesses are supplied;
it does not mean the Lean development avoids its permitted classical axioms.

A shorter academic review paper is a distinct backlog deliverable. Derive it later
from the accepted book and theorem map, rather than writing two versions in parallel.

Current status (2026-10-17): 34 frozen Core files cover CH01–20 within their reviewed scopes and implemented support. CH19/A08 (62 contracts) and finite CH20 (64 contracts) are Phase C complete. CH20b is the working label for the open Chapter 20 completion bridge, not another numbered chapter. CH21 has an R&D proposal but no accepted Lean interface. Polynomial CCR, formal-series results and finite CAR comparisons remain distinct. The book master includes CH01–21; manuscript inclusion does not imply proof acceptance.

Version 1 closes the agreed CH20 bridge, finite CH21 and release/coverage gates as a standalone project. Version 2 is a future complete refactor built on finiteQMB, after version 1 acceptance. The immediate scope is status reconciliation and theory prompts; no new Lean R&D starts now. The earlier page counts and draft inventories were planning snapshots, not current build measurements.

## Narrative and appendix integration

Preserve the 21-chapter subject spine while making the book flow continuously.
Lean file layout and book layout need not coincide. The migration concerns the
exposition, not renaming or rewriting frozen Core modules.

| Main-text development | Supporting material to integrate at first use |
| --- | --- |
| CH01–03: lattice, finite differences, Fourier | A01 roots, characters, normalization and orthogonality; motivate the asymmetric band and positive Nyquist mode. |
| CH04–06: occupation states, CAR, spatial fields, local net | A02 finite Hilbert spaces, signs, adjoints and bilinears; construct bases before invoking abstract Fock notation. Explain equal-time graded locality and its limits. |
| CH07–08: seas, sectors, budgets, bosonic occupations | A03 projections/filtered maps; A05 finite polynomial exponentials where needed. Distinguish ambient polynomial helpers from finite weighted slices. |
| CH09–12: currents, edge terms, partitions, completeness, energy | A04 partial shifts, exact edge formulas, word excursions, partition counting, Gram factors and Sugawara. Prove the dictionary before using it. |
| CH13–14: species, Klein maps, projected field identity | A05 signs, source/target budgets, nilpotency, adjoint reversal, full ground action and common residuals. Explain the conditional theorem as conditional. |
| CH15–16: dual fields and finite field Hamiltonians | A06 orientation, lattice kernels, finite sums, normal ordering, dispersion errors and nonzero witnesses. |
| CH17–18: interactions and Bogoliubov | A07 sea-Wick corrections, hopping versus chosen pairing, scalar matching and budget actions. Bring the relevant A10 shell/SW coefficient argument here, without equating it with exact RG. |
| CH19: states and correlations | A08 positivity, weighted pairings, contractions and finite compressed-state distinctions. Keep ordered and symmetrized correlators separate. |
| CH20: order parameters, vertices and duality | A08/A09 moments, charge maps, formal coefficients and exact projection residuals. Identify any missing finite-CAR comparison as an explicit obligation. |
| CH21: spin, charge, Cooper and Umklapp | A09 parity lattice, channel signs, actual charge shifts and nonzero leakage; remaining A10 finite shell/effective-theory context. |

Move a proof once, then cross-reference it. Do not retain the same mathematical
development in both main text and appendices. Only genuinely optional technical
tables or lengthy auxiliary calculations may remain at the back. Maintain an
old-section → new-section map and theorem label aliases during migration.
Keep source Markdown and companion records for provenance; do not reproduce
their administrative material as a second appendix inside the book.

Every chapter should motivate the problem, construct the objects, state the exact
finite result, give the complete mathematical proof, work a nontrivial example,
and explain the physical interpretation with its scope. Avoid a compulsory repeated
template when it would interrupt the narrative. Introduce required mathematics
before use; do not assume CFT, Lie theory, exterior algebra, RG, or AQFT background.
Replace tactic transcripts and unexplained code identifiers with mathematical prose.

## Finite-dimensional scope gate

Classify every statement by its actual carrier:

1. Finite CAR Hilbert space, finite matrix algebra, finite-mode/weighted-budget slice.
2. Exact restricted action or matrix element, with explicit source/target and margins.
3. Uncompressed polynomial CCR algebra or coefficientwise formal series used as a
   helper construction. These are algebraic, but generally not finite-dimensional.
4. Analytic, asymptotic, thermodynamic or continuum source claim requiring a separate
   finite counterpart, comparison/error theorem, or explicit non-applicability decision.

No finite-dimensional carrier can satisfy a nonzero scalar CCR globally. Compressed
operators retain boundary remainders. Do not silently substitute a formal Gaussian
state for a finite-CAR density matrix, evaluate formal series at one, infer a
spectral gap from a charge shift, or promote CH14's conditional field criterion
to unconditional field equality. Helper constructions may remain in the formal
library, but cannot alone close the requested finite-dimensional coverage row.

The goal is comprehensive coverage of the requested sources in the chosen regulated
sense. Where a literal source theorem has no exact finite version, write the precise
finite result or obstruction and distinguish it from the source's limiting claim.
If a new construction is needed, open a reviewed extension card; do not declare the
source covered merely because a related chapter exists.

## Literature coverage ledger: first required content artifact

Canonical local inputs are under the separate workspace repository
`References/references-transcripts/`: `miranda_2003`,
`von_delft_schoeller_1998`, `senechal_1999`, and selected `giamarchi_2004` sections.
Transcripts are navigational evidence, not infallible mathematical authorities;
check suspect equations against the printed source. No broad OCR or transcript
rewriting is part of the present plan.

Create one row per source section and then per substantive claim. Required fields:
source identity and section/page; exact claim; finite model/regulator; status;
Lean declaration(s), source hash and proof evidence; book section; remaining
hypotheses/residuals; interpretation/obstruction; owner and acceptance decision.
Statuses must separate verified finite theorem, conditional finite theorem,
formal helper only, prose derivation awaiting review, missing, and source claim
without the proposed exact finite counterpart. Empty entries never mean covered.

The following is a navigation inventory, not a completed source audit:

| Source | Existing chapter alignment | Required gap investigation |
| --- | --- | --- |
| Miranda I–XIV, XVI–XVIII and appendices | Foundations, dictionary, Klein/dual fields, spinless/spinful models, correlators and gaps context. | Microscopic Hubbard/Heisenberg-to-chiral-model bridge, exact versus linearized dynamics, all correlator and gap claims. |
| Miranda XV | XXZ application. | No automatic equivalence with the chosen pairing Hamiltonian. Inventory an exact finite spin/Jordan–Wigner/fermion treatment and any justified low-energy comparison. Existing separate XXZ numerical project is not a Lean proof. |
| vDS §§2–9, supporting appendices | Fields, oscillator Fock, identity, linear dispersion, Green functions and vertices. | Finite-size conventions, boundary twists, exact field comparison, time/temperature Green functions, point splitting and asymptotic/Coulomb-gas claims. |
| vDS §10 | Impurity in a TLL / finite-size refermionization. | A distinct missing-coverage candidate; identify the finite impurity Hamiltonian, observables and exact result before scheduling proof work. |
| Sénéchal §§1,3–6 | QM/QFT bridge, interacting electrons, Abelian construction and TLL. | Reconcile all rescalings, normalizations, state semantics and finite versus asymptotic correlators. |
| Sénéchal §2, §7, §8 and RG/OPE appendix | Conformal symmetry, non-Abelian bosonization, other applications, RG/OPE. | Not established by the current Abelian chapter map. Inventory finite symmetry/current analogues, spin-chain applications and obstructions to literal continuum claims; assess reviewed extension scope. |
| Selected Giamarchi | Existing guidance cites physical properties/correlations, LL parameters, order/duality, spin and commensurate/Umklapp context. | Freeze the selected section list explicitly; validate microscopic versus effective claims and finite spectra versus thermodynamic phase/gap statements. “Some Giamarchi” is not a claim of whole-book coverage. |

The canonical 21-chapter release and exhaustive source coverage are separate gates.
Finish stable canonical work first, while inventorying gaps early. If the ledger
requires extra finite constructions or book sections, propose their scope and
dependencies before declaring the larger original objective complete. Do not
silently put requested source topics into an optional backlog.

## Controlled book production

- Establish a reviewed notation/normalization specification before parallel writing.
  Resolve current density direction, nonwrapping definition, CCR sign and Sugawara
  product order discrepancies; record exceptions explicitly.
- A Jules task owns one chapter or small coherent section batch and fixed output
  paths. Its packet includes the exact source snapshot, final Lean contracts,
  companion mapping, prerequisite sections, notation version and review findings.
- Separate authorship of chapter text, shared notation and master-book integration.
  A second worker never edits the same chapter while its task is active.
- Jules compiles locally in its configured VM; deterministic independent CI builds
  the actual whole book, rejects undefined/duplicate labels, checks inclusion and
  notation policies, and retains the PDF/logs. Compilation is not semantic review.
- A reviewer through the OpenAI API checks source fidelity, each proof and its
  hypotheses, finite carrier, notation and completeness. Gemini API can supply
  an independent provider for critical cases under its own budget. Keep the
  required review/adjudication protocol; do not replace it with self-approval.
- Integrate accepted sections once. Preserve theorem anchors and references;
  review the assembled narrative and rendered pages, not just isolated chapters.
- Final acceptance requires complete proofs, claims mapped to evidence, all
  mandatory coverage rows closed, reproducible PDF, bibliography, clean Git and
  verified remote synchronization. More pages do not count as more verified results.

## Separate locality/RG/functional-integration project

Recommendation: separate future project, matching the user's preference. The two
private files are currently under ignored `notes/draft-lean-code/proposals/aqft_locality/`:
`finite_aqft_locality_rg_followup_proposal.md` and `func_integral.md`.
The proposal itself says it follows canonical completion; the second file is a
chat-derived functional-integration discussion. Neither is verified Core.

Its new questions concern locality after compression, interacting dynamics,
dressed filtrations, real-space coarse nets, Euclidean-time projection and
functional elimination. These are a separate research program with new models,
numerical experiments and proof targets. They are not prerequisites for completing
the canonical current/sector identities. Retain only necessary scope caveats in
the present book; do not import the proposal's full contents as another chapter.

Keep both private files untouched and unpublished during this planning turn. Later
prepare a checksum inventory and sanitized standalone proposal before a separate
repository/task is created. No private transcripts are copied into public docs.
If a concrete finding contradicts an existing canonical theorem or claimed
interpretation, triage that exact issue now through the normal issue-sprint process;
separation must not conceal a correctness defect.
