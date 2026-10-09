# Notes review completion and Fourier readiness — 2026-10-09

## Decision and meaning of completion

The current Markdown source/suggestion reconciliation is complete for the specified finite and algebraic program. The remaining known revision actions have been applied or assigned an explicit research/analytic scope outside the unconditional implementation queue. **Chapters 1–2 are coherent with A01 and Chapter 3 and require no Lean source change. The next implementation card is A01/Chapter 3 Phase A.**

This closes a source-checking pass; it does not prove Chapters 3–21, guarantee that every later strategy will succeed, or certify a universal finite-band bosonization dictionary. Proof development may reveal new issues. [The adaptive roadmap](../adaptative_roadmap.md) records the Kanban board, dependency order, and dedicated issue-sprint procedure for discrepancies affecting multiple notes/files. Each chapter retains its A–B–C gates.

The scope includes all 21 chapter notes, A01–A10, their inline proof strategies and the external Chapter 1–3 suggestions. The earlier corpus review and revision were checkpointed in d3770c1/e570727; the main mathematical closures below entered the incoming documentation checkpoint 3ed134a. This follow-up reconciles active guidance, indexing, pipeline and final validation. Dated prior reviews remain provenance snapshots, with links to this current decision.

## Closed revision actions

| Area | Applied contract / revision | Location |
| --- | --- | --- |
| Fourier scalars | Field cancellation, separate nonzero-L inverse assumption, nonzero root for integer powers, representative independence, existing positive Nyquist convention. | A01 / Chapter 3 / external Fourier guide. |
| Fourier carriers and APIs | Distinct function S/T carriers transported with `WithLp.linearEquiv`; normalized U uses Euclidean S₂/T₂. Replaced nonexistent trigonometric helper names with checked APIs. | Same three references. |
| Normal ordering | Explicit sea quasiparticle q/q† convention and stable raw-word ordering. Evaluation and contraction expansion are separate linear constructions. | A02 / A07 / Chapter 17. |
| Raw quartic reduction | Exact coincident-index Wick identity and `H4,raw = H4,current − (g4/(2L)) Σ Q_M,ν`, with finite distance weights; no scalar-CCR margin needed. | Lemma 17.4a / A07. |
| Projected field verification | Conditional cyclic-span criterion with the same typed residual family for both maps. Full projected Fourier-hole ground vector; no independence or zero-residual assumption needed. | Theorem 14.5 / A05. |
| Finite products | Explicit source/intermediate/target budgets and retained `p_t A (I-P_m) B i_s` residual. Singlet terms included into their distinct orthogonal target sectors. | Chapters 20–21 / A03. |
| State existence | Star-compatible CCR quotient represented on weighted polynomials, positive vacuum expectation, real Bogoliubov automorphism and inverse-pullback state. | A08 / Chapter 19. |
| Charge/state extension | Generated adjointable charge algebra on finite-support ℤ² kets, fixed integer Klein signs, tensor representation and charge-indexed positive state. | A08 / Chapter 20. |
| Vertex scope | Specified Weyl-type formal vertices, central self-adjoint t, coefficientwise evaluator into ℂ[[t]], opposite chirality orientations, exact phases and C₀=C₀′=1. | A08 / Chapter 20. |
| Duality | Explicit generator/charge map, `F_L↦−F_L†`, adjoint vertex exchange with ζ^x, chemically adjusted Hamiltonian and charge-indexed state transport. | A09 / Chapter 20. |
| Spin and leakage | Exchange-symmetric quadratic blocks, explicit unequal-velocity condition, two typed singlet channels, general Umklapp sign −1 and coefficient `−g_U/L²`. | A09 / Chapter 21. |
| Guidance and status | P01–P15 current execution entries reconciled; obsolete solved correction paragraphs removed from committed auxiliary history; README, TOC and appendix index point to current scope and pipeline. | Proof revision guide / indexes / adaptive roadmap. |

## Explicit exclusions and future obligations

The numerical-margin-only equality between the finite fermion field and the candidate (14.4) remains a **research candidate**, not an unconditional Phase A theorem. All-species completeness and mode coverage are necessary checks; they do not replace proof of the full ground-vector equality and actual intertwining residuals. The approved useful theorem is the conditional cyclic-span criterion. Applying it to the candidate is a later proof task that may justify an issue sprint.

Chapter 20 now uses an explicitly chosen **formal Weyl-type model**. This changes the model relative to older normal-ordered Mattis–Mandelstam vertex expressions; it is not a proof that those former expressions had the displayed correlators. At equal points its normalization is L⁻², unlike the example finite CAR correlator at L=4 (1/4). Comparison with finite CAR, convergence/substitution t=1, compactification/T-duality interpretation and continuum asymptotics require separate constructions. They are outside this source-checking closure and cannot be imported as facts into a finite theorem.

Every later construction still needs complete Lean definitions, correctly elaborated instances and its stated proofs. In particular the noncommutative series carrier and quotient/state implementation must be checked before their interfaces are locked; a familiar commutative exponential API is not assumed applicable. Frozen Core must not be changed to accommodate these future choices.

## Existing Core compatibility

| Frozen infrastructure | Use by the next notes | Result |
| --- | --- | --- |
| `Ch01.Lattice L = ZMod L` and `band_projection_bijective L hL` | Derive `Band L ≃ ZMod L` via `Equiv.ofBijective`, reindex characters and sums. | Compatible; reuse the existing band and finite instances. |
| Positive Nyquist representative and transported negation | Character evaluation under ordinary integer negative labels. | Compatible; prove representative independence. At L=4, representative(−2)=+2 and bandNeg(+2)=+2. |
| Positivity hL:0<L versus `[NeZero L]` | Modular finite APIs / DFT. | Derive the local instance or positivity bridge explicitly. Scalar `(L:K)≠0` remains separate. |
| Bundled `Ch02.shift`, inverseShift, forwardDiff, backwardDiff, laplacian | Character eigenvalues and Hilbert transport. | Signs match ζ^k−1, 1−ζ^(−k), ζ^k+ζ^(−k)−2. |
| `Ch02.sum_by_parts` | Periodic finite sum manipulations. | Compatible bilinear identity; a complex adjoint result needs conjugation and the Euclidean counting pairing. |
| Polynomial umbral identities / integer Heisenberg pair | Separate algebraic model. | Compatible; not transplanted to finite cyclic CCR. |
| Core companion notebooks | Complete-source correspondence. | Both current blocks match their Lean sources. |

The `identity_apply` warning is already resolved by `omit` in frozen Chapter 2. Fresh direct compilation has no warnings; no linter suppression or threshold change is needed.

## Evidence and its limits

- CI against the committed baseline 3ed134a passed: 69 guard tests, strict freeze of 52 lemma statements and 54 non-lemma commands, complete-source freeze of two Core files, and both Lean library builds. The earlier same-pass run against e570727 also passed. Guards verify preservation, not mathematical truth.
- Fresh direct compilation of each Core chapter with `lake env lean -DwarningAsError=true <source>` exited 0 with empty diagnostics.
- Axiom auditing of freshly parsed complete sources covered all 20 Chapter 1 and 32 Chapter 2 lemmas. Dependencies use only subsets of `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` was found.
- Focused stdin probes checked band equivalence, Euclidean/function transport, transported shifts, the L=4 Nyquist examples and replacement exponential/trigonometric APIs. These validate the specific interfaces, not the new Chapter 3 theorems.
- The complete word/span/cyclicity proof of Theorem 14.5's generic criterion compiled with `autoImplicit=false` and `warningAsError=true` over a semiring and additive commutative group modules. Its three helpers depend on `propext` and `Quot.sound`. This scratch proof is evidence for the criterion, not a new repository Lean declaration or a proof of its physical specialization.
- Independent exact arithmetic checks passed 10,072 sea-Wick quartic word identities and 624 raw/current/Q operator columns for h=1..3, including M=0 and cutoffs beyond the band. The one-body formula still needs its general Lean proof; these finite checks are useful consistency evidence.
- Exact basis-coefficient checks passed 3,240 Klein-duality cases for h=1..4 and integer charges −4..4, and the Umklapp witness sign for h=1..20. The general sign calculation is recorded in Lemma 21.8; finite checks alone do not prove all h.
- The repository's saved reference-counterexample script passed, preserving witnesses that explain retired claims. All 18 protected Lean/spec/script/toolchain files matched their starting SHA-256 values. No Lean implementation or freeze baseline changed.
- Markdown links and whitespace were checked for the current reference/guidance set. Native MCP/LSP transport was not exercised in this pass; compiler evidence is reported separately.

## Task, skill and agent attribution

The parent used the local formalizer skill for scope, source reconciliation, compiler evidence and frozen-interface discipline, applied the Markdown changes, reconciled the indexes/pipeline and ran independent exact checks. `proof_revision_plan` audited Core/Fourier compatibility and compiled the generic cyclic criterion; `revision_c01_c07` derived the full quartic correction and conditional field plan; `revision_c08_c13` derived the constructed state/formal-vertex/duality and spin contracts. These were read-only subtasks of this chat, not an installed scheduler or new user threads.

The additional final reread requests to the last two agents could not run because of tool-reported usage limits. The parent performed the final source reconciliation and independent exact computations; this record does not claim those two agents independently audited the final edited text.

## Next authorized implementation sequence

1. Read A01 and the revised Fourier guide; derive the band/residue equivalence and character/sign bridges from frozen Core.
2. Draft complete Chapter 3 staging definitions and one-sorry lemma statements in dependency order: character laws and nontriviality, sums/orthogonality, unscaled S/T, inverse, Euclidean transport/normalization, then adjoint/isometry and Chapter 2 eigenvalues. Reuse the installed canonical complex `ZMod.dft` where its kernel matches; keep a generic field layer small and justified by downstream needs.
3. Mirror exact signatures, imports, local instances, corner cases L=1/Nyquist, witness obligations and adopted/rejected suggestions in the companion notebook. Define normalized U as a linear map until isometry proof fields are available.
4. Build and present Phase A for review. Freeze only the approved interface, then enter Phase B within authorized scope; complete the ordinary audit/promotion in Phase C.
5. Read later appendices alongside their dependent chapters. If proof/compiler evidence exposes a shared error, follow the adaptive issue-sprint procedure and update the affected notes before resuming.

This documentation checkpoint does not start Chapter 3 Lean work, freeze its interface, or authorize its proofs.
