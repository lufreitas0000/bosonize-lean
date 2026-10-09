# Current revision verification and proof-guide execution — 2026-10-09

Latest status: [notes review completion](notes_review_completion_2026-10-09.md). This document records the earlier snapshot; its remaining-action entries are superseded where the completion ledger says resolved.
## Decision and scope

The attachment's conclusion that C01–C13 were all resolved and the notes formed a verified mathematical foundation is too strong. Several useful specification repairs were present, but the checkpoint still contained false vertex, quartic-reduction, duality, and leakage claims. Passing freeze guards establishes preservation of Lean interfaces/sources; it does not validate the mathematics in Markdown.

The incoming changes were committed first as **`d3770c1`**, `docs: checkpoint revised chapters, appendices, reviews, and formalizer guidance` (38 Markdown files). This preserves the chapters, appendices, historical review notes, and the prior formalizer update before obsolete draft material is retired. The ignore audit found no additional generated-file pattern needed. The attached log was compared with the actual source at this checkpoint, rather than accepted as proof evidence.

The present revision changes Markdown only. No project `.lean` file, guard script, freeze manifest, toolchain, or Lake dependency file is changed. It applies the [proof suggestion revision guide](proof_suggestions_revision_2026-10-09.md) to the external drafts and affected inline strategies, and corrects the mathematical contracts needed by those strategies. The older [confirmation review](revision_confirmation_2026-10-09.md) and [further-changes review](further_changes_review_2026-10-09.md) remain historical snapshot records.

## C01–C13 reconciliation

“Specified” below means the notes now state a coherent contract. It does not mean a later chapter has a Lean proof. Only Chapters 1–2 currently have proved, frozen Core implementations.

| Item | Checkpoint assessment | This Markdown revision |
| --- | --- | --- |
| C01 — Charge shift | Correct sign `[N̂,A]=qA` and target N+q present. | Retained; clarified integer charge/coordinate budget construction. |
| C02 — Gram induction | Correct right-remainder bound present, but its adjacent strategy still used a whole-prefix argument and reversed CCR sign. | Aligned the strategy with E≤K−n, m+n+E≤2K, and `[ρ_-m,ρ_m]=mI`. Proof remains a target. |
| C03 — Multispecies Klein | All-species construction and four-budget margins present. | Fixed strategy parenthesization of the phase; require joint partition labels with summed energy≤K. |
| C04 — Projected vertex | Not resolved: incompatible duplicate phases, missing mode coverage, incomplete all-species construction contract, ambient raising in the adjoint. | One phase convention, explicitly compressed adjoint, counterexamples, and a proposed full-vector/intertwining contract. Full equality remains pending. |
| C05 — Hopping/pairing | Two different models correctly distinguished. | Retained the chosen pairing model; do not claim a proved physical dictionary from the raw opposite-transfer interaction. |
| C06 — Ordering/zero modes | Chemical potential fixed, but quartic ordering unspecified and raw=current equality unjustified. | Define H4,current directly; withdraw the raw-quartic reduction pending full contractions. Retain the actual scalar coefficients. |
| C07 — Vacuum obstruction | Restricted CCR addressed the boundary issue, but ψ=0 was still admitted; strategy replaced the cross-branch transform with a same-branch shorthand. | Explicit ψ≠0 and actual cross-branch proof using one same-mode CCR. |
| C08 — Order phases | Correct phase characters, but the CDW table multiplied the wrong Klein signs. | Correct product `(+1)(−1)ζ⁻¹/4=i/4`; full projected products remain pending typed composition. |
| C09 — Abstract correlators | Distinct symbols alone did not construct a vertex carrier/completion or an extended positive state. | Label vertex/state/covariance targets pending; remove multiplicative state-map suggestion. |
| C10 — Duality | Scalar parameter involution present; claimed operator equivalence not constructed and direct CDW→SC contradicts charges. | Withdraw direct exchange; SC adjoint is only a candidate requiring generator/Klein phase calculation. |
| C11 — SW | Adapted basis and coupled-entry nonresonance repair coherent; 3×3 counterexample correct. | Use actual adjoint equations; the S1=0 rotation case is exact, without fictional higher-order rotation terms. |
| C12 — Leakage | Still false: nonzero total HUψ can be entirely inward. | Require nonzero outward component/outside projection; add proper-box counterexample and Proposed Lemma 21.8 witness family. |
| C13 — Status/index | “Verified”/“formalized” language promoted proposed chapters and undefined abstract maps. | TOC/appendix index now distinguish proved Core, proposed finite targets, pending abstract constructions, and physical context. |

## Concrete checks behind the corrections

### Vertex phases and mode coverage

Use the one-species ordered occupation basis in band `{-h+1,…,h}`, with source sea `S0={-h+1,…,0}`. All coefficients below factor out the common `1/√L`.

1. At h=4,L=8,M=1,N=0,Kin=0,Kout=1,x=0, the physical hole-at-−1 coefficient is +1. The discarded `(ζ^(±mx)−1)` phases vanish and give 0. The former margin is satisfied: 2+1+1=4. Restore positive-phase lowering and negative-phase raising from (14.1)–(14.2).
2. Restoring those phases does not suffice. At h=6,L=12,M=1,N=0,Kin=0,Kout=2,x=0, the physical hole-at-−2 coefficient is −1, while the mode-1 vertex gives −1/2. The former margin is satisfied: 2+2+1=5≤6. Both sectors satisfy the completeness margin; mode 2 is missing.

These coefficients were recomputed with exact occupation insert/erase signs and rational current powers. The proposed conservative coverage M≥max(Kin,Kout) still needs a proof of the entire projected ground vector and compatible intertwining. It is not presented as a sufficient theorem. Construction must hold for every species in both sectors. Adjoint factors act on the actual restricted/compressed carriers.

### Quartic ordering and actual zero-mode coefficients

Full sea-quasiparticle Wick ordering differs from subtracting a bilinear vacuum expectation or moving ordinary physical creators left. The ground state with NR=1,NL=0 contains only one sea quasiparticle, so a fully normal-ordered quartic has zero expectation. The former current expression instead gives g4/(2L). A raw-to-current theorem must compute all contractions and any one-body terms; relabeling it “exact” does not supply that calculation.

For the chosen quadratic current/pairing model, after μ=πvF/L the notes give

\[
E_0=\left(\frac{\pi v_F}{L}+\frac{g_4}{2L}\right)(N_R^2+N_L^2)+\frac{g_2}{L}N_RN_L.
\]

The attachment's additional factors `2πvF*g4/L` and `4πvF*g2/L` do not match the displayed coupling definitions and were not adopted. The chosen current model is explicit; its equivalence to a fully Wick-ordered raw model remains pending.

### Duality charge obstruction

For f(NR,NL)=(NR,−NL), CDW shift (+1,−1) maps to (+1,+1). SC has shift (−1,−1). A nonzero charge-preserving model equivalence cannot map those operators directly. SC† has compatible charge, but its sign/phase and ordering need calculation on actual generators. Scalar reciprocal parameters alone prove neither operator equivalence nor spectral/state transport.

### Leakage counterexample and useful witness

At h=2,L=4, use species order Ru,Rd,Lu,Ld and ascending momenta. Fill only −1 in each R species and every mode in each L species. Charges are (−1,−1,2,2), total excitation zero. Set absolute charge bounds (1,1,2,2) and K=16. This is a proper charge box: a fully filled R sector is excluded.

Outward OU vanishes because both L species are full. The adjoint sum has coefficient +gU/16 into R occupations {−1,0} and L occupations {−1,0,1}, charges (0,0,1,1). Exact enumeration gives 36 nonzero output configurations, all at those charges and excitation≤16. Thus HUψ≠0 but the whole image is inside. The old criterion fails.

A useful replacement witness avoids unnecessary CCR margins. For any h≥1, use four zero-charge seas, K=0 and all charge bounds zero. Add momentum 1 to each L species and remove 1−h from each R species. The target is outside, with charge shift (+1,+1,−1,−1). Its selected spatial exponent is −L, so the character sum equals L; four normalized Fourier factors and the HU prefactor give magnitude |gU|/L². The adjoint has the opposite charge and cannot cancel. For species order Lu,Ld,Ru,Rd, exact finite calculations at L=2,4,6 give respectively −gU/4, −gU/16, −gU/36. Proposed Lemma 21.8 requires proving the general coefficient; these finite checks are not that Lean proof.

### Schrieffer-Wolff check

The A10 3×3 matrices satisfy S1†=−S1, `[S1,H0]=−Voff`, and `P[S1,V]P=0` while PVQ≠0. Integer matrix multiplication independently confirmed the generator equation and cancellation. Retain only the forward implication from off-block vanishing. An anti-Hermitian finite matrix is not automatically nilpotent; the general second-order calculation is a coefficient identity modulo t³.

## Applying the proof suggestion guide

All 21 chapter strategies, A01–A10, and the three external suggestions were reviewed. Safe strategies in Chapters 5 and 7 were retained where appropriate; no edit is required merely to show coverage. Changes include:

- Correct carriers and index labels: finite Hilbert occupation basis, signed integer band shifts, positive boson weights, integer charge, and coordinate support budgets.
- Actual map construction through `Module.Basis.constr`, map equality through basis extensionality, and explicit derivation-to-linear-map coercion.
- Oriented CAR/CCR substitutions with fixed word order; scalar `ring`, additive `abel`, and `noncomm_ring` used only for their appropriate identities.
- A separate normal-symbol/word carrier, full contractions, Hermitian forms, and scalar factorial actions for nilpotent exponentials.
- Right-suffix margin checks and exact intermediate-projection remainders; inactive Sugawara modes handled by grading rather than an excessive all-mode bound.
- Positive state existence, vertex carrier extension, duality relations/inverses, and nonzero outside coefficients treated as obligations rather than assumptions inferred from notation.

The Chapter 1 and Chapter 2 replacement modules were retired into references to their frozen Core implementations. Their original contents remain committed at d3770c1. Chapter 3 was rewritten around characters → unscaled inversion → complex isometry. This is the recommended version of the two-step proposal: it avoids square roots in generic inversion while retaining the normalization required by counting-inner-product unitarity and canonical CAR.

## Framework philosophy, skills, and task attribution

Used [formalizer](../.agents/skills/formalizer/SKILL.md) and its [proof design reference](../.agents/skills/formalizer/references/proof_design.md). The work preserves frozen interfaces, does not silently weaken targets, and records false/underspecified statements before proof search. It separates source claims, exact finite calculations, compiler evidence, and proved declarations. There is no linter suppression or Phase B implementation in this revision.

| Role | Task | Scope |
| --- | --- | --- |
| Parent agent | Check attachment/source, checkpoint Git, revise Markdown, run compiler/exact checks, final commit | Sole writer |
| `revision_c01_c07` | Independent source and final-diff review of C01–C07 | Read only |
| `revision_c08_c13` | Independent source and final-diff review of C08–C13 | Read only |
| `proof_revision_plan` | All draft strategies and implementation-pattern review | Read only |

These are subagents used for this review, not claims of an implemented persistent scheduler or proof queue.

## Validation and remaining boundary

Installed Lean: `leanprover/lean4:v4.35.0-rc4`; Mathlib revision: `e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`.

- Direct `lake env lean --stdin` checked 17 API references and compiled four examples: basis construction evaluation, noncommutative square cancellation, exact projection remainder, and hyperbolic scalar-action inversion. Final run exited 0 without warnings or placeholders. An initially guessed `ZMod.invDFT` name was rejected; the guide uses `ZMod.dft.symm` and the checked `ZMod.invDFT_apply` lemma.
- Exact finite CAR/current calculations checked both vertex obstructions, the proper-box leakage counterexample, and three outward witness instances. Integer SW matrix calculations checked the displayed counterexample.
- Strict stub guard: 52 statements and 54 commands preserved. Core guard: 2 complete Core files preserved.
- Protected-file SHA-256 comparison and final Git diff checks establish that this revision is Markdown only. Native Lean MCP/LSP validation and full project rebuild are not claimed; no Lean implementation changed.

The proof suggestions can now be used as revised design guidance. Do not freeze the pending full vertex equality, raw-quartic reduction, extended abstract vertex/state formulas, or operator duality from these sketches alone. Resolve their stated contracts in the ordinary Phase A review before implementing their Lean statements/proofs. Independent earlier chapters can proceed when the user authorizes that chapter and phase.

*Independent final-diff review:* The three read-only reviewers checked the revised strategies and contracts. Their follow-up fixes were applied: explicit HU normalization, CDW oscillator signs consistent with the single-field adjoint, pending Gaussian wording, both SW off-block premises, consistent band carriers, same-sign shift composition, and the Klein construction contract at the vertex definition. The maximum-excursion scan remains a valid option; the older recurrence was not mathematically wrong when its list was already in application order.
