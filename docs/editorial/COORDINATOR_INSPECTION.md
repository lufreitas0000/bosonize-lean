# Coordinator inspection of Jules's first editorial review

## Decision and boundary

This is an inspection of the 24-observation final Jules report obtained from the completed session
8606663091090500557 after two corrective messages. It is a first editorial review,
not a mathematical verification of the book and not approval of every proposed
sentence. Preserve the raw Jules report alongside this assessment. The user's
STYLE_AND_SCOPE.md governs later prose; the review's remaining promotional
adjectives are not a model for the manuscript. No chapter rewrite is authorized or
started by accepting this report as an editorial artifact.

Coverage is the published manuscript: CH01–11, CH19–21, A01–A04 and frontmatter.
Private CH12–18 LaTeX drafts were not reviewed. Their implemented Lean modules are
promoted; their omission from this PDF does not make the formal theories unverified.
CH19/A08 is Phase-B accepted and not Core promoted; CH20–21 chapter Lean remains
unimplemented. These statuses must remain separate from editorial readiness.

## Evidence and checks

- The original 14-observation artifact admitted nine unreviewed chapters. It was
  rejected as a complete first pass; its scope/tone examples also needed correction.
- The next artifact added observations but retained a stray planning file and
  inaccurate finite-dimensional prose. It was not accepted through the whitelist.
- The inspected 24-observation final candidate changes only first_review.md and passes
  strict patch extraction at baseline 15849fa603c1d2c0b5b555c103647a57e427088d.
- Its verifier passed inside the namespace sandbox in a disposable checkout. The
  complete read-only source inventory is unchanged; only the report was added. The normal agentctl collector independently passed the same gates at candidate commit 901f5d535d63be77fe9543a3fcdbf52e701fc33d. Its final file is byte-identical to the inspected snapshot.
- All 24 finding anchors were inspected against the actual numbered sources.
  Most identify the relevant passage. ED-16 cites the charge definition at 23–24;
  the admissibility bounds are actually at CH07 lines 25–28. This is a retained
  convention, not a defect requiring a manuscript correction.
- Coverage and connection tables now include all fourteen published chapters.
  That is useful first-pass coverage, not a claim that every proof, citation or
  word has received an independent mathematical/literature audit.

## Disposition of the observations

| Findings | Inspection result and instruction for later revision |
| --- | --- |
| ED-01–02 | Confirmed preface completeness/superiority problems. Use a modest account of selected literature constructions; explicitly disclose missing prerequisites and limits. |
| ED-03–04 | Explain the chosen finite setting and half-open band convention. Do not imply that Lean/Fourier theory requires finite dimension, or that the mirrored convention is impossible. |
| ED-05 | Valid scope concern. A protected-subspace identity does not establish unrestricted lattice/continuum dynamical equivalence. Check the exact theorem and margin before choosing replacement wording. |
| ED-06–07 | Qualify the difference-calculus correspondence and fixed-model regularization. Do not claim preservation of every continuum structure or elimination of every divergence. |
| ED-08 | Low-priority explanation of an occupation-basis ordering convention. Do not turn this into a new mathematical limitation or pretend the physical index specialization is absent: CH04 already gives it at lines 14–17. |
| ED-09 | The cited CH05 paragraph already makes a fairly neutral distinction between smeared continuum fields and bounded lattice operators. Retain it unless editing surrounding prose improves continuity; do not manufacture a polemical defect. |
| ED-10–12 | Confirmed tone/scope problems in CH06–08. Explain the different chosen setting; remove claims of pristine construction, immediate universal divergences or elimination of topological subtleties. ED-11's assertion that the original blanket claim is simply true is not independently endorsed here. |
| ED-13 | Retain the distinction between adjointness for the algebraic pairing and operator adjoints/domains in a completed Hilbert space. Verify exact hypotheses when rewriting. The positive pairing is not merely a heuristic because no completion was chosen. |
| ED-14 | Important mathematical-scope warning. Finite dimension and projection do not imply nilpotency; a finite identity matrix is already a counterexample. State the actual nilpotent maps and source/target cutoffs for terminating exponentials. |
| ED-15 | Optional style edit: “central feature” is available. A pedagogical metaphor need not be removed merely for being informal; do not flatten all explanatory prose into sterile wording. |
| ED-16 | Checked convention to preserve: N equals particle number minus h, giving -h <= N <= h. Not a requested correction. Use CH07:25–28 for the bound's actual anchor. |
| ED-17 | Replace a claim that continuum arguments break down with an explanation of the finite counting/Gram argument used here and its hypotheses. Do not imply that other finite adaptations are impossible. |
| ED-18–19 | Important caveats already present in CH20–21. Preserve them. They are strengths to carry into later revision, not newly discovered errors. Distinguish projected CAR identities, formal oscillator models, spin/charge linear combinations, budget commutation and state-space factorization. |
| ED-20 | Actual spatial-fermion naming and phase differences need an explicit alias/convention map; see the paired sources below. No blind renaming. |
| ED-21–22 | CH19 already distinguishes g from g_U and abstract from finite expectations. Preserve that practice and include it in the global ledger. Do not invent a conflict where an explicit distinction already works. |
| ED-23 | Miranda and Sénéchal are absent from the current bibliography. Verify the intended works and claim-level source use before adding real entries; no invented pages or placeholders in the published book. |
| ED-24 | Confirmed reader-facing gap. Distinguish a temporary prerequisites/coverage bridge from actually supplying the missing CH12–18 derivations. |

## Notation decisions that must precede global replacement

1. **Spatial Fourier phase.** The frontmatter defines the annihilator with
   chi(-k,x) at notes/latex/frontmatter/notation.tex:64–67. CH05 defines it with
   chi(k,x) at notes/latex/chapters/ch05_fermions.tex:34–38. CH21 uses positive
   zeta^(kx) at notes/latex/chapters/sections/21.1.tex:27–34. CH03 analysis and
   synthesis have opposite signs at notes/latex/chapters/ch03_fourier.tex:63–71.
   These formulas must be related explicitly to the chosen source/Lean convention;
   do not call ordinary analysis/synthesis conjugation itself an inconsistency.
   Jules's CH03:53–54 anchor is only a heading, so use these formula anchors.
2. **Density and CCR.** Frontmatter:98–104 uses a cyclic wrapped lowering shift
   and a stated scalar commutator. CH09:75–81 defines a nonwrapping raising shift
   and its normal-ordering correction. CH10:103–109 states the protected-budget
   bracket in the reverse index order. This is an actual definition/scope issue,
   not just typography. Reconcile against the exact carrier, shift and margin;
   never transfer a scalar CCR to arbitrary finite matrices or redefine frozen Lean.
3. **Spin and charge.** The actual symbols are R^c and R^s, defined without
   1/sqrt(2) at notes/latex/chapters/sections/21.1.tex:152–183. The review's generic
   J/J_raw row is not the book's notation. Use the actual R symbols; distinguish
   raw from normalized currents, and preserve the actual hypotheses for any 2m CCR.
4. **States and parameters.** Keep finite vector/density expectations separate
   from the abstract state and its coefficientwise extension. Keep g and g_U
   distinct. A source-compatible symbol table is useful; it does not prove an
   interacting finite-CAR/abstract-state comparison.

## Chapter-by-chapter connection instructions

These are brief/handoff instructions, not changes already made to the chapters.

| Chapter | Concrete entry/exit instruction |
| --- | --- |
| CH01 | Begin with the finite circle as a modelling choice and fix the representative convention. End by motivating the shift and finite differences used in CH02. |
| CH02 | State which space each operator acts on. Connect the periodic difference identities to diagonalization by finite characters in CH03; do not conflate the bilateral-sequence CCR with finite-matrix identities. |
| CH03 | Introduce analysis/synthesis signs and distinguish algebraic inversion from complex-unitary normalization. End with the unitary change of one-particle basis needed for CAR. |
| CH04 | Retain the existing examples specializing the finite index set to momentum/spin labels. End by pointing to their Fourier realization in CH05, without repeating the CAR construction. |
| CH05 | Retain its clear opening that combines CH03 and CH04. Make the spatial-field convention explicit, then motivate local field and even observable algebras for CH06. |
| CH06 | Distinguish graded field locality from ordinary locality of even observables and from the broader continuum axiom program. End by explaining why the next step chooses charge sectors and reference states. |
| CH07 | Define charge, ground and excitation budget before using margins. End by separating the finite fermionic budget from the ambient bosonic carrier introduced in CH08. |
| CH08 | Say immediately that bounded mode count does not bound polynomial degree. Explain the pairing, finite budgets and exact domains of exponentials; lead into their fermionic current realization in CH09. |
| CH09 | Define nonwrapping currents and normal ordering explicitly. End with the question of what their commutator does at finite band edges, answered in CH10. |
| CH10 | Put global edge terms before the protected scalar identity and track word-dependent margins. End by asking whether current-generated states span the protected budget, motivating CH11. |
| CH11 | Connect counting and Gram identities to the precise completeness regime. Close with an honest map of omitted CH12–18 prerequisites and the limited route to CH19, not a promise that the PDF already derives them. |
| CH19 | List the required oscillator/Bogoliubov/state definitions and distinguish each carrier. End by separating finite comparisons from the formal order-parameter models in CH20. |
| CH20 | Keep finite projected CAR identities and formal-series correlators in separate stages with an explicit comparison gap. End by motivating the four-species, charge-shift and parity questions of CH21. |
| CH21 | Define species order and raw charge/spin conventions before using them. Close with the distinction between finite leakage/SW identities and any later continuum RG, gap or full separation construction. |

## Tone and next-stage order

Use STYLE_AND_SCOPE.md as the authority, not unqualified adjectives in Jules's
executive paragraph. A suitable opening describes selected rederivations, credits
the literature, explains the chosen finite objects and identifies what remains
outside the construction. It does not say that the literature's methods are less
rigorous, that every part of the framework is finite-dimensional, or that choosing
a lattice resolves all analytic questions.

First settle the frontmatter conventions and prerequisites/status language as a
small reviewed coordination task. Then use CH01–03/A01 as the rewrite pilot and
CH07–08/A03 as a later pair. Keep the dense chapters separate, especially CH20
and CH21. Give each shared appendix one owner; others use it as read-only context.
The current book's useful derivations, examples and caveats must be preserved.
Each later rewrite needs a source-preservation diff, actual-book compilation and
inspection of changed mathematical claims. No rewrite is dispatched by this review.
