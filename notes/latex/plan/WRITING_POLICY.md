# Section writing contract

One task returns ONE standalone `.tex` file. Use the generated template verbatim
outside its body markers. Do not return JSON, a ZIP, a PDF or a second source file.
If a compiler is available, compile the standalone source and report its result
in chat. The human may request revisions in the same chat before downloading.
The controller archives each submitted download, not the web conversation.

The primary deliverable is a detailed book, assuming undergraduate quantum
mechanics. Introduce every additional mathematical construction before use;
write full proofs and worked examples rather than tactic transcripts. More than
200 pages is acceptable. Preserve useful source content. Move appendix arguments
into their first logical main-text use once; maintain labels and cross-references.
The short review-paper version is deferred.

## Context selection

Each packet identifies one target section, its chapter position and prerequisites.
Supply the whole chapter outline and existing chapter text when useful, the
original Markdown note, the relevant companion and exact Lean source snapshot,
shared preamble/bibliography, and this policy. Add adjacent sections and supporting
appendix excerpts only where they supply actual prerequisites. Do not send all
Core modules or entire reference books simply because the context window permits it.
The specification's explicit context paths and the manifest record what was sent.

The generated chapter/section catalog is navigational, not a completed source
coverage audit. Existing Markdown references identify literature anchors. The
source coverage ledger still needs claim-level review, particularly the selected
Giamarchi sections and source topics without an accepted finite counterpart.
Never invent page numbers or citations missing from the supplied source.

## Notation and mathematical scope

Use the shared preamble; request macro changes separately. The legacy global
notation chapter has known unresolved density/CCR convention issues and must not
silently override the target's exact Lean hypotheses. For the first CH19 pilot:
write a section explaining finite vector/density-matrix expectations versus the
abstract positive CCR functional. Use separate symbols for those evaluations.
The latter's polynomial carrier is not finite-dimensional; CH19 B-complete is
not Core promotion. Do not call its Gaussian functional a finite-CAR ground-state
expectation without a proved comparison. Preserve current product order and
state annihilation orientation from the supplied accepted proofs.
For later chapters a task-specific reviewed notation sheet is required before
claiming cross-chapter consistency; automated notation checks are a supplement.

Theorem bodies in Lean may guide mathematical derivations, but successful
compilation alone does not establish source coverage or the pedagogical claims.
State actual assumptions and projection residuals. Do not assert global nonzero
scalar CCR in finite dimension or silently convert a formal state into a finite
CAR density matrix. Mark unproved/draft results accurately.

## Acceptance

Only the section body enters the book. Local verification compiles the ACTUAL
master book with fresh auxiliary files and checks undefined references/citations,
duplicate labels, target inclusion and task-specific notation rules. The original
standalone download remains archived. Independent mathematical/editorial review
and explicit human approval precede integration. The author cannot self-approve.

## Current manuscript and section identifiers

The master includes CH01–21. CH19 uses its complete replacement chapter; the earlier 19.1–19.4 files are superseded provenance. CH20–21 use included numbered section files 20.1–20.3 and 21.1–21.4. Use numeric identifiers in task menus and
filenames, while retaining descriptive book headings and stable semantic labels.
These are manuscript drafts with independent mathematical/editorial review pending.
The user-requested batch import does not imply a passing independent review or
change any Lean status. A later Jules revision round is planned, not dispatched.

**Current master assembly (October 16, 2026):** the user explicitly directed
the book to cover every chapter and appendix topic. The existing CH12–18 chapter
sources and A05–A07/A10 appendices have therefore been integrated, and
pedagogical A08–A09 appendix sources added. Their inclusion does not alter the
Core/Phase-B/manuscript status recorded in the preface and each source. The
previous instruction to keep CH12–18 private is superseded for this book update.

## Original writing priority (historical)

Historical priority before October 16 was to draft chapters without a LaTeX
source, beginning with CH19, while keeping CH12–18 local. The explicit current
direction above supersedes that boundary for master-book coverage. Future
editorial revisions still require their own reviewed scope and must preserve
the mathematical status distinctions.

## CH19 writing record

The historical four-section queue has been superseded by the complete
`chapters/ch19_states_correlations.tex` replacement, included after Chapter 18.
Its master build passes; independent editorial review of this replacement is
still pending. CH19/A08 Lean Phase C is complete as recorded in
`note/ch19_phase_c_validation_2026-10-16.md`. This Lean status does not waive the
manuscript review gate or extend the proved scope.
