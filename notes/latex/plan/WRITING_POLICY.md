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

## Current writing priority

Write the chapters that have no LaTeX draft yet, starting with CH19. CH12–18 have
private local drafts awaiting separate review/integration; preserve them. CH01–11
are already in the published book and are not being rewritten in this sprint.
A later Jules task may revise existing chapters. Do not interpret the section
workflow as authorization to rewrite the whole book.

## CH19 writing queue

1. `book_ch19_scope.toml`: finite expectations versus abstract functionals.
2. `book_ch19_mode_correlators.toml`: ordered mode contractions.
3. `book_ch19_spatial_correlators.toml`: spatial kernels and symmetrization.
4. `book_ch19_finite_comparison.toml`: finite-Fock comparison and limitations.

Prepare the next task only after integrating its predecessors. Each later packet
requires their committed section files as context, so work follows a continuous
narrative. The writing queue does not bypass CH19's pending formal promotion.
