---
name: pedagogical-sync
description: Update Bosonize-Lean pedagogical chapter and appendix notes after verified formalization, preserving reference theory and explaining the actual constructive Lean realization in natural mathematical language. Use during Phase C or an explicitly requested synchronization; do not infer proof completion from stubs or rewrite unrelated notes.
---

# Synchronize pedagogical theory and verified construction

This skill is specific to Bosonize-Lean. Phase C must update both the exact companion notebook and the corresponding pedagogical note: chapters in `notes/md/`, supporting appendices in `notes/appendices/`. Keep the two Markdown documents complementary. The companion focuses on the formal Lean document: exact declarations, source snapshot, proof dependencies, audit evidence and technical provenance. The pedagogical Markdown is a lecture note about the Lean file: explain what its objects and constructions mean, why they were chosen, how its mathematical arguments work and how they realize the abstract theory. Explain the abstract mathematical theory and its actual constructive realization together, preserving the information in the original reference note. Routine synchronization is included in the authorized chapter cycle. An explicit workflow-only request updates these instructions, not the entire note corpus.

## Establish the verified scope

Read the current pedagogical note from the worktree, its related source references/corrections, the final promoted Lean source, companion and fresh Phase C build/axiom evidence. Use `notes/md/TOC.md` and the appendix index to establish the actual note/module mapping; do not infer it solely from filenames. Multiple modules can realize one note, and an appendix can have only one implemented portion. An extension may belong as a subsection of the original chapter. Use indexes for navigation, not proof status: verify status against the actual source and audit evidence, and flag stale index claims without expanding a targeted update into a corpus rewrite. Update only corresponding authorized notes/sections; record their mapping in the companion.

For every result described as formalized, check the actual carrier, parameters, hypotheses, conclusion and complete proof. Record the declaration/source anchor and evidence in a compact companion mapping; only add code names to the pedagogical text when they aid navigation. A draft signature, agent review, finite numerical check or successful build with sorry is not a proved result. If evidence is incomplete, retain accurate draft/pending labels and do not declare Phase C complete.

## Preserve the reference and explain the realization

Use the current worktree text as the preservation baseline, including user edits. Retain definitions, formulas, examples, physical interpretation, citations and mathematically relevant caveats from the reference exposition. Prefer adding a clearly titled “Constructive realization in Lean” section or topic-level subsections. Update an existing realization section rather than duplicating it; retain useful conceptual information as it is revised. Where an existing “Lean 4 Proof Strategy” describes a different proposed approach, preserve its explanatory content, identify it as an earlier proposal and explain the actual choice alongside it. Do not imply that historical suggested code was the implementation. Do not replace the theory with code commentary, silently delete unformalized claims, or erase reference material to make it match the implementation.

Describe the implemented mathematics in natural mathematical prose and equations:

- Give the actual carrier and objects: for example, finitely supported polynomials, finite occupation configurations, a weighted Hermitian pairing or a genuinely finite Hilbert space.
- Explain construction choices and why they matter: integer representatives and endpoint convention, explicit basis extension, positive mode weights, sector labels, truncation/projection and normalization.
- State what was proved, with its exact hypotheses, domain and source/target. Relate it to the abstract statement: exact realization, conditional version, finite model, or only one part of the reference theory.
- Explain how the proof works mathematically, such as basis action, finite coefficient sums, a grading argument, or an exact projection remainder. Avoid a tactic transcript, typeclass tutorial, import list or unexplained API names.
- Retain physical parameters, including boundary twist/holonomy and charge, wherever the verified construction retains them. Explain cancellation only for quantities with an actual cancellation theorem.
- Describe limitations and open obligations where they change the reader's interpretation: ambient versus compressed operators, algebraic versus analytic statements, actual adjoints versus pairing identities, or an unproved model comparison. Keep unformalized reference theory visible with accurate status.

The reader should understand the mathematics without knowing Lean. A short link to the promoted source and companion is sufficient for implementation navigation. Exact declaration mappings, proof logs, full source snapshots, counts and hashes belong in the companion. Use a comparison table only when several choices are easier to compare that way; do not impose a fixed essay template.

If the source note contains an error exposed by the proof, preserve its reference context and explain the discrepancy and correction explicitly. A source-determined correction can be documented and independently reviewed within scope. Competing physical conventions or changed mathematical targets require the user's decision under the [pipeline policy](../formalizer/references/pipeline.md). Do not describe a weaker theorem as a proof of the stronger reference claim or edit frozen Core to make the story consistent.

## Review and Phase C completion

Give another agent the pedagogical diff, current baseline, final Lean source, companion and validation evidence. The reviewer checks that reference information is preserved, the prose matches proved declarations and hypotheses, status labels are accurate, and the constructive explanation is readable as mathematics. Record reviewer/task, findings/resolution and verdict in the companion. Resolve deterministic findings and have changed passages reassessed; human involvement is reserved for substantive ambiguity. Missing independent review blocks documentation completion rather than permitting self-approval.

Inspect the diff against the captured worktree baseline, not only HEAD: preserve unrelated/user-authored content and existing citations. Check formulas, notation, relative links/anchors and source/companion coherence. Evidence of preservation is a content comparison, not merely a build or hash count. Do not run unnecessary Lean proof searches for a prose-only edit; reuse fresh Phase C evidence unless the underlying source changed.

Phase C is complete only when the corresponding pedagogical update and its review pass, together with the formalizer's proof/build/axiom/guard gates. Include the note, companion and code/lock migration in the scoped checkpoint, and report the pedagogy update and any explicitly unformalized remainder. Standalone synchronization of already promoted chapters uses this same evidence/preservation review but does not re-promote or mutate Core. There is no automatic retrospective rewrite of earlier chapters unless the user requests that scope.
