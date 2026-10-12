# CH14/A05 Phase C source migration: independent conditional review

Reviewer: `/root/ch14_phase_a` (Phase A author; separate from root's migration executor). This review concerns path/import/manifest preservation, not independent mathematical proof approval. The final proof auditor separately supplies that gate.

**Verdict: conditional PASS.** Apply this exact migration only after the fresh full Phase B build and standard-axiom audit pass. Record the actual migrated hashes and rerun both guards/builds and fresh audits through the Core aggregator before promotion completion.

The exact parser-level comparison and before/after complete-source hashes are recorded in [the migration comparison](ch14_phase_c_migration_review_2026-10-12.json). The comparison reads the current approved v2 records, independently parses each candidate, and asserts that every candidate record before migration matches its frozen entry.

- Move `BosonizeStubs/A05FiniteExponentials.lean` to `Bosonize/Core/A05FiniteExponentials.lean` byte for byte. Its 13 theorem interfaces and every command/context record are identical.
- Move `BosonizeStubs/Ch14Mandelstam.lean` to `Bosonize/Core/Ch14Mandelstam.lean`. Its only source substitution is `public import BosonizeStubs.A05FiniteExponentials` to `public import Bosonize.Core.A05FiniteExponentials`, exactly once. All mathematical data, theorem statements, comments and proof bodies remain unchanged.
- Move the two v2 manifest records by path. For CH14, recompute only the one affected import-command record and the 24 dependent theorem context hashes; preserve all 24 theorem-header hashes and every other command hash/text. For A05 preserve its entire existing record. Preserve every unrelated manifest entry and metadata. Do not regenerate a repository-wide baseline.
- Extend the complete-source Core manifest with the two new source hashes. All 21 old entries must retain their exact values; their current source hashes already match the frozen manifest.
- Add both new Core imports to the initial import block of `Bosonize.lean`, with the support module before its dependent chapter. Remove precisely those two staging imports from `BosonizeStubs.lean`; retain its existing Core aggregator import and module documentation.
- Move the two companions to `docs/companion/Bosonize/Core/` and update relative source/note links for the new depth, without conflating them with the complementary lecture notes.

No source/module migration was performed by this review. Candidate promoted copies are in `/tmp/bosonize-ch14/A05FiniteExponentials-promoted-candidate.lean` and `/tmp/bosonize-ch14/Ch14Mandelstam-promoted-candidate.lean`. If either input source changes after this snapshot, refresh this comparison before applying the migration.

The pedagogical-sync skill was read. Original current-worktree CH14 and A05 notes were preserved in `/tmp/bosonize-ch14/ch14_Mattis_Mandelstam_formula.md.original` and `/tmp/bosonize-ch14/a05_exponentials_klein_and_vertex_scope.md.original`; neither note has been changed by this review. Lecture synchronization may begin only after the fresh proof gate, and must preserve reference material while accurately explaining the finite compressed nilpotency, actual adjoints, full retained ground image, residuals and explicitly conditional field comparison.
