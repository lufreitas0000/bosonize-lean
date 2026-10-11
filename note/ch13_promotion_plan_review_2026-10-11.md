# CH13/A05 promotion plan: independent scoped review

Date: 2026-10-11. Reviewer: inherited Codex fallback; Flash/Pro providers unavailable.

**Scoped migration-plan result: PASS, conditional on all Phase B proof gates. No migration was applied by this reviewer.** Require zero placeholders, a warning-free build, the fresh 95-declaration axiom closure restricted to `propext`, `Classical.choice`, and `Quot.sound`, and independent final proof review before applying this plan. These checks are obligations, not inferred from this migration review.

Move `BosonizeStubs/A05MultiSpecies.lean` to `Bosonize/Core/A05MultiSpecies.lean` byte-identically. Move `BosonizeStubs/Ch13KleinFactors.lean` to `Bosonize/Core/Ch13KleinFactors.lean`, changing only its `public import BosonizeStubs.A05MultiSpecies` to `public import Bosonize.Core.A05MultiSpecies`. Preserve every namespace, theorem header, data definition, other command, and proof body. Recompute final source hashes after completed proof integration; the in-memory review snapshots are not final promotion hashes.

The installed guard parser was run on the current source and the hypothetical import-only substitution. All 28 A05 and 25 CH13 theorem-header hashes match the existing frozen baseline. A05 has no changed command or dependent context. CH13 has exactly one changed command: import-command index 2 (the separately parsed `public` command remains unchanged). Its 25 theorem context hashes depend on that import and must be recomputed. Every other CH13 command hash remains unchanged. Exact parsed evidence and the source-bound snapshots are in `/tmp/bosonize-ch13/promotion-plan-review.json`.

Move only those two v2 file records to their Core paths; preserve all theorem-header hashes and unchanged command hashes. Update only the reviewed CH13 import hash and its dependent context entries. Add the two final complete-source SHA-256 values to `docs/spec/core_locks.json`, preserving the existing 19 entries exactly. Do not regenerate an unrelated baseline.

Move the two existing companions from `docs/companion/BosonizeStubs/` to `docs/companion/Bosonize/Core/`, updating source links and verified evidence while retaining history. Add both promoted imports to the initial import block of `Bosonize.lean`, and remove their direct staging imports from `BosonizeStubs.lean`, which already imports the Core aggregator. Perform source-preserving pedagogical synchronization only after fresh proof closure.

After migration, require strict guards, both warning-free library builds, the native Core diagnostics, and a repeated fresh axiom audit through the Core aggregator. Review the exact manifest delta against this plan before the Phase C checkpoint. This is a path/import migration review, not permission to alter mathematics or proof bodies.
