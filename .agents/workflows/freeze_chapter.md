# Phase C: Audit, promote, and freeze

Execute after the user authorizes Phase C for a fully proved chapter.

1. Check the chapter against its approved definition/statement baseline. Require no `sorry`/`admit`, no compiler warnings, and only `propext`, `Classical.choice`, and `Quot.sound` in every lemma's axiom dependencies. Use freshly built declarations for the axiom audit.
2. Move the completed source from `BosonizeStubs/` to `Bosonize/Core/`. Preserve the Lean namespace, definitions, and statements. Add its import to `Bosonize.lean` and remove its direct staging import from `BosonizeStubs.lean`; staging already imports the Core aggregator.
3. Move the existing chapter entry in `docs/spec/stub_locks.v2.json` to its new source path, preserving every recorded hash and context entry. This is an explicitly authorized path migration, not permission to change other chapters or regenerate the entire interface baseline.
4. Record the promoted file's SHA-256 in `docs/spec/core_locks.json` without altering hashes of existing Core files. `core_lock.py` has no automatic update command: extending this manifest belongs to the reviewed promotion. Core proof bodies must now remain unchanged along with definitions and statements.
5. Move and update the companion notebook under `docs/companion/Bosonize/Core/`. Include proof strategy, exact source, axiom output, validation evidence, and the approved baseline migration. Retain the v1 manifest as historical migration evidence.
6. Run both guards, their tests, and both Lean library builds through `make ci`. Import the Core aggregator for the final axiom audit to verify the promoted chapter is accessible to downstream chapters.
7. Commit the completed proof work and promotion checkpoint. Verify both guards against that committed Git reference and report the commit and final working-tree status. Do not begin the next chapter unless it is included in the user's authorized scope.
