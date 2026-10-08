# Chapter 1 freeze audit — 2026-10-08

## Current status: Phase C completed

Chapter 1 is promoted to `Bosonize/Core/Ch01LatticeBand.lean`. Its full v2 manifest entry was moved from the staging path with all 20 header hashes and 24 command entries unchanged. The approved source namespace remains `Bosonize.Ch01`, and every lemma is proved. The v1 manifest is retained as historical evidence rather than regenerated after migration.

`stub_lock.py` now scans both staging and Core. `core_lock.py` additionally checks SHA-256 hashes of complete Core files against `docs/spec/core_locks.json`, including proof bodies and comments. It rejects changed, missing, and unreviewed Core files and has no baseline-update command. CI and `make lock-check` run both guards. The combined suite contains 65 passing tests (59 interface-guard tests and 6 Core-freeze tests). Both library builds pass with no warnings, and all 20 lemma axioms were checked through `import Bosonize`: only standard Lean axioms occur.

This authorized promotion changes the active manifest's chapter path and adds a reviewed complete-source manifest. Future Git-reference checks must use a reference containing that promotion, rather than the earlier staging-only baseline. The original v2 audit below records the state before proof work and promotion.

## Initial v2 audit (historical)

The active v2 baseline, `docs/spec/stub_locks.v2.json`, matches the current chapter: **20 lemma headers and 24 fully frozen command entries**. `python3 scripts/guards/stub_lock.py --check --strict` passes. The migration check, `--legacy-check`, also confirms that all 20 statements still match the prior v1 record. Neither baseline nor the staging Lean source was changed during the v2 audit.

## Guard behavior

The v2 guard lexes comments and literals, splits command text, hashes complete non-lemma commands in order, and hashes lemma/theorem headers independently of proof bodies. It also records the preceding non-lemma context for each lemma. Definitions, abbreviations, instances, imports, namespaces, options, attributes, and other environment commands are consequently covered in guarded files. The 24 command entries include parser fragments such as `public`; they are not a count of 24 mathematical definitions.

Comments and proof-body changes are allowed. New lemmas and new files cause warnings by default; **use `--strict`** to reject them until reviewed and included in an approved baseline. The script refuses to overwrite changed frozen content without `--accept-changes`, and refuses `--update` whenever the `CI` environment variable is set. Agents must never use these update options to hide drift.

The earlier v1 guard froze only theorem/lemma statements. Its temporary-copy tests allowed definition, namespace, and extra-declaration changes. Those results described v1 and are superseded by the v2 checks below; the old `stub_locks.json` is retained as migration evidence only.

## Validation

The supplied 56-test suite passed. It covers headers, defaults containing `:=`, comments and literals, attributes/modifiers, definitions and instances, environment/context changes, additions and deletion, strict-mode behavior, update protection, and verification against a committed Git baseline.

Fifteen additional temporary-copy checks used the actual chapter and its existing v2 baseline:

| Change | Strict guard result |
| --- | --- |
| None | Pass |
| Proof-body replacement | Pass |
| Nested comment addition | Pass |
| Quotient definition changed to zero | Reject |
| Band boundary changed | Reject |
| Decidability instance changed | Reject |
| Lemma hypothesis changed | Reject |
| Lemma conclusion changed | Reject |
| Namespace changed | Reject |
| Import changed | Reject |
| Lemma renamed | Reject |
| Lemma added | Reject |
| Axiom added | Reject |
| Unterminated comment | Reject |
| Unterminated string | Reject |

An additional audit found that malformed brackets inside unfrozen proof bodies were not rejected by the original v2 scanner. Whole-file bracket validation was added, together with three regression tests for unclosed, mismatched, and extra closing brackets. The resulting **59-test suite passes**. Comments and string/character literals remain excluded from bracket interpretation.

`make ci` now runs the guard tests and strict freeze verification before building Core and staging. Both library builds pass; staging retains the 20 expected `sorry` warnings. The Makefile Core-build comment was corrected: warning checks do not perform the separate theorem-axiom audit.

## Working with the freeze

1. Before editing, run `make lock-check` or `python3 scripts/guards/stub_lock.py --check --strict`.
2. Read the mathematical source and chapter-relevant suggestions critically. Preserve approved definitions, context, names, hypotheses, and conclusions; edit only proof bodies of locked lemmas.
3. New supporting declarations require explicit review and baseline extension. Strict verification rejects additions until that occurs.
4. After each proof batch, run the strict guard, review source/dependency diffs, compile, and update the companion notebook. Never regenerate the baseline as a routine proof step.
5. Before Core promotion, require complete proofs and a theorem-axiom audit; passing the freeze is not a proof-completion certificate.

To verify against an approved committed baseline rather than the editable working-tree record, use `--baseline-ref <approved-ref>`. CI supports the same choice through `STUB_LOCK_BASELINE_REF`. For example, after committing the baseline, `STUB_LOCK_BASELINE_REF=HEAD make ci` verifies against that commit. A stable approved reference is needed for review of later changes; a reference containing an unreviewed replacement baseline cannot provide that protection.

## Limits

This remains a text-level guard, not Lean's elaborator or filesystem write protection. Imported modules outside the guarded directories, dependency revisions, and toolchain changes require separate review. Formatting changes to frozen commands can cause conservative failures. Unsupported syntax may require parser improvements or freeze whole declarations. `--dir` changes the scan scope and must not be used to exclude locked files. Keep the script and baseline themselves reviewable in Git. No Phase B proof work was performed in this audit.
