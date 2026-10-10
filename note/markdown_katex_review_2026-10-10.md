# Markdown and KaTeX formatting review — 2026-10-10

Scope: all 21 chapter lecture notes and A01–A10, plus the chapter TOC, appendix README and appendix brainstorm (34 Markdown files). This review changes presentation only and preserves the mathematical and physical content of the task-start working copies.

## Changes

- Mathematical formulas use math delimiters; Lean names and types use code spans. Existing fenced code is unchanged.
- Display delimiters and list spacing were normalized where needed. A04 had a commutator formula opened with a backtick and closed with a dollar sign; its delimiters are repaired.
- Plain annihilators paired with adjoints receive invisible `^{\phantom{\dagger}}` padding where appropriate. Bosonic fields do not receive this padding.
- Escaped braces were checked. The task-start notes contained no malformed `\left{` or `\right}` instances requiring correction.
- No hypotheses, physical conventions, signs, operator order, scope claims or proof status were deliberately changed. The CH20 dual tuple retains its named `gInv` parameter.

## Verification

KaTeX 0.16.22 rendered all 2,997 extracted math fragments with `throwOnError: true`, `strict: "ignore"`, and `trust: false`: zero parse errors and zero delimiter issues. Fenced and indented code blocks are byte-exact in all 34 files. All tracked files outside this note inventory retain their task-start hashes, including the pre-existing lock serialization change and deleted suggestion files.

Independent agents reviewed CH01–CH07, CH08–CH14, CH15–CH21 and A01–A10. Appendix review findings were corrected: padding was removed from a bosonic field, added to two missed annihilators, and remaining mathematical identities were moved out of code spans. All reviews preserve mathematical and physical meaning.

The strict stub guard verified 579 statements and 456 frozen commands. The Core guard verified 14 complete modules. No Lean source changed, so no new proof completion or build claim is made. Parser validation does not establish identical visual appearance in every Markdown viewer or mathematical correctness of the reference theory.

## Checkpoint and usage

Task-start copies and validation/review evidence are retained in `/tmp/bosonize-markdown-review/`. Formatting on previously clean notes is committed separately. Notes with pre-existing user edits retain their complete working copies, including the formatting corrections, without absorbing those earlier edits into this commit.

The usage guard reported 8% remaining in the five-hour window and 10% remaining weekly. The five-hour threshold has been reached; finish this validation checkpoint and recommend pausing before further development.
