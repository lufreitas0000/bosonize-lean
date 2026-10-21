# Reconciliation API audit: backup yes, promotion no

## Verdict

**Backup is supported. Promotion is not.**

The supplied evidence supports archiving/backing up the current main state at `source1bdd21f` with the accepted Core/S1–S5 material left unchanged, while **S6 h3 remains intentionally pending** and must stay labeled as such. This audit does **not** justify automatic promotion or any claim that the paused editorial wave has been fully accepted.

## Evidence and anchors

### 1) Current-main chronology and lock evidence

From `docs/integration/reconciliation-audit-input.md`:

- `Source HEAD1bdd21f49fbdc977c597a99c3cb3d7ab038129d6`
- `Sandboxed make lock-check passed 1317 statement/1394 command+43 Core files`
- `Full sandboxed make ci now PASSED at source1bdd21f (guards,Core,staging,WebLLM verifier tests)`
- `Staging sorry warnings are explicitly permitted; no promotion claimed`
- `S6 h3 staged placeholder remains intentional and must be labeled`
- `No lock regeneration`

These are the relevant scope/lock anchors. They support **backup of the current main snapshot**, not a promotion claim.

### 2) Editorial-wave supersession status

From `docs/editorial/REWRITE_WAVE1_STATUS.json`:

- `stage`: `Paused by user on 2026-10-16`
- `All 15 author candidates are mechanically verified; manuscript acceptance and final main release are pending`
- `mechanical_verification_is_not_editorial_or_mathematical_acceptance: true`
- `CH21` is `waiting_jules`
- acceptance items remain open for CH21 author, foundations reviewer, and currents reviewer

This means the wave is **mechanically prepared but not editorially accepted**. Hash differences alone do not establish obsolescence or acceptance.

### 3) Current source anchors in the manuscript

Relevant current-source anchors show the manuscript itself already distinguishes between backed-up review scope and still-pending work:

- `notes/latex/main.tex` includes `chapters/ch19_states_correlations`, `chapters/ch20_order_parameters`, and `chapters/ch21_spinful_umklapp` in the main book flow.
- `notes/latex/chapters/ch19_states_correlations.tex` explicitly says the chapter is complete only **within its reviewed scope** and that the **finite interacting ground-state equivalence is not established** there.
- `notes/latex/chapters/ch20_order_parameters.tex` and `notes/latex/chapters/ch21_spinful_umklapp.tex` contain stronger chapter-level claims than the current acceptance state supports, so they should remain scoped as chapter promises, not release claims.

## Backup versus promotion

### Backup supported

Backup is justified because the supplied record shows:

1. main chronology is already at `1bdd21f`;
2. lock-check evidence exists;
3. full sandboxed CI evidence exists for that source;
4. the editorial wave is paused but mechanically verified;
5. S6 h3 is explicitly still pending and labeled as such.

### Promotion not supported

Promotion is **not** justified because:

1. CH21 review remains pending (`waiting_jules`);
2. the status file explicitly says mechanical verification is not acceptance;
3. the audit packet itself says no promotion is claimed;
4. the task requires distinguishing backup from promotion, and the supplied evidence only reaches the backup threshold.

## Supersession logic: what the hashes do and do not prove

The current source chronology shows that many chapter files differ from both the old wave and the candidate hashes, while some files are exact matches to the old author base. That means:

- hash mismatches are **not** enough to call an older editorial wave obsolete;
- hash matches are **not** enough to claim acceptance;
- the correct conclusion is that the manuscript has evolved beyond the old wave in several places, but the old-wave logic still needs human/editorial treatment where the prose remains scope-sensitive.

One concrete example from the supplied chronology:

- `notes/latex/chapters/sections/21.2.tex` is `old_equal_current: true`, showing that hash-difference reasoning must be applied carefully and not as a blanket supersession rule.

## Concrete residual prose corrections worth salvaging

These are not source fixes; they are prose-level candidates that remain worth keeping or tightening rather than being dismissed just because hashes differ.

### A) Keep the CH19 scope boundary explicit

In `notes/latex/chapters/ch19_states_correlations.tex`, the chapter already contains the right kind of corrective wording:

- it distinguishes the finite CAR system from the abstract CCR algebra;
- it warns that agreement holds only for **protected words / protected states**;
- it states that the Gaussian state is **not automatically** the finite interacting ground state.

That boundary language should be preserved. It is a genuine corrective and should not be flattened by hash-based supersession reasoning.

### B) Soften CH20 introduction-level definiteness

In `notes/latex/chapters/ch20_order_parameters.tex`, the introductory prose is still more assertive than the acceptance state supports. The salvageable correction is to frame the chapter as conditional and scoped, e.g.:

- “we analyze” rather than “we demonstrate” when the claim depends on later review;
- “within the stated finite-mode hypotheses” rather than an unconditional global statement.

This is a wording correction, not a mathematical change.

### C) Keep CH21 chapter claims provisional until review completes

In `notes/latex/chapters/ch21_spinful_umklapp.tex`, phrases like:

- “This chapter establishes…”
- “resolving the exact nature…”
- “Finally, we formalize Umklapp scattering…”

should remain **provisional** until the paused CH21 review is completed and accepted. The current evidence supports the chapter as a candidate, not as a promoted final statement.

## Commands versus skipped checks

### Evidenced commands/checks

From the supplied packet, the relevant checks were:

- `python3 -m unittest discover -s scripts/guards -p 'test_*.py'`
- `python3 scripts/guards/stub_lock.py --check --strict`
- `python3 scripts/guards/core_lock.py`
- `lake build Bosonize`
- `lake build BosonizeStubs`
- `python3 -m unittest discover -s scripts/webllm -p 'test_*.py'`

The supplied record says these passed in the sandboxed CI run for `source1bdd21f`.

### Skipped in this report-only audit

I did **not** rerun compilation, lock regeneration, or source mutation here. In particular, this report does **not** claim new build results beyond the supplied evidence.

## Final assessment

- **Backup:** yes, supported by the supplied lock/CI evidence and the current-main chronology.
- **Promotion:** no, not supported; S6 h3 is still pending and the editorial wave is paused.
- **Prose salvage:** yes, especially the scope delimiters around CH19–CH21, which should remain explicit rather than being discarded as “obsolete” just because hashes differ.
