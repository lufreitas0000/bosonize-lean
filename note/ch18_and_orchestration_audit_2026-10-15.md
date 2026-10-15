# CH18, project validation, and external delegation audit

Review date: 2026-10-15. Reviewed commit: `05c25e405efe980213e6d3fb8b374335c1e05632`.
Scope: read-only review of mathematical sources and orchestration; local validation;
no chapter development, model calls, routing changes, or modification of frozen Core.
This report is the only repository source addition from the audit.

## Findings

1. **CH18 positivity prose omits the positive-cutoff condition.**
   `notes/md/ch18_bogoliubov.md:112`, the promoted companion's explanatory paragraph,
   and ignored draft `notes/latex/chapters/ch18_bogoliubov.tex:261` assert strict
   positivity of the shift iff `v2 ≠ 0` without specifying `M ≥ 1`.
   For `h > 0` and a stable parameter package, the correct condition is
   `M ≥ 1 ∧ v2 ≠ 0`. The definition permits `M = 0`, making the sum zero.
   This is a prose omission, not a failure of a proved Core theorem. Lean checked:

   ```lean
   import Bosonize.Core.Ch18Bogoliubov
   example : Bosonize.Ch18.concreteV2 ≠ 0 ∧
       Bosonize.Ch18.vacuumShiftScalar 8 0
         Bosonize.Ch18.concreteParams.u Bosonize.Ch18.concreteParams.s = 0 := by
     constructor
     · norm_num [Bosonize.Ch18.concreteV2]
     · simp [Bosonize.Ch18.vacuumShiftScalar]
   ```

2. **The CH18 Markdown proof has a commutator transcription error.**
   `notes/md/ch18_bogoliubov.md:124` writes the second term as
   `rho_-m (rho_-m psi)`; it should be `rho_m (rho_-m psi)` when expanding
   `[rho_-m, rho_m] psi`. The Lean proof uses a correct left-branch expansion;
   the LaTeX draft's proof at lines 304–310 also uses the correct expansion.

3. **The LaTeX draft overstates the vacuum obstruction.**
   `notes/latex/chapters/ch18_bogoliubov.tex:276` asserts impossibility of a dressed
   vacuum in the active regime. The cited Core theorem excludes simultaneous
   bare-and-dressed annihilation on a nonzero budget vector under explicit margins.
   That theorem alone does not establish nonexistence of a dressed-only vacuum,
   a ground vector, or a ground energy formula. The remark at line 314 also needs
   to retain the budget/margin qualification. Additional assertions require
   independent arguments; do not silently strengthen the frozen theorem.

4. **The shared LaTeX notation conflicts with the verified current convention.**
   `notes/latex/frontmatter/notation.tex:100` uses a wrapped `k minus m` current;
   Core CH09 uses the nonwrapping partial shift. At line 104 the frontmatter gives
   `[rho_m, rho_-n] = +m delta`, whereas Core CH10 and the LaTeX CH10 convention give
   `[rho_m, rho_n] psi = -m delta_(m+n,0) psi`, hence
   `[rho_-m, rho_m] psi = +m psi`. The frontmatter sign, transfer direction, and
   restriction must be reconciled together. The outlook in `main.tex:63` also
   reverses the Sugawara product relative to draft CH12 (`rho_m rho_-m`).

5. **A successful current LaTeX workflow does not validate the later drafts.**
   The existing GitHub workflow builds `notes/latex/main.tex`, which includes only
   CH1–11 and A01–A04. Eleven later source files are locally ignored and absent
   from those includes. The original master builds successfully (110 pages).
   A temporary expanded master including CH12–18 and A05–A07/A10 also produces
   a PDF, but reports unresolved and duplicate references. Its exit status alone
   therefore does not establish an acceptable integrated book. The tracked
   workflow uses `-halt-on-error` but does not reject these reference warnings.
   No GitHub Lean workflow exists under `.github/workflows` at the reviewed commit;
   the local `scripts/ci.sh` does perform the Lean checks.

## Fresh verification

- `bash scripts/ci.sh`: PASS; 69 guard tests, strict statement/context locks
  (968 statements, 1020 commands), 31 complete Core locks, Core and staging builds,
  and 15 verifier/audit tests. The fixture `sorryAx` line belongs to a deliberate
  negative test, not a project declaration.
- `python3 scripts/webllm/audit_axioms.py Bosonize/Core/Ch18Bogoliubov.lean`:
  PASS, all 55 data/theorem declarations use only permitted standard axioms.
- The cutoff counterexample above compiled under `-DwarningAsError=true`.
- Offline hub orchestrator tests: 90 PASS.
- Local `main` equalled live GitHub `main` at the reviewed commit.
- Logs and disposable trial sources: `/tmp/bosonize-audit-20261015/`.

These results validate the checked Lean statements and tooling. They do not certify
all mathematical prose, all project declarations' axioms, or the unfinished CH19–21
and LaTeX integration work. No frozen Core change is justified by these findings.

## Proposed delegation policy, not implemented by this audit

- No Antigravity drafting, proof generation, or review by default; no implicit
  Antigravity fallback after external budgets run out. Desktop overage settings
  require separate control because `agentctl` cannot intercept desktop generation.
- Jules authors bounded LaTeX chapter/appendix patches from a committed source
  snapshot, a shared notation specification, and a Lean declaration mapping.
  Separate ownership of chapter text, shared notation, and master-book integration.
- An independent OpenAI or Gemini API reviewer checks mathematical fidelity and
  notation. Use a different provider from the author where available; adjudicate
  substantive disputes rather than blindly repeating entire reviews.
- Deterministic LaTeX builds, reference/label checks, and Lean audits run without
  asking an LLM to interpret routine successes. Return concise failure evidence
  to the original worker, with bounded retries and retained complete logs.
- Extend `agentctl` with an actual document-task dispatch/collection/verification
  path before claiming it already supports this workflow. Today its CLI and Jules
  collector primarily support theorem tasks. Routing table entries for `review`
  and `repo.chore` are not a complete generic task implementation.
- Jules needs committed GitHub-visible inputs; preserve and checkpoint ignored
  drafts before dispatch. Work stays on reviewable branches/PRs and is not merged
  merely because a session completed or a PDF was emitted.

Official capability references checked on the review date:
[Jules environment setup](https://jules.google/docs/environment/) and
[Jules sessions API](https://jules.google/docs/api/reference/sessions/).
