# Bosonize-Lean: Exact Lattice AQFT Bosonization in Lean 4

Bosonize-Lean develops exact algebraic statements for 1+1-dimensional lattice bosonization. The program uses finite-dimensional CAR/budget spaces and polynomial or explicitly specified algebraic carriers. Formal series, where selected, are interpreted coefficientwise; analytic limits, Hilbert completions and topological interpretations require separate constructions.

**Current status:** Chapters 1–2 are proved and frozen in Core. The 21 chapter notes, ten supporting appendices and proof suggestions have a reconciled source baseline; later chapter statements remain implementation targets. See [the completion ledger](note/notes_review_completion_2026-10-09.md) for evidence, exclusions and Fourier readiness. Source notes and suggested proofs require scrutiny; the Lean kernel checks completed Lean proofs.

**Overall pipeline:** [Adaptive roadmap and Kanban board](adaptative_roadmap.md). The board orders dependent chapter work and records evidence. When a discovered mathematical/interface problem affects several notes or dependent files, halt the affected work and run a dedicated issue sprint before resuming. Routine local proof repairs stay within the chapter. A01/Chapter 3 Phase B is complete in staging: all 61 lemmas are proved against the approved interface, with warning-free compilation and standard-axiom audits. See the [A01 notebook](docs/companion/BosonizeStubs/A01FourierCharacters.md) and [Chapter 3 notebook](docs/companion/BosonizeStubs/Ch03Fourier.md). Phase C promotion awaits authorization.

**Chapter workflow:**

1. **Phase A — Draft and document:** Complete definitions, one-sorry theorem stubs, checked imports/APIs and an exact companion notebook. Present the interface for human review.
2. **Phase B — Prove the approved interface:** Lock the reviewed baseline, then change proof bodies while preserving definitions, names and signatures. Run guards and compiler checks; critically evaluate suggestions.
3. **Phase C — Audit, promote and freeze:** After authorized promotion, require zero warnings/placeholders and only standard axioms, migrate to Core, freeze its complete source and commit the verified checkpoint.

Review and lock approval follows the user's authorized scope. Guards establish interface preservation; they do not establish proof completion. Solve lint causes without suppressing linters, and never weaken a frozen theorem to make a suggested tactic succeed.

| Location | Purpose |
| --- | --- |
| `Bosonize/Core/` | Proved, immutable Lean sources, including frozen proof bodies. |
| `BosonizeStubs/` | Staging definitions/statements and approved proof work. |
| [Chapter index](notes/md/TOC.md) | Mathematical references and dependency roadmap. |
| [Appendix index](notes/appendices/README.md) | Supporting contracts and helper obligations. |
| `docs/companion/` | Mirrored source, design decisions, proof and validation evidence. |
| `docs/stub_suggestion/`, `docs/proof_suggestion/` | Advisory interfaces/proof ideas; adopted, adapted or rejected with reasons. |
| `note/` | Dated audits, completion records and future issue-sprint notes. |
| [Formalizer skill](.agents/skills/formalizer/SKILL.md) | Detailed A–B–C and proof-design instructions. |

Validation: run `make ci` for guard tests, strict definition/statement freeze, complete Core freeze and both Lean library builds. Use `STUB_LOCK_BASELINE_REF=<approved-commit>` to compare against a committed baseline. Axiom auditing and fresh warning-free chapter compilation supply separate evidence; a build with staging placeholders is not proof completion. If Lean MCP tools are not exposed to the chat, use the installed compiler/local library and report that fallback explicitly. See the [Lean MCP launch repair and live checks](note/lean_mcp_connection_repair_2026-10-09.md) for the desktop PATH fix, verified diagnostics/goals and current-chat reload boundary.

The approved A01/Chapter 3 interface lock is committed at `73add90`. Strict CI passes against that baseline; all proof changes preserve definitions and statements. Both modules remain in staging until authorized Phase C promotion and complete-source freezing.
