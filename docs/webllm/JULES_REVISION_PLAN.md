# Planned second revision round with Jules — not dispatched

> Historical review/plan snapshot. Status update 2026-10-17: CH19/A08 and finite CH20 are now promoted; the master includes CH01–21. The original findings below describe their reviewed source revision, not the current implementation or dispatch state. See the [current roadmap](../../adaptative_roadmap.md).

This is a plan only. No Jules sessions, API calls or chapter rewrites are
started by preparing or committing it. The current baseline is the compiled
manuscript containing CH01–11, CH19–21 and A01–A04. CH12–18 LaTeX drafts remain
private/local, not available to a GitHub-based worker merely because they exist
on the operator's computer. CH19/A08 is Phase-B accepted; CH20–21 chapter Lean is
unimplemented. Prose review cannot change those formal statuses.

## Group by shared prerequisites and editing difficulty

| Proposed task | Appendix context | Reason and boundary |
| --- | --- | --- |
| CH01–03 together (first pilot) | A01 Fourier; relevant lattice/umbral notes | One continuous foundations narrative; remove repeated prerequisites and keep one Fourier convention. Split if the pilot cannot return a bounded, reviewable diff. |
| CH04 alone | A02 finite CAR | Signs, adjoints and Hilbert-space construction need concentrated review. |
| CH05 alone | A02 and CH03–04 | Spatial Fourier/CAR and vacuum conventions. |
| CH06 alone | A02 plus exact CH06/extension support | Locality, twists and boundary hypotheses are too dense to hide in a large bundle. |
| CH07–08 together | A03 budgets; relevant partition material | Shared budget filtration; explain finite carriers versus ambient polynomial CCR once. |
| CH09 alone | A02/A03; CH07–08 | Density ordering, nonwrapping modes and exact finite identities. |
| CH10 alone | A03; CH09 | Edge terms and margins are a correctness-sensitive unit. |
| CH11 alone | A04 partitions; CH07–10 | Completeness, Gram identities and exact budget hypotheses. |
| Each of CH12–18 alone, later | Only its actual supporting notes and accepted Core | First make a sanitized writing packet from the private LaTeX draft. Do not upload ignored chat transcripts or publish the entire ignored directory. |
| CH19 alone | A08 plus exact CH19/A08 Phase-B sources | Harmonize its four new sections and distinguish finite and abstract states. |
| CH20 alone | Relevant A09 material, CH14 and CH19 | Projected residuals, formal series, signed duality; mathematical review pending. |
| CH21 alone | Relevant A09/A10, multispecies support | Parity, typed charge channels, leakage and finite Schrieffer–Wolff scope. |

Appendices are context by default. Where an argument belongs in the main text,
assign exactly one owning task to move it there. Remove the duplicate appendix
exposition only after that move is reviewed; retain a short cross-reference if
useful. For example, the foundations pilot can own A01, CH04 can own A02,
CH07–08 can own A03, and CH11 can own A04. Other tasks read those shared sources.
Do not allow simultaneous workers to rewrite the same appendix, preamble,
bibliography, notation table or master file.

## Bounded task contract

Give each worker one committed baseline, the existing chapter text, original
Markdown, relevant appendix sections, exact Lean/companion scope, shared notation
sheet, bibliography keys, and concrete review findings. The first pass should
identify the gaps and revise the assigned chapters; it must not regenerate the
book without comparing against the existing text. Preserve useful derivations,
examples, source anchors, labels and explicit limitations. Write for undergraduate
QM readers with full constructive mathematical arguments. Lean tactics are not a
substitute for a prose proof.

Whitelist only owned LaTeX files and any explicitly assigned appendix. Freeze
Lean/Core/stubs/locks, transport and CI code. Shared notation changes become
separate proposals; one coordination pass applies approved changes consistently.
Require a concise change report: results moved, material preserved, mathematical
corrections, unresolved questions and actual compilation evidence.

## Spend resources on distinct jobs

1. Pilot CH01–03 before dispatching the full queue. Measure diff size, compiler
   failures, source preservation and human review time. If the scope is too large,
   use CH01–02 together and CH03 separately rather than repeatedly restarting a
   three-chapter task.
2. Use at most two disjoint authoring tasks initially. Reserve one task/session
   per packet and keep corrections in that session; do not start a new worker for
   every compiler message. Never redispatch an uncertain session automatically.
3. Use deterministic scripts for wrapper extraction, diffing, source inclusion,
   notation checks and LaTeX compilation. Run one whole-book check on each ready
   candidate, with complete feedback saved; do not run a model to read routine
   compiler chatter. CI repeats publication verification after integration.
4. Human review checks exposition and preservation. If independent API review is
   needed, provide only changed claims, their dependencies and precise concerns.
   Use configured task/pool ceilings and stop after a bounded revision attempt;
   escalate substantive mathematical questions. Do not use Antigravity as the
   default reviewer, and do not pay for multiple agents to reread unchanged text.
5. Integrate approved patches one at a time and refresh subsequent baselines.
   Apply global notation/cross-reference reconciliation once per completed wave.
   Publish the resulting book and verify the release receipt against its commit.

A green compiler is a mechanical gate. It is not independent mathematical review,
proof completion, literature coverage, or evidence that a requested rewrite was
pedagogically successful. Those decisions stay explicit in the task report.
