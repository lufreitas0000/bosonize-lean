# CH10/A04 Phase C verification — 2026-10-10

Reviewed interface baseline: `e2074b4`. Complete Phase B checkpoint: `7b0f1c1`.
The one-time scheduled continuation was handled and its automation deleted.

## Formal scope

A04CurrentMargins has 16 complete theorem proofs and three data definitions.
Ch10Heisenberg has 21 complete theorem proofs and three data definitions.
They use the actual CH09 partial density currents and frozen CAR occupation carrier.
The diagonal Schwinger action retains M1; unequal/general current action retains M2.
Signed budgets and actual application-order/right-suffix excitation margins are explicit.
The arbitrary-boundary-twist theorem uses the reconstructed partial-current dictionary,
not the cyclic site Fourier density with its nonzero wrap remainder.
Ground witnesses and the empty-ket obstruction rule out vacuous/trivial replacements.
Partitions, Gram/completeness, Sugawara and later physical model claims remain unformalized.

## Independently reviewed migration

Reviewer `/root/ch10_edge_probe`: scoped PASS for the staging-to-Core migration.
A04 retains every command and theorem header/context record. CH10 changes only
its A04 import path and the dependent context hashes; all theorem-header and
other command hashes are preserved. Proof bodies and namespaces are unchanged.
The two sources and exact companions move to Core; aggregators add/remove exactly
the matching imports. The full-source Core lock extends by two files, retaining
all fourteen earlier source hashes. The preliminary CH10 hash in the review
was before its remaining proofs were integrated; final hashes below are authoritative.

## Fresh promoted evidence

- `make ci`: 69 guard tests pass, strict interface guard verifies 616 statements
  and 478 commands, Core guard verifies 16 complete modules, both builds pass.
- Direct `lake env lean -DwarningAsError=true` compilation of each promoted source:
  zero warnings and zero errors. No `sorry` or `admit` token remains in either source.
- Fresh `#print axioms` through the built `Bosonize` aggregator covers all
  37 new theorem proofs and six data definitions. Each depends only on
  `propext`, `Classical.choice`, `Quot.sound`, or no axioms. No `sorryAx`/custom axiom.
- Native Lean MCP diagnostics for promoted CH10: success=true, partial=false,
  zero items, zero failed dependencies.
- The fourteen task-start Core sources retain their exact hashes.

The installed compiler determines proof validity. Guards certify preserved
interfaces/source bytes; the independent review and proofs establish separate evidence.
Native tools were available and used. Requested Flash/Pro provider tools were unavailable;
the available inherited Codex models supplied drafting/review/proof groups.

## Pedagogical synchronization

The complementary CH10 lecture and A04 support note are being synchronized against
these final proved sources. Reference information must remain intact, and the new
constructive account must retain carriers, signs, margins, twist scope and future-work labels.
Final independent prose review and Markdown/KaTeX validation are recorded below
before the promotion checkpoint is declared complete.

## Final independent pedagogical review and checkpoint

Author `/root/ch10_pedagogical_sync`; independent reviewer `/root`: PASS against the task-start notes and final proved sources. CH10 retains the original reference text verbatim and adds its constructive lecture. A04 updates only five stale status passages and adds the current-margin explanation; all partition/Gram/completeness/Sugawara reference information remains visible and explicitly pending. One precision correction describes the exported word theorem as a signed shifted budget bound rather than an exported exact-grading theorem. Final prose preserves signs, useful M1 versus M2, both-endpoint blocking, signed negative budgets, right-suffix order, twist versus cyclic-wrap scope, and nonzero witnesses.

KaTeX 0.16.22 parses all 3,067 math fragments across the 34-note inventory, with zero errors and zero delimiter issues. Markdown whitespace checks and local source/companion links pass. Exact companion source snapshots match promoted sources.

Final source hashes:

- `A04CurrentMargins.lean`: `48119166b886ffd0a92c79111570142d931467d089aa1e777c1bab9b466ffd16`
- `Ch10Heisenberg.lean`: `b60b521055ca01363a033e227f473e9bb51a21abc58d92fc668d1ab5c49af735`

Phase C is complete. CH11 is next and has not started. At 2026-10-10T19:27:19-03:00, account allowance was 64% remaining five-hour and 4% weekly. The weekly threshold is crossed; no new chapter/proof batch is started. Reported window reset times: five-hour 2026-10-11T00:14:18-03:00; weekly 2026-10-14T00:29:58-03:00. No credits/reset allowance were purchased or spent. No new continuation is scheduled.
