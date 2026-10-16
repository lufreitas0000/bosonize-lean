# CH20 Phase A recovery checkpoint — October 16, 2026

## Scope and evidence inspected

The CH20 Phase A source guidance is present at
`docs/webllm/guidance/ch20_phase_a_sources.md` (SHA-256
`f52d501a08c032d96ee9d9384b77604b2d8e00da6cd8143e074aecf60db6045f`). It is
explicitly a proposal, says no Lean code was compiled for it, and defers the
A08-dependent formal-series/state obligations to a separate CH20b package.
The current mathematical source `notes/md/ch20_CDW.md` has SHA-256
`29a1016437b6fbc310c455fec6d15c1216e16b048eb12c34885b647deca87f78`.

The reported reviewed 48-contract/30-data Phase A interface is not present in
the current checkout: there is no `BosonizeStubs/Ch20*.lean`, matching companion,
`docs/webllm/drafts/ch20*` artifact, CH20 chapter record, review report, or v2
stub-lock entry. Searching available Git history for the expected CH20 staging,
companion, draft, and review paths found no commit containing them. The roadmap's
prior status therefore could not be verified against a live artifact.

The only tracked Lean sketch, `notes/draft-lean-code/ch20-draft-gemini-pro.txt`,
has SHA-256 `e0eb4977d7605e141f69905d4f59796454da83b9ad4b25c7eb5bc748c78cf1bd`.
It contains 12 theorem/lemma declarations and 19 `sorry` tokens, imports a
nonexistent A08 staging module, uses `True` for several targets, has residual
lemmas disconnected from the actual fields, and conflates carriers. The live
source guidance itself documents these as rejected patterns. It is not a valid
Phase A or review baseline.

## Phase boundary and next action

The formalizer workflow requires an external Phase A drafter, then an independent
mathematical/interface review before establishing locks. The user authorized no
paid-provider calls, desktop/Antigravity subagents, or other credit pools. No
provider or credit-pool call was made. The remaining repository-approved path
under that constraint is to prepare and return a bounded human-browser packet;
the human-operated browser response and independent review artifact must then be
returned to this checkout for local elaboration and review. Phase B, CH20b, and
CH21 must remain downstream of that accepted interface.

No CH20 Lean source, lock, companion, or chapter note was altered here. The
roadmap was corrected to mark Phase A as awaiting recovery. The unrelated dirty
LaTeX, Markdown, and rule-file changes present before this checkpoint were left
untouched.
