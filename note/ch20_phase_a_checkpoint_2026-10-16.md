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

## Original phase boundary

At the initial inspection the formalizer workflow still required an external
Phase A draft and independent mathematical/interface review. The user authorized
no paid-provider calls, desktop/Antigravity subagents, or other credit pools. No
provider or credit-pool call was made. The bounded browser packet was prepared,
and the user supplied its response and matching Markdown download.

## Phase A acceptance — October 16, 2026

- Packet: `ch20_phase_a-20261016T133230Z-dbc49307`; base SHA
  `d555477a75e28da8e75d5e6e88518fdce173c9aa`.
- Final draft SHA-256:
  `d3b89fbbde18a8f2d6a06a7b6779721cd1eb48749615cd9b4e5ca4ec3ff59272`.
- Staging source: `BosonizeStubs/Ch20CDW.lean`; SHA-256
  `77d49a6fe6166d07cdc706a2ab1de0b7a0745882ed0658e6d3ca104cacddb241`.
- Independent reviewer `/root/ch20_phase_a_review` returned PASS for the exact
  final draft hash. The review covered interface mathematics and scope; it did
  not prove any of the stubs. Its provenance finding was resolved by separating
  the empty editable-target baseline hash from the source-hash list.
- The first fresh elaboration found two missing `[Fintype σ] [LinearOrder σ]`
  binders on zero-mode lemmas. Those were added, the candidate was re-elaborated,
  and the exact revised artifact was re-reviewed.
- Fresh `scripts/webllm/verify_phase_a.py` passed: 27 audited data declarations,
  64 unproved theorem stubs, with only expected `sorry` warnings. Data axioms
  were limited to `Classical.choice`, `Quot.sound`, and `propext` (or none).
- `lake build BosonizeStubs` passed at 3420 jobs, including
  `BosonizeStubs.Ch20CDW`; its 64 `sorry` warnings are expected for Phase A.
- `stub_lock.py --check --strict` passed with 1032 statements and 1063 frozen
  commands across 34 files. `core_lock.py` passed for all 33 frozen Core files.
- The exact reviewed interface is now in `docs/webllm/drafts/ch20_phase_a.md`,
  `BosonizeStubs/Ch20CDW.lean`, and
  `docs/companion/BosonizeStubs/Ch20CDW.md`; only its scoped new lock record was
  added. `BosonizeStubs.lean` imports the new staging module.
- The original files in `C:\Users\lucas\Downloads` were not modified.

Phase A is complete. All 64 contracts remain unproved and are eligible for
Phase B under the frozen interface. CH20b, CH21, and the canonical closure audit
remain downstream. The unrelated dirty LaTeX, Markdown, and rule-file changes
listed in the initial checkpoint remain untouched.
