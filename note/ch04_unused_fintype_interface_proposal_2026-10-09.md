# CH04 unused Fintype interface cleanup proposal — 2026-10-09

Status: **approved by the user, applied, and revalidated**. All 69 CH04/A02 lemmas are proved against approved interface baseline `7a2da78`. CH04's original section includes `[Fintype ι]` in count/sign theorem signatures even though their occupation input is a finite set and only the total order is needed. The original compiler run reported seven unused-section-variable warnings; the approved source now has none. Phase C requires zero warnings, and the locked interface cannot be changed silently.

## Exact approved change

The applied [review patch](ch04_unused_fintype_interface_proposal_2026-10-09.patch) prefixes the 14 count/sign lemmas below with:

```lean
omit [Fintype ι] in
```

The first seven warning locations are direct proof implementations. Several remaining helpers previously consumed the same redundant instance through calls to those lemmas. Omitting only the seven warned binders exposes unused-instance warnings in their dependents. The coherent cleanup removes it from the entire 14-lemma count/sign layer. The operator layer still requires `[Fintype ι]` for its finite Euclidean carrier.

- `Bosonize.Ch04.preceding_count_empty`
- `Bosonize.Ch04.preceding_count_insert`
- `Bosonize.Ch04.preceding_count_erase`
- `Bosonize.Ch04.preceding_count_insert_self`
- `Bosonize.Ch04.preceding_count_erase_self`
- `Bosonize.Ch04.fermion_sign_empty`
- `Bosonize.Ch04.fermion_sign_ne_zero`
- `Bosonize.Ch04.fermion_sign_square`
- `Bosonize.Ch04.fermion_sign_conj`
- `Bosonize.Ch04.fermion_sign_insert_self`
- `Bosonize.Ch04.fermion_sign_erase_self`
- `Bosonize.Ch04.sign_insert_insert`
- `Bosonize.Ch04.sign_erase_erase`
- `Bosonize.Ch04.sign_insert_erase`

All conclusions, explicit membership/distinctness hypotheses, definitions, proof bodies, imports, operators, and Core sources are unchanged. These 14 theorem APIs become more general by dropping an unused implicit instance; this is an interface change even though the mathematical conclusions are preserved. No linter is suppressed and no dummy use of the instance is introduced.

## Validation of the proposal

- A complete temporary candidate outside guarded source directories compiles with `lake env lean -DwarningAsError=true` and empty diagnostics.
- Parsing both variants verifies identical ordered non-lemma commands and exactly 14 changed theorem headers. The other 37 CH04 theorem headers and all 18 A02 headers are unchanged.
- Before application, the patch passed `git apply --check --unidiff-zero`; after application it passes the corresponding reverse check.
- The approved cleanup is now in `BosonizeStubs/`. Only its 14 theorem records were migrated; all other lock records, ordered non-lemma commands, definitions, proofs and Core hashes are preserved. Both modules pass fresh warning-as-error compilation and complete native MCP diagnostics with empty items. All 69 theorem axiom audits use only standard axioms; strict guards, 69 guard tests and both builds pass. Use the cleanup commit containing this record and manifest as the new baseline; `7a2da78` remains historical.

## Approval and subsequent action

The user approved this exact patch and its lock migration. That approval authorizes applying the 14 scoped prefixes, updating only their reviewed header records in the v2 manifest, committing a new approved baseline, and repeating strict guards, warning-as-error compilation, native MCP diagnostics and all 69 axiom audits. Preserve every other lock record and all complete Core hashes. Approval of the cleanup alone does not authorize Phase C promotion.

This is a local interface cleanup discovered by proof compilation, not a shared mathematical failure or a dedicated cross-chapter issue sprint.

The review patch contains only the 14 inserted prefixes (zero context). Its pre-cleanup source SHA-256 was `b1c2959acc2935a51c1dfb9a07fcf272bb15c9632acf0f8e7090d93026103117`. Use `git apply --reverse --check --unidiff-zero note/ch04_unused_fintype_interface_proposal_2026-10-09.patch` to verify the applied patch against the current source.
