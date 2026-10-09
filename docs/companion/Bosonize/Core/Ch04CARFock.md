# Chapter 4 occupation-CAR lab notebook

Status (2026-10-09): **Phase C complete; proved and frozen in Core.** Lean module: `Bosonize/Core/Ch04CARFock.lean`.

## Scope, review and source reconciliation

The user authorized Phase A for CH04 and the finite-CAR portion of A02 on 2026-10-09. This initial draft was unlocked and unproved; the user subsequently approved Phase B for both modules. Its initial reviewed interface was locked at `7a2da78`; the approved count/sign cleanup was committed at `ddf9548`. All 69 proofs are complete and have now been promoted after Phase C authorization. The historical Phase A evidence below is retained separately from the current Phase B audit. The source baseline at task start is `648c076abe7f82061c29e01f8fb5f7f561d2a70b`. Frozen CH01–CH03 and A01 are preserved. The roadmap controls current status; the dated completion ledger still records its older Fourier readiness checkpoint.

Read [CH04](../../../../notes/md/ch04_CAR_Fock_space.md), [A02](../../../../notes/appendices/a02_car_hilbert_and_normal_ordering.md), [TOC](../../../../notes/md/TOC.md), [source audit](../../../../docs/audit/reference_notes_lean_audit.md), [proof corrections](../../../../note/proof_suggestions_revision_2026-10-09.md), and [completion ledger](../../../../note/notes_review_completion_2026-10-09.md). No CH04/A02-specific file exists in `docs/stub_suggestion/` or `docs/proof_suggestion/`; inline strategies and the reviewed corrections are advisory. Three older CH01–CH03 suggestion files changed concurrently during drafting; those unrelated edits are preserved and excluded from this checkpoint.

Adopt the Euclidean carrier and occupation basis from the notes, basis construction via `Module.Basis.constr`, additive erasure counts, actual Hilbert adjoints, and a fixed ordered parity product. Adapt the abstract CAR contract into an algebraic structure and a separate finite Hilbert structure. Reject the withdrawn generic four-factor commutator formula (A=C=1 yields the wrong coefficient); use the CAR-specific bilinear commutator. Do not install symmetric CAR swaps as simp rules or infer an algebraic CAR pair is adjoint compatible.

Deferred: A02 polynomial Hermitian forms, raw words/normal symbols, Wick reduction, sea-Wick quartic corrections, CH06 local algebras/graded words/matrix units, and CH07 budgets. No compression, energy margin, lattice-evenness, or nonempty mode assumption is needed for this generic finite occupation model. The empty mode type has one occupation configuration, the empty set; creation witnesses take a mode `i`, so they do not claim modes exist in that edge case. Species later require an explicitly chosen lexicographic total order.

## Phase A validation (historical checkpoint)

- `lake build Bosonize` passes with unchanged Core. `lake build BosonizeStubs` passes with exactly 69 expected declaration-uses-sorry warnings (18 A02, 51 CH04). Fresh direct `lake env lean` checks have the same expected warnings and no errors or other warnings. No diagnostic/linter suppression was added.
- All 18 definitions/abbreviations and both structures elaborate without placeholders. A fresh definition/constructor/projection audit checks 23 names with only `propext`, `Classical.choice`, `Quot.sound`, and no `sorryAx`. This proves the definitions do not consume stub proofs, not the CAR identities themselves.
- Every one of the 69 proposed lemma bodies is exactly `:= by sorry`. Fresh theorem-axiom inspection exposes `sorryAx` in the stubs; theorem proofs remain outstanding. No definition, structure or instance body contains `sorry` or `admit`.
- Native Lean MCP diagnostics return full results, no errors or failed dependencies, and only the 18/51 expected `sorry` warnings. `lean_local_search` fails because its server PATH lacks `rg`; shell `rg` and direct compiler checks supplied declaration retrieval. This does not affect the successful diagnostic checks.
- Installed APIs checked directly: `EuclideanSpace.basisFun`, `.toBasis`, `Module.Basis.constr` with scalar argument `ℂ`, `WithLp.linearEquiv`, and finite-dimensional `LinearMap.adjoint`. Scratch checks elaborate `FockSpace Empty`, `ket ∅` over empty modes, creation over `Fin 1`, and parity over `Fin 0`.
- An independent temporary exact integer-coefficient occupation calculation passes 7,761 checks for 0–4 modes: insert/erase counts and sign relations, concrete CAR, adjoint matrix coefficients, number action, and bilinear commutators. Finite checks are sanity evidence, **not** Lean proofs for arbitrary finite mode types.
- All 69 existing guard regression tests pass. `core_lock.py --baseline-ref 648c076` verifies the four original complete-source hashes. Non-strict interface verification against `648c076` verifies all 113 existing statements and 102 commands, with warnings naming exactly the two new drafts. **Strict verification fails exactly on those two unreviewed files**, as required before interface approval. Consequently `make ci` and `make lock-check` are not reported as passing for this unlocked Phase A state.
- All manifests and existing Core source bytes remain unchanged. Review these exact definitions and statements; after explicit approval, establish and commit the reviewed lock before Phase B. Do not regenerate the lock to conceal a failure or start proofs from a successful staging build.

## Concrete definitions and type choices

Namespace `Bosonize.Ch04`. Eight complete definitions and 51 proved lemmas. The operator carrier uses a finite linearly ordered mode type `[Fintype ι] [LinearOrder ι]`; the order supplies decidable equality and comparisons. The Phase A section declaration also automatically included `[Fintype ι]` in count/sign theorem signatures. Phase B compilation revealed that this instance is unnecessary for that layer; the approved cleanup now omits it from all 14 count/sign lemma signatures. The chosen order is part of the fermionic phase convention.

| Definition | Meaning |
| --- | --- |
| `precedingCount i S` | Cardinality of occupied modes j with j<i. |
| `fermionSign i S` | Complex scalar (-1) raised to that natural count. |
| `creation i` | Basis extension: zero if i∈S, otherwise sign(i,S) times ket(insert i S). |
| `annihilation i` | Basis extension: sign(i,S) times ket(S.erase i) if i∈S, otherwise zero. |
| `number i` | Creation followed by annihilation: c†ᵢ cᵢ. |
| `totalNumber` | Finite sum of mode number operators. |
| `parity` | Ascending sorted list product of I−2nᵢ; ambient multiplication is not assumed commutative. |
| `hopping i j` | c†ᵢ cⱼ, with annihilation on the right acting first. |

All operators act on the same `A02.FockSpace ι`. No representation structure with unproved fields is hidden inside the operator definitions. `concrete_car_exists` now proves existence of a finite Hilbert CAR representation with these exact maps, using the proved CAR and adjoint lemmas.

## Phase A proof plan (historical)

1. **A02 basis bridges**, especially evaluation, inner product, nonzero kets, map extensionality and the adjoint pairing criterion.
2. **Atomic counts/signs**: insertion with j∉S and additive erasure with j∈S; same-mode count/sign invariance; sign square and conjugation. The insert/insert, erase/erase and mixed insert/erase helper hypotheses describe exactly the nonzero branches for distinct modes. Keep the membership conditions rather than deriving a sign relation on forbidden branches.
3. **Concrete basis actions and witnesses**: creation/annihilation evaluation, empty occupation action, creation on vacuum and annihilation on singleton nonzero. These proposed witnesses guard against trivial zero operators, but remain unproved in Phase A.
4. **Nilpotency, CAR, adjoints**: split coincident/distinct mode indices and occupied/empty configurations. Lift from basis actions with `end_ext_basis`. For adjointness, prove the basis-pair equation with conjugation in the first slot, then apply the A02 bridge. Establish both adjoint directions and `concrete_car_exists` only after those proofs.
5. **Diagonal observables/parity**: number action and idempotency, actual adjoints, pairwise number commutativity, total-number action, and parity action on kets. Derive parity square/self-adjointness and oddness of creation/annihilation from those actions; the sorted list fixes the defining order.
6. **Bilinears and hops**: reuse A02 pure-CAR algebra after obtaining the concrete CAR witness. Prove local/total number commutators, hopping basis action, blocked cases, diagonal identity and actual hopping adjoint.

## Sign, adjoint and edge contracts

`preceding_count_erase` states oldCount = erasedCount + indicator(j<i), avoiding natural subtraction. The hopping coefficient is sign(j,S) * sign(i,S.erase j), exactly matching the right-to-left action. The blocked-hop condition permits j∉S, or i≠j with i already occupied; i=j is handled by `hopping_diagonal`, so occupied diagonal hops are not accidentally claimed zero.

The mixed CAR target uses a scalar Kronecker indicator times the identity endomorphism. The adjoint basis equation is ⟨δS,cᵢ δT⟩=⟨c†ᵢ δS,δT⟩, with actual finite Hilbert adjoints. The bilinear identity preserves the corrected signs δbc c†a cd − δad c†c cb. Parity uses an explicit ascending list, never `Finset.prod` on an arbitrary noncommutative ring.

No lattice length, half filling or energy margin enters this generic chapter. Empty-mode dimension/vacuum contracts belong to A02; when a mode is supplied, singleton witnesses are available as proposed stubs. No true-for-all-modes conclusion is inferred from the finite sanity checks. All 51 proofs and their 18 A02 dependencies are now complete. The approved unused-instance cleanup is complete; Phase C audit and promotion are now complete.

## Exact theorem inventory

All names below now have complete proofs. Exact binder types, statements, and proofs appear in the source snapshot.

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
- `Bosonize.Ch04.creation_ket`
- `Bosonize.Ch04.annihilation_ket`
- `Bosonize.Ch04.creation_vacuum`
- `Bosonize.Ch04.annihilation_vacuum`
- `Bosonize.Ch04.creation_vacuum_ne_zero`
- `Bosonize.Ch04.annihilation_singleton`
- `Bosonize.Ch04.annihilation_singleton_ne_zero`
- `Bosonize.Ch04.creation_square`
- `Bosonize.Ch04.annihilation_square`
- `Bosonize.Ch04.creation_adjoint_pairing`
- `Bosonize.Ch04.creation_eq_adjoint`
- `Bosonize.Ch04.annihilation_eq_adjoint`
- `Bosonize.Ch04.annihilation_car`
- `Bosonize.Ch04.creation_car`
- `Bosonize.Ch04.mixed_car`
- `Bosonize.Ch04.concrete_car_exists`
- `Bosonize.Ch04.number_ket`
- `Bosonize.Ch04.number_idempotent`
- `Bosonize.Ch04.number_adjoint`
- `Bosonize.Ch04.number_commute`
- `Bosonize.Ch04.total_number_ket`
- `Bosonize.Ch04.total_number_adjoint`
- `Bosonize.Ch04.parity_ket`
- `Bosonize.Ch04.parity_square`
- `Bosonize.Ch04.parity_adjoint`
- `Bosonize.Ch04.parity_vacuum`
- `Bosonize.Ch04.parity_creation`
- `Bosonize.Ch04.parity_annihilation`
- `Bosonize.Ch04.bilinear_commutator`
- `Bosonize.Ch04.number_creation_commutator`
- `Bosonize.Ch04.number_annihilation_commutator`
- `Bosonize.Ch04.total_number_creation_commutator`
- `Bosonize.Ch04.total_number_annihilation_commutator`
- `Bosonize.Ch04.hopping_ket`
- `Bosonize.Ch04.hopping_blocked`
- `Bosonize.Ch04.hopping_diagonal`
- `Bosonize.Ch04.hopping_adjoint`

## Source provenance

These hashes identify the consulted snapshots; they do not certify mathematical correctness.

| Source | SHA-256 |
| --- | --- |
| `notes/md/ch04_CAR_Fock_space.md` | `dccd43890181e7acbb10ff4c94fdbe51a1e671ae829c64c5515b4f74e19d826f` |
| `notes/appendices/a02_car_hilbert_and_normal_ordering.md` | `1dfcf6960585d2871bfa92a305d299f94f5880d93775ae0e64d121ec46b55556` |
| `notes/md/TOC.md` | `5ea6b32bdecf8f9c65a345dc12356ff767b176c0b131e32acdb836778b054977` |
| `docs/audit/reference_notes_lean_audit.md` | `35245d3a8ed87e5ed1f31947132fb272848cfc8ff83236af49c9c45dc0bb4877` |
| `note/proof_suggestions_revision_2026-10-09.md` | `1db5f28b3e392d3b400ccc219ac640778fc5ceabc5cba17dfeb44b225a1b383c` |
| `note/notes_review_completion_2026-10-09.md` | `ee96609b0c32346be604041a99e3345c3420b71c830c88ef83ff8d93bd9c1dc1` |

## Definition axiom evidence

Historical Phase A audit output for data in this namespace. Phase B freshly rechecked these declarations with only standard axioms; all theorem proofs are now complete.

```text
'Bosonize.Ch04.precedingCount' depends on axioms: [propext, Quot.sound]
'Bosonize.Ch04.fermionSign' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.creation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.annihilation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.number' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.totalNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.parity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.hopping' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Phase B proof completion and validation — 2026-10-09

The user approved Phase B for CH04 and finite-CAR A02. Initial locking added only the two reviewed Phase A entries to `stub_locks.v2.json`; every prior entry stayed identical. The approved baseline is `7a2da78`. Proof work changed only lemma bodies; no public helper, definition, import, namespace, theorem header, attribute, or hypothesis was changed. Original Phase A module comments are retained as part of the frozen source context; this notebook records the current completion state.

All 51 CH04 lemmas are proved. Atomic signs follow the additive count identities and the two possible orders of distinct modes. Concrete CAR is proved on occupation kets, with membership cases and exact set-operation/sign cancellation; adjoints follow the basis-pair criterion. `concrete_car_exists` now constructs the actual finite Hilbert CAR witness from these proved identities, rather than introducing an assumed representation. Number action is diagonal, and parity is proved by induction over the defining ordered list, transporting only its scalar eigenvalues to a commutative finite product. Oddness, number commutators, and hopping identities then follow from those exact actions and the reusable A02 algebra.

Before the approved cleanup, `lake env lean BosonizeStubs/Ch04CARFock.lean` exited 0, with no errors or placeholders and exactly seven unused-section-variable warnings for the locked `[Fintype ι]` assumption:

- `preceding_count_empty`
- `preceding_count_insert`
- `preceding_count_insert_self`
- `preceding_count_erase_self`
- `fermion_sign_ne_zero`
- `fermion_sign_square`
- `fermion_sign_conj`

Before cleanup, native MCP independently reported those same seven linter warnings, with no errors, failed dependencies, timeout, or partial result. Goal retrieval on `parity_square` shows the product of the two scalar powers becoming the power of `(-1)*(-1)`, before the final simplification closes the proof.

The user approved the [exact interface cleanup](../../../../note/ch04_unused_fintype_interface_proposal_2026-10-09.md). Its 14 scoped `omit [Fintype ι] in` prefixes and only the corresponding lock records are applied. Definitions, proof bodies, conclusions and the finite operator carrier are unchanged. Both modules now compile with warnings treated as errors and empty diagnostics; no linter was suppressed.

Historical pre-cleanup validation (baseline `7a2da78`):

- `STUB_LOCK_BASELINE_REF=7a2da78 make ci` passes all 69 guard tests, 182 frozen statements, 152 frozen commands, four complete Core source hashes, and both library builds. The staging build allows the seven reported CH04 linter warnings; passing CI is not a warning-free promotion result.
- Strict committed-baseline verification passes. All existing Core bytes, all manifests after the approved initial lock, the toolchain, and the dependency manifest remain unchanged throughout proof work.
- All 69 A02/CH04 lemmas freshly audited through `import BosonizeStubs` use only subsets of `propext`, `Classical.choice`, `Quot.sound`. Zero `sorryAx`, extra axioms, or placeholder proof tokens remain. A fresh data/constructor/projection audit also uses only standard axioms.
- At that historical Phase B checkpoint, the exact source snapshot matched staging and Phase C had not been authorized. The current source snapshot below records the authorized Core promotion.
- Declaration search's previously observed missing-`rg` limitation was handled by installed-source `rg`/compiler inspection. Native diagnostic and goal tools worked; a search-tool failure is not reported as total MCP/LSP unavailability.

## Approved interface cleanup validation — 2026-10-09

The user approved the 14 CH04 count/sign prefixes and their lock-record migration. Only those theorem records changed; all other records and complete Core hashes are preserved. Fresh warning-as-error compilation of both staging modules exits 0 with empty output. Native MCP diagnostics for both modules are complete, successful and empty, with no failed dependencies or timeout. Fresh axiom inspection of all 69 lemmas permits only `propext`, `Classical.choice`, `Quot.sound`. Strict guards, 69 guard tests and both library builds pass against the approved cleanup manifest. That cleanup baseline is `ddf9548`. Both modules were still in staging at that checkpoint; the authorized Phase C migration is recorded below.

## Phase C audit, promotion and freeze — 2026-10-09

The user authorized Phase C after the approved cleanup checkpoint `ddf9548`. Both modules are now exposed through `import Bosonize` in Core. A02 source and its entire interface entry move unchanged. CH04 changes only its dependency import from `BosonizeStubs.A02CARHilbert` to `Bosonize.Core.A02CARHilbert`; its theorem hashes and proof bodies are unchanged, and only the import command and dependent context hashes migrate. All four prior Core source hashes and all unrelated interface entries are unchanged. The v1 manifest remains historical.

Fresh warning-as-error compilation of both promoted sources exits 0 with empty output. Native Lean MCP diagnostics are successful, complete and empty for both Core paths; goal retrieval at `parity_square` confirms the final simplification closes the proof. A fresh audit through `import Bosonize` checks all 182 Core lemmas, including these 69, using only subsets of `propext`, `Classical.choice`, `Quot.sound`. No placeholder proof tokens or additional axioms remain. CI passes all 69 guard tests, 182 statements, 152 commands, six complete-source hashes and both library builds; `make lock-check` passes both guards.

Use the committed Phase C checkpoint containing these promoted paths and manifests (or a later approved checkpoint) for committed-baseline checks. `ddf9548` is retained as the historical pre-promotion interface baseline. Core now freezes the complete proof source. The scope is finite-CAR A02; its polynomial Hermitian forms, normal symbols and Wick work remain deferred.

## Fresh theorem axiom audit

```text
'Bosonize.Ch04.annihilation_car' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.annihilation_eq_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.annihilation_ket' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.annihilation_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.annihilation_singleton_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.annihilation_square' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.annihilation_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.bilinear_commutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.concrete_car_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.creation_adjoint_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.creation_car' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.creation_eq_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.creation_ket' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.creation_square' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.creation_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.creation_vacuum_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.fermion_sign_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.fermion_sign_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.fermion_sign_erase_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.fermion_sign_insert_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.fermion_sign_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.fermion_sign_square' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.hopping_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.hopping_blocked' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.hopping_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.hopping_ket' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.mixed_car' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.number_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.number_annihilation_commutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.number_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.number_creation_commutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.number_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.number_ket' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.parity_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.parity_annihilation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.parity_creation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.parity_ket' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.parity_square' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.parity_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.preceding_count_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.preceding_count_erase' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.preceding_count_erase_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.preceding_count_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.preceding_count_insert_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.sign_erase_erase' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.sign_insert_erase' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.sign_insert_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.total_number_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.total_number_annihilation_commutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.total_number_creation_commutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch04.total_number_ket' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Exact Lean source snapshot

This block matches the current approved source byte-for-byte, including its final newline. All lemma bodies are proved; definitions and statements retain their approved freeze.

Module SHA-256: `8be8dacb9212e7535e1fa7357398bb5b6a7cae6188d6d8643be6548d0ec422e0`.

```lean
module

public import Bosonize.Core.A02CARHilbert

/-!
# CH04: concrete finite occupation CAR
Phase A: basis-extension operators are complete; every lemma is an unproved review stub.
No budget compression or Wick ordering is introduced.
-/

@[expose] public section

namespace Bosonize.Ch04

open scoped BigOperators ComplexConjugate

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Number of occupied modes strictly preceding i in the chosen total order. -/
def precedingCount (i : ι) (S : A02.Occupation ι) : ℕ := (S.filter (· < i)).card

def fermionSign (i : ι) (S : A02.Occupation ι) : ℂ := (-1 : ℂ) ^ precedingCount i S

noncomputable def creation (i : ι) : Module.End ℂ (A02.FockSpace ι) :=
  A02.extendBasis fun S =>
    if i ∈ S then 0 else fermionSign i S • A02.ket (insert i S)

noncomputable def annihilation (i : ι) : Module.End ℂ (A02.FockSpace ι) :=
  A02.extendBasis fun S =>
    if i ∈ S then fermionSign i S • A02.ket (S.erase i) else 0

noncomputable def number (i : ι) : Module.End ℂ (A02.FockSpace ι) :=
  creation i * annihilation i

noncomputable def totalNumber : Module.End ℂ (A02.FockSpace ι) := ∑ i : ι, number i

/-- Ascending ordered product, since the ambient endomorphism ring is noncommutative. -/
noncomputable def parity : Module.End ℂ (A02.FockSpace ι) :=
  ((Finset.univ : Finset ι).sort (· ≤ ·)).map
    (fun i => 1 - (2 : ℂ) • number i) |>.prod

noncomputable def hopping (i j : ι) : Module.End ℂ (A02.FockSpace ι) :=
  creation i * annihilation j

omit [Fintype ι] in
lemma preceding_count_empty (i : ι) : precedingCount i ∅ = 0 := by
  simp [precedingCount]

omit [Fintype ι] in
lemma preceding_count_insert (i j : ι) (S : A02.Occupation ι) (hj : j ∉ S) :
    precedingCount i (insert j S) = precedingCount i S + if j < i then 1 else 0 := by
  classical
  by_cases hji : j < i
  · simp [precedingCount, Finset.filter_insert, hji, hj]
  · simp [precedingCount, Finset.filter_insert, hji]

omit [Fintype ι] in
lemma preceding_count_erase (i j : ι) (S : A02.Occupation ι) (hj : j ∈ S) :
    precedingCount i S = precedingCount i (S.erase j) + if j < i then 1 else 0 := by
  have h := preceding_count_insert i j (S.erase j) (Finset.notMem_erase j S)
  simpa [Finset.insert_erase hj] using h

omit [Fintype ι] in
lemma preceding_count_insert_self (i : ι) (S : A02.Occupation ι) :
    precedingCount i (insert i S) = precedingCount i S := by
  simp [precedingCount, Finset.filter_insert]

omit [Fintype ι] in
lemma preceding_count_erase_self (i : ι) (S : A02.Occupation ι) :
    precedingCount i (S.erase i) = precedingCount i S := by
  simp [precedingCount, Finset.filter_erase, Finset.erase_eq_of_notMem]

omit [Fintype ι] in
lemma fermion_sign_empty (i : ι) : fermionSign i ∅ = 1 := by
  simp [fermionSign, preceding_count_empty]

omit [Fintype ι] in
lemma fermion_sign_ne_zero (i : ι) (S : A02.Occupation ι) : fermionSign i S ≠ 0 := by
  exact pow_ne_zero _ (by norm_num)

omit [Fintype ι] in
lemma fermion_sign_square (i : ι) (S : A02.Occupation ι) :
    fermionSign i S * fermionSign i S = 1 := by
  unfold fermionSign
  rw [← mul_pow]
  simp

omit [Fintype ι] in
lemma fermion_sign_conj (i : ι) (S : A02.Occupation ι) :
    conj (fermionSign i S) = fermionSign i S := by
  simp [fermionSign]

omit [Fintype ι] in
lemma fermion_sign_insert_self (i : ι) (S : A02.Occupation ι) :
    fermionSign i (insert i S) = fermionSign i S := by
  simp only [fermionSign, preceding_count_insert_self]

omit [Fintype ι] in
lemma fermion_sign_erase_self (i : ι) (S : A02.Occupation ι) :
    fermionSign i (S.erase i) = fermionSign i S := by
  simp only [fermionSign, preceding_count_erase_self]

omit [Fintype ι] in
lemma sign_insert_insert (i j : ι) (S : A02.Occupation ι)
    (hij : i ≠ j) (hi : i ∉ S) (hj : j ∉ S) :
    fermionSign j S * fermionSign i (insert j S) =
      -(fermionSign i S * fermionSign j (insert i S)) := by
  have hci := preceding_count_insert i j S hj
  have hcj := preceding_count_insert j i S hi
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · simp only [fermionSign, hci, hcj, ite_eq_right (not_lt_of_gt hlt), ite_eq_left hlt, add_zero, pow_succ]
    ring
  · simp only [fermionSign, hci, hcj, ite_eq_left hgt, ite_eq_right (not_lt_of_gt hgt), add_zero, pow_succ]
    ring

omit [Fintype ι] in
lemma sign_erase_erase (i j : ι) (S : A02.Occupation ι)
    (hij : i ≠ j) (hi : i ∈ S) (hj : j ∈ S) :
    fermionSign j S * fermionSign i (S.erase j) =
      -(fermionSign i S * fermionSign j (S.erase i)) := by
  have hci := preceding_count_erase i j S hj
  have hcj := preceding_count_erase j i S hi
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · simp only [ite_eq_right (not_lt_of_gt hlt), ite_eq_left hlt, add_zero] at hci hcj
    simp only [fermionSign, hci, hcj, pow_succ]
    ring
  · simp only [ite_eq_left hgt, ite_eq_right (not_lt_of_gt hgt), add_zero] at hci hcj
    simp only [fermionSign, hci, hcj, pow_succ]
    ring

omit [Fintype ι] in
lemma sign_insert_erase (i j : ι) (S : A02.Occupation ι)
    (hij : i ≠ j) (hi : i ∉ S) (hj : j ∈ S) :
    fermionSign j S * fermionSign i (S.erase j) =
      -(fermionSign i S * fermionSign j (insert i S)) := by
  have hci := preceding_count_erase i j S hj
  have hcj := preceding_count_insert j i S hi
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · simp only [ite_eq_right (not_lt_of_gt hlt), ite_eq_left hlt, add_zero] at hci hcj
    simp only [fermionSign, hci, hcj, pow_succ]
    ring
  · simp only [ite_eq_left hgt, ite_eq_right (not_lt_of_gt hgt), add_zero] at hci hcj
    simp only [fermionSign, hci, hcj, pow_succ]
    ring

lemma creation_ket (i : ι) (S : A02.Occupation ι) :
    creation i (A02.ket S) =
      if i ∈ S then 0 else fermionSign i S • A02.ket (insert i S) := by
  exact A02.extend_basis_ket _ S

lemma annihilation_ket (i : ι) (S : A02.Occupation ι) :
    annihilation i (A02.ket S) =
      if i ∈ S then fermionSign i S • A02.ket (S.erase i) else 0 := by
  exact A02.extend_basis_ket _ S

lemma creation_vacuum (i : ι) : creation i (A02.ket ∅) = A02.ket {i} := by
  simp [creation_ket, fermion_sign_empty]

lemma annihilation_vacuum (i : ι) : annihilation i (A02.ket ∅) = 0 := by
  simp [annihilation_ket]

lemma creation_vacuum_ne_zero (i : ι) : creation i (A02.ket ∅) ≠ 0 := by
  rw [creation_vacuum]; exact A02.ket_ne_zero {i}

lemma annihilation_singleton (i : ι) : annihilation i (A02.ket {i}) = A02.ket ∅ := by
  have hs : fermionSign i ({i} : A02.Occupation ι) = 1 := by
    simpa [fermion_sign_empty] using fermion_sign_insert_self i (∅ : A02.Occupation ι)
  simp [annihilation_ket, hs]

lemma annihilation_singleton_ne_zero (i : ι) : annihilation i (A02.ket {i}) ≠ 0 := by
  rw [annihilation_singleton]; exact A02.vacuum_ne_zero

lemma creation_square (i : ι) : creation i * creation i = 0 := by
  apply A02.end_ext_basis
  intro S
  simp only [Module.End.mul_apply, LinearMap.zero_apply, creation_ket]
  by_cases hi : i ∈ S
  · simp [hi]
  · simp [hi, map_smul, creation_ket]

lemma annihilation_square (i : ι) : annihilation i * annihilation i = 0 := by
  apply A02.end_ext_basis
  intro S
  simp only [Module.End.mul_apply, LinearMap.zero_apply, annihilation_ket]
  by_cases hi : i ∈ S
  · simp [hi, map_smul, annihilation_ket]
  · simp [hi]

lemma creation_adjoint_pairing (i : ι) (S T : A02.Occupation ι) :
    inner ℂ (A02.ket S) (annihilation i (A02.ket T)) =
      inner ℂ (creation i (A02.ket S)) (A02.ket T) := by
  simp only [annihilation_ket, creation_ket]
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
  · simp [hiS, hiT, inner_smul_right, A02.ket_inner]
    have hne : S ≠ T.erase i := by intro h; subst S; simp at hiS
    simp [hne]
  · simp [hiS, hiT]
  · simp only [hiS, hiT, ite_true, ite_false, inner_smul_right, inner_smul_left,
      A02.ket_inner, fermion_sign_conj]
    by_cases hST : S = T.erase i
    · subst S
      simp [Finset.insert_erase hiT, fermion_sign_erase_self]
    · have hTS : insert i S ≠ T := by
        intro h
        have he := congrArg (fun U : A02.Occupation ι => U.erase i) h
        exact hST (by simpa [Finset.erase_insert, hiS] using he)
      simp [hST, hTS]
  · simp [hiS, hiT, inner_smul_left, A02.ket_inner]
    have hne : insert i S ≠ T := by intro h; subst T; simp at hiT
    simp [hne]

lemma creation_eq_adjoint (i : ι) : creation i = LinearMap.adjoint (annihilation i) := by
  exact A02.adjoint_of_basis_pairing _ _ (creation_adjoint_pairing i)

lemma annihilation_eq_adjoint (i : ι) : annihilation i = LinearMap.adjoint (creation i) := by
  rw [creation_eq_adjoint, LinearMap.adjoint_adjoint]

lemma annihilation_car (i j : ι) : A02.anticommutator (annihilation i) (annihilation j) = 0 := by
  by_cases hij : i = j
  · subst j; simp [A02.anticommutator, annihilation_square]
  · apply A02.end_ext_basis
    intro S
    simp only [A02.anticommutator, LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply]
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      simp [annihilation_ket, hi, hj, hij, Ne.symm hij, map_smul, smul_smul]
    rw [Finset.erase_right_comm, ← add_smul, sign_erase_erase i j S hij hi hj]
    simp

lemma creation_car (i j : ι) : A02.anticommutator (creation i) (creation j) = 0 := by
  by_cases hij : i = j
  · subst j; simp [A02.anticommutator, creation_square]
  · apply A02.end_ext_basis
    intro S
    simp only [A02.anticommutator, LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply]
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      simp [creation_ket, hi, hj, hij, Ne.symm hij, map_smul, smul_smul]
    rw [Finset.insert_comm, ← add_smul, sign_insert_insert i j S hij hi hj]
    simp

lemma mixed_car (i j : ι) : A02.anticommutator (annihilation i) (creation j) =
    (if i = j then (1 : ℂ) else 0) • (1 : Module.End ℂ (A02.FockSpace ι)) := by
  apply A02.end_ext_basis
  intro S
  simp only [A02.anticommutator, LinearMap.add_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Module.End.one_apply]
  by_cases hij : i = j
  · subst j
    by_cases hi : i ∈ S
    · simp [annihilation_ket, creation_ket, hi, map_smul, smul_smul,
        fermion_sign_erase_self, fermion_sign_square, Finset.insert_erase hi]
    · simp [annihilation_ket, creation_ket, hi, map_smul, smul_smul,
        fermion_sign_insert_self, fermion_sign_square]
  · by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      simp [annihilation_ket, creation_ket, hi, hj, hij, Ne.symm hij, map_smul, smul_smul]
    rw [Finset.erase_insert_of_ne (Ne.symm hij), ← add_smul]
    have hs := sign_insert_erase j i S (Ne.symm hij) hj hi
    rw [hs]
    simp

/-- Proposed existence of the concrete representation, not an assumed CAR instance. -/
lemma concrete_car_exists : ∃ R : A02.CAR ι (A02.FockSpace ι),
    R.annihilation = annihilation ∧ R.creation = creation := by
  exact ⟨{ annihilation := annihilation
           creation := creation
           annihilation_car := annihilation_car
           creation_car := creation_car
           mixed_car := mixed_car
           adjoint_compat := creation_eq_adjoint }, rfl, rfl⟩

lemma number_ket (i : ι) (S : A02.Occupation ι) :
    number i (A02.ket S) = (if i ∈ S then (1 : ℂ) else 0) • A02.ket S := by
  unfold number
  simp only [Module.End.mul_apply, annihilation_ket]
  by_cases hi : i ∈ S
  · simp [hi, map_smul, creation_ket, fermion_sign_erase_self, smul_smul, fermion_sign_square, Finset.insert_erase hi]
  · simp [hi]

lemma number_idempotent (i : ι) : number i * number i = number i := by
  apply A02.end_ext_basis
  intro S
  simp only [Module.End.mul_apply, number_ket, map_smul]
  by_cases hi : i ∈ S <;> simp [hi]

lemma number_adjoint (i : ι) : LinearMap.adjoint (number i) = number i := by
  change LinearMap.adjoint ((creation i).comp (annihilation i)) = (creation i).comp (annihilation i)
  rw [LinearMap.adjoint_comp, ← creation_eq_adjoint, ← annihilation_eq_adjoint]

lemma number_commute (i j : ι) : number i * number j = number j * number i := by
  apply A02.end_ext_basis
  intro S
  simp only [Module.End.mul_apply, number_ket, map_smul, smul_smul]
  congr 1
  exact mul_comm _ _

lemma total_number_ket (S : A02.Occupation ι) :
    totalNumber (ι := ι) (A02.ket S) = (S.card : ℂ) • A02.ket S := by
  simp only [totalNumber, LinearMap.sum_apply, number_ket]
  rw [← Finset.sum_smul]
  congr 1
  simp

lemma total_number_adjoint :
    LinearMap.adjoint (totalNumber (ι := ι)) = totalNumber (ι := ι) := by
  simp [totalNumber, number_adjoint]

lemma parity_ket (S : A02.Occupation ι) :
    parity (ι := ι) (A02.ket S) = (-1 : ℂ) ^ S.card • A02.ket S := by
  have hl : ∀ l : List ι,
      (l.map (fun i => (1 : Module.End ℂ (A02.FockSpace ι)) - (2 : ℂ) • number i)).prod (A02.ket S) =
        (l.map (fun i => if i ∈ S then (-1 : ℂ) else 1)).prod • A02.ket S := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, map_smul,
        LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, number_ket]
      by_cases hi : i ∈ S
      · simp [hi, smul_smul, smul_sub]; module
      · simp [hi]
  unfold parity
  rw [hl, ← List.prod_toFinset _ (Finset.sort_nodup _ _)]
  simp only [Finset.sort_toFinset]
  rw [Finset.prod_ite]
  simp

lemma parity_square : parity (ι := ι) * parity (ι := ι) = 1 := by
  apply A02.end_ext_basis
  intro S
  simp only [Module.End.mul_apply, parity_ket, map_smul, Module.End.one_apply, smul_smul]
  rw [← mul_pow]
  simp

lemma parity_adjoint : LinearMap.adjoint (parity (ι := ι)) = parity (ι := ι) := by
  apply Eq.symm
  apply A02.adjoint_of_basis_pairing
  intro S T
  simp only [parity_ket, inner_smul_right, inner_smul_left, A02.ket_inner]
  by_cases h : S = T
  · subst T; simp
  · simp [h]

lemma parity_vacuum : parity (ι := ι) (A02.ket ∅) = A02.ket ∅ := by
  simp [parity_ket]

lemma parity_creation (i : ι) : parity (ι := ι) * creation i = -(creation i * parity (ι := ι)) := by
  apply A02.end_ext_basis
  intro S
  simp only [Module.End.mul_apply, LinearMap.neg_apply, parity_ket]
  by_cases hi : i ∈ S
  · simp [creation_ket, hi]
  · simp [creation_ket, hi, map_smul, parity_ket, Finset.card_insert_of_notMem hi,
      pow_succ, smul_smul, mul_comm]

lemma parity_annihilation (i : ι) :
    parity (ι := ι) * annihilation i = -(annihilation i * parity (ι := ι)) := by
  apply A02.end_ext_basis
  intro S
  simp only [Module.End.mul_apply, LinearMap.neg_apply, parity_ket]
  by_cases hi : i ∈ S
  · have hcard : S.card = (S.erase i).card + 1 := by
      simpa [Finset.insert_erase hi] using Finset.card_insert_of_notMem (Finset.notMem_erase i S)
    have hp : (-1 : ℂ) ^ S.card = -((-1 : ℂ) ^ (S.erase i).card) := by
      rw [hcard, pow_succ]; ring
    simp only [annihilation_ket, ite_eq_left hi, map_smul, parity_ket, hp, smul_smul]
    module
  · simp [annihilation_ket, hi]

lemma bilinear_commutator (a b c d : ι) :
    A02.commutator (hopping a b) (hopping c d) =
      (if b = c then (1 : ℂ) else 0) • hopping a d -
      (if a = d then (1 : ℂ) else 0) • hopping c b := by
  obtain ⟨R, ha, hc⟩ := concrete_car_exists (ι := ι)
  simpa [hopping, ha, hc] using A02.car_bilinear_commutator R.toAlgebraicCAR a b c d

lemma number_creation_commutator (i j : ι) : A02.commutator (number i) (creation j) =
    (if i = j then (1 : ℂ) else 0) • creation j := by
  obtain ⟨R, ha, hc⟩ := concrete_car_exists (ι := ι)
  simpa [A02.AlgebraicCAR.number, number, ha, hc] using
    A02.car_number_creation_commutator R.toAlgebraicCAR i j

lemma number_annihilation_commutator (i j : ι) : A02.commutator (number i) (annihilation j) =
    -(if i = j then (1 : ℂ) else 0) • annihilation j := by
  obtain ⟨R, ha, hc⟩ := concrete_car_exists (ι := ι)
  simpa [A02.AlgebraicCAR.number, number, ha, hc] using
    A02.car_number_annihilation_commutator R.toAlgebraicCAR i j

lemma total_number_creation_commutator (i : ι) :
    A02.commutator (totalNumber (ι := ι)) (creation i) = creation i := by
  simp only [totalNumber, A02.commutator, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  change (∑ j : ι, A02.commutator (number j) (creation i)) = _
  simp [number_creation_commutator]

lemma total_number_annihilation_commutator (i : ι) :
    A02.commutator (totalNumber (ι := ι)) (annihilation i) = -annihilation i := by
  simp only [totalNumber, A02.commutator, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  change (∑ j : ι, A02.commutator (number j) (annihilation i)) = _
  simp [number_annihilation_commutator]

lemma hopping_ket (i j : ι) (S : A02.Occupation ι) (hij : i ≠ j)
    (hi : i ∉ S) (hj : j ∈ S) :
    hopping i j (A02.ket S) = (fermionSign j S * fermionSign i (S.erase j)) •
      A02.ket (insert i (S.erase j)) := by
  unfold hopping
  simp [Module.End.mul_apply, annihilation_ket, hj, map_smul, creation_ket,
    hi, hij, smul_smul]

lemma hopping_blocked (i j : ι) (S : A02.Occupation ι)
    (h : j ∉ S ∨ (i ≠ j ∧ i ∈ S)) : hopping i j (A02.ket S) = 0 := by
  unfold hopping
  rcases h with hj | ⟨hij, hi⟩
  · simp [Module.End.mul_apply, annihilation_ket, hj]
  · by_cases hj : j ∈ S
    · simp [Module.End.mul_apply, annihilation_ket, hj, map_smul, creation_ket, hi, hij]
    · simp [Module.End.mul_apply, annihilation_ket, hj]

lemma hopping_diagonal (i : ι) : hopping i i = number i := by
  rfl

lemma hopping_adjoint (i j : ι) : LinearMap.adjoint (hopping i j) = hopping j i := by
  change LinearMap.adjoint ((creation i).comp (annihilation j)) = (creation j).comp (annihilation i)
  rw [LinearMap.adjoint_comp, ← creation_eq_adjoint, ← annihilation_eq_adjoint]

end Bosonize.Ch04
```
