# Chapter 4 occupation-CAR lab notebook

Status (2026-10-09): **Phase A complete; awaiting interface review.** Lean module: `BosonizeStubs/Ch04CARFock.lean`.

## Scope, review and source reconciliation

The user authorized Phase A for CH04 and the finite-CAR portion of A02 on 2026-10-09. This draft is **unlocked and unproved**. The source baseline at task start is `648c076abe7f82061c29e01f8fb5f7f561d2a70b`. Frozen CH01–CH03 and A01 are preserved. The roadmap controls current status; the dated completion ledger still records its older Fourier readiness checkpoint.

Read [CH04](../../../notes/md/ch04_CAR_Fock_space.md), [A02](../../../notes/appendices/a02_car_hilbert_and_normal_ordering.md), [TOC](../../../notes/md/TOC.md), [source audit](../../../docs/audit/reference_notes_lean_audit.md), [proof corrections](../../../note/proof_suggestions_revision_2026-10-09.md), and [completion ledger](../../../note/notes_review_completion_2026-10-09.md). No CH04/A02-specific file exists in `docs/stub_suggestion/` or `docs/proof_suggestion/`; inline strategies and the reviewed corrections are advisory. Three older CH01–CH03 suggestion files changed concurrently during drafting; those unrelated edits are preserved and excluded from this checkpoint.

Adopt the Euclidean carrier and occupation basis from the notes, basis construction via `Module.Basis.constr`, additive erasure counts, actual Hilbert adjoints, and a fixed ordered parity product. Adapt the abstract CAR contract into an algebraic structure and a separate finite Hilbert structure. Reject the withdrawn generic four-factor commutator formula (A=C=1 yields the wrong coefficient); use the CAR-specific bilinear commutator. Do not install symmetric CAR swaps as simp rules or infer an algebraic CAR pair is adjoint compatible.

Deferred: A02 polynomial Hermitian forms, raw words/normal symbols, Wick reduction, sea-Wick quartic corrections, CH06 local algebras/graded words/matrix units, and CH07 budgets. No compression, energy margin, lattice-evenness, or nonempty mode assumption is needed for this generic finite occupation model. The empty mode type has one occupation configuration, the empty set; creation witnesses take a mode `i`, so they do not claim modes exist in that edge case. Species later require an explicitly chosen lexicographic total order.

## Validation and approval boundary

- `lake build Bosonize` passes with unchanged Core. `lake build BosonizeStubs` passes with exactly 69 expected declaration-uses-sorry warnings (18 A02, 51 CH04). Fresh direct `lake env lean` checks have the same expected warnings and no errors or other warnings. No diagnostic/linter suppression was added.
- All 18 definitions/abbreviations and both structures elaborate without placeholders. A fresh definition/constructor/projection audit checks 23 names with only `propext`, `Classical.choice`, `Quot.sound`, and no `sorryAx`. This proves the definitions do not consume stub proofs, not the CAR identities themselves.
- Every one of the 69 proposed lemma bodies is exactly `:= by sorry`. Fresh theorem-axiom inspection exposes `sorryAx` in the stubs; theorem proofs remain outstanding. No definition, structure or instance body contains `sorry` or `admit`.
- Native Lean MCP diagnostics return full results, no errors or failed dependencies, and only the 18/51 expected `sorry` warnings. `lean_local_search` fails because its server PATH lacks `rg`; shell `rg` and direct compiler checks supplied declaration retrieval. This does not affect the successful diagnostic checks.
- Installed APIs checked directly: `EuclideanSpace.basisFun`, `.toBasis`, `Module.Basis.constr` with scalar argument `ℂ`, `WithLp.linearEquiv`, and finite-dimensional `LinearMap.adjoint`. Scratch checks elaborate `FockSpace Empty`, `ket ∅` over empty modes, creation over `Fin 1`, and parity over `Fin 0`.
- An independent temporary exact integer-coefficient occupation calculation passes 7,761 checks for 0–4 modes: insert/erase counts and sign relations, concrete CAR, adjoint matrix coefficients, number action, and bilinear commutators. Finite checks are sanity evidence, **not** Lean proofs for arbitrary finite mode types.
- All 69 existing guard regression tests pass. `core_lock.py --baseline-ref 648c076` verifies the four original complete-source hashes. Non-strict interface verification against `648c076` verifies all 113 existing statements and 102 commands, with warnings naming exactly the two new drafts. **Strict verification fails exactly on those two unreviewed files**, as required before interface approval. Consequently `make ci` and `make lock-check` are not reported as passing for this unlocked Phase A state.
- All manifests and existing Core source bytes remain unchanged. Review these exact definitions and statements; after explicit approval, establish and commit the reviewed lock before Phase B. Do not regenerate the lock to conceal a failure or start proofs from a successful staging build.

## Concrete definitions and type choices

Namespace `Bosonize.Ch04`. Eight complete definitions and 51 theorem stubs. The operator carrier uses a finite linearly ordered mode type `[Fintype ι] [LinearOrder ι]`; the order supplies decidable equality and comparisons. Count/sign helpers retain only the instances needed by their inferred signatures (finiteness is not needed for a finite occupation set). The chosen order is part of the fermionic phase convention.

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

All operators act on the same `A02.FockSpace ι`. No representation structure with unproved fields is hidden inside their definitions. `concrete_car_exists` is the explicitly unproved target asserting a finite Hilbert CAR representation with these exact maps. Prove CAR and adjoints before filling that witness; no concrete bundled data is introduced through a `sorry`-dependent definition.

## Proposed Phase B dependency order

1. **A02 basis bridges**, especially evaluation, inner product, nonzero kets, map extensionality and the adjoint pairing criterion.
2. **Atomic counts/signs**: insertion with j∉S and additive erasure with j∈S; same-mode count/sign invariance; sign square and conjugation. The insert/insert, erase/erase and mixed insert/erase helper hypotheses describe exactly the nonzero branches for distinct modes. Keep the membership conditions rather than deriving a sign relation on forbidden branches.
3. **Concrete basis actions and witnesses**: creation/annihilation evaluation, empty occupation action, creation on vacuum and annihilation on singleton nonzero. These proposed witnesses guard against trivial zero operators, but remain unproved in Phase A.
4. **Nilpotency, CAR, adjoints**: split coincident/distinct mode indices and occupied/empty configurations. Lift from basis actions with `end_ext_basis`. For adjointness, prove the basis-pair equation with conjugation in the first slot, then apply the A02 bridge. Establish both adjoint directions and `concrete_car_exists` only after those proofs.
5. **Diagonal observables/parity**: number action and idempotency, actual adjoints, pairwise number commutativity, total-number action, and parity action on kets. Derive parity square/self-adjointness and oddness of creation/annihilation from those actions; the sorted list fixes the defining order.
6. **Bilinears and hops**: reuse A02 pure-CAR algebra after obtaining the concrete CAR witness. Prove local/total number commutators, hopping basis action, blocked cases, diagonal identity and actual hopping adjoint.

## Sign, adjoint and edge contracts for review

`preceding_count_erase` states oldCount = erasedCount + indicator(j<i), avoiding natural subtraction. The hopping coefficient is sign(j,S) * sign(i,S.erase j), exactly matching the right-to-left action. The blocked-hop condition permits j∉S, or i≠j with i already occupied; i=j is handled by `hopping_diagonal`, so occupied diagonal hops are not accidentally claimed zero.

The mixed CAR target uses a scalar Kronecker indicator times the identity endomorphism. The adjoint basis equation is ⟨δS,cᵢ δT⟩=⟨c†ᵢ δS,δT⟩, with actual finite Hilbert adjoints. The bilinear identity preserves the corrected signs δbc c†a cd − δad c†c cb. Parity uses an explicit ascending list, never `Finset.prod` on an arbitrary noncommutative ring.

No lattice length, half filling or energy margin enters this generic chapter. Empty-mode dimension/vacuum contracts belong to A02; when a mode is supplied, singleton witnesses are available as proposed stubs. No true-for-all-modes conclusion is inferred from the finite sanity checks. Remaining obligations are exactly the 51 proofs and their 18 A02 dependencies, followed by the normal Phase C audit.

## Exact theorem inventory

Names below are review stubs; exact binder types and statements appear in the source snapshot.

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

Fresh audit output for data in this namespace; all stubs remain unproved.

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

## Exact Lean source snapshot

This block matches the source byte-for-byte, including its final newline.

Module SHA-256: `58f6e1a3e9e50e56ba4808cabeea4bed531f7e418c9990f0fdfc42bf2a03eb56`.

```lean
module

public import BosonizeStubs.A02CARHilbert

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

lemma preceding_count_empty (i : ι) : precedingCount i ∅ = 0 := by sorry

lemma preceding_count_insert (i j : ι) (S : A02.Occupation ι) (hj : j ∉ S) :
    precedingCount i (insert j S) = precedingCount i S + if j < i then 1 else 0 := by sorry

lemma preceding_count_erase (i j : ι) (S : A02.Occupation ι) (hj : j ∈ S) :
    precedingCount i S = precedingCount i (S.erase j) + if j < i then 1 else 0 := by sorry

lemma preceding_count_insert_self (i : ι) (S : A02.Occupation ι) :
    precedingCount i (insert i S) = precedingCount i S := by sorry

lemma preceding_count_erase_self (i : ι) (S : A02.Occupation ι) :
    precedingCount i (S.erase i) = precedingCount i S := by sorry

lemma fermion_sign_empty (i : ι) : fermionSign i ∅ = 1 := by sorry

lemma fermion_sign_ne_zero (i : ι) (S : A02.Occupation ι) : fermionSign i S ≠ 0 := by sorry

lemma fermion_sign_square (i : ι) (S : A02.Occupation ι) :
    fermionSign i S * fermionSign i S = 1 := by sorry

lemma fermion_sign_conj (i : ι) (S : A02.Occupation ι) :
    conj (fermionSign i S) = fermionSign i S := by sorry

lemma fermion_sign_insert_self (i : ι) (S : A02.Occupation ι) :
    fermionSign i (insert i S) = fermionSign i S := by sorry

lemma fermion_sign_erase_self (i : ι) (S : A02.Occupation ι) :
    fermionSign i (S.erase i) = fermionSign i S := by sorry

lemma sign_insert_insert (i j : ι) (S : A02.Occupation ι)
    (hij : i ≠ j) (hi : i ∉ S) (hj : j ∉ S) :
    fermionSign j S * fermionSign i (insert j S) =
      -(fermionSign i S * fermionSign j (insert i S)) := by sorry

lemma sign_erase_erase (i j : ι) (S : A02.Occupation ι)
    (hij : i ≠ j) (hi : i ∈ S) (hj : j ∈ S) :
    fermionSign j S * fermionSign i (S.erase j) =
      -(fermionSign i S * fermionSign j (S.erase i)) := by sorry

lemma sign_insert_erase (i j : ι) (S : A02.Occupation ι)
    (hij : i ≠ j) (hi : i ∉ S) (hj : j ∈ S) :
    fermionSign j S * fermionSign i (S.erase j) =
      -(fermionSign i S * fermionSign j (insert i S)) := by sorry

lemma creation_ket (i : ι) (S : A02.Occupation ι) :
    creation i (A02.ket S) =
      if i ∈ S then 0 else fermionSign i S • A02.ket (insert i S) := by sorry

lemma annihilation_ket (i : ι) (S : A02.Occupation ι) :
    annihilation i (A02.ket S) =
      if i ∈ S then fermionSign i S • A02.ket (S.erase i) else 0 := by sorry

lemma creation_vacuum (i : ι) : creation i (A02.ket ∅) = A02.ket {i} := by sorry

lemma annihilation_vacuum (i : ι) : annihilation i (A02.ket ∅) = 0 := by sorry

lemma creation_vacuum_ne_zero (i : ι) : creation i (A02.ket ∅) ≠ 0 := by sorry

lemma annihilation_singleton (i : ι) : annihilation i (A02.ket {i}) = A02.ket ∅ := by sorry

lemma annihilation_singleton_ne_zero (i : ι) : annihilation i (A02.ket {i}) ≠ 0 := by sorry

lemma creation_square (i : ι) : creation i * creation i = 0 := by sorry

lemma annihilation_square (i : ι) : annihilation i * annihilation i = 0 := by sorry

lemma creation_adjoint_pairing (i : ι) (S T : A02.Occupation ι) :
    inner ℂ (A02.ket S) (annihilation i (A02.ket T)) =
      inner ℂ (creation i (A02.ket S)) (A02.ket T) := by sorry

lemma creation_eq_adjoint (i : ι) : creation i = LinearMap.adjoint (annihilation i) := by sorry

lemma annihilation_eq_adjoint (i : ι) : annihilation i = LinearMap.adjoint (creation i) := by sorry

lemma annihilation_car (i j : ι) : A02.anticommutator (annihilation i) (annihilation j) = 0 := by sorry

lemma creation_car (i j : ι) : A02.anticommutator (creation i) (creation j) = 0 := by sorry

lemma mixed_car (i j : ι) : A02.anticommutator (annihilation i) (creation j) =
    (if i = j then (1 : ℂ) else 0) • (1 : Module.End ℂ (A02.FockSpace ι)) := by sorry

/-- Proposed existence of the concrete representation, not an assumed CAR instance. -/
lemma concrete_car_exists : ∃ R : A02.CAR ι (A02.FockSpace ι),
    R.annihilation = annihilation ∧ R.creation = creation := by sorry

lemma number_ket (i : ι) (S : A02.Occupation ι) :
    number i (A02.ket S) = (if i ∈ S then (1 : ℂ) else 0) • A02.ket S := by sorry

lemma number_idempotent (i : ι) : number i * number i = number i := by sorry

lemma number_adjoint (i : ι) : LinearMap.adjoint (number i) = number i := by sorry

lemma number_commute (i j : ι) : number i * number j = number j * number i := by sorry

lemma total_number_ket (S : A02.Occupation ι) :
    totalNumber (ι := ι) (A02.ket S) = (S.card : ℂ) • A02.ket S := by sorry

lemma total_number_adjoint :
    LinearMap.adjoint (totalNumber (ι := ι)) = totalNumber (ι := ι) := by sorry

lemma parity_ket (S : A02.Occupation ι) :
    parity (ι := ι) (A02.ket S) = (-1 : ℂ) ^ S.card • A02.ket S := by sorry

lemma parity_square : parity (ι := ι) * parity (ι := ι) = 1 := by sorry

lemma parity_adjoint : LinearMap.adjoint (parity (ι := ι)) = parity (ι := ι) := by sorry

lemma parity_vacuum : parity (ι := ι) (A02.ket ∅) = A02.ket ∅ := by sorry

lemma parity_creation (i : ι) : parity (ι := ι) * creation i = -(creation i * parity (ι := ι)) := by sorry

lemma parity_annihilation (i : ι) :
    parity (ι := ι) * annihilation i = -(annihilation i * parity (ι := ι)) := by sorry

lemma bilinear_commutator (a b c d : ι) :
    A02.commutator (hopping a b) (hopping c d) =
      (if b = c then (1 : ℂ) else 0) • hopping a d -
      (if a = d then (1 : ℂ) else 0) • hopping c b := by sorry

lemma number_creation_commutator (i j : ι) : A02.commutator (number i) (creation j) =
    (if i = j then (1 : ℂ) else 0) • creation j := by sorry

lemma number_annihilation_commutator (i j : ι) : A02.commutator (number i) (annihilation j) =
    -(if i = j then (1 : ℂ) else 0) • annihilation j := by sorry

lemma total_number_creation_commutator (i : ι) :
    A02.commutator (totalNumber (ι := ι)) (creation i) = creation i := by sorry

lemma total_number_annihilation_commutator (i : ι) :
    A02.commutator (totalNumber (ι := ι)) (annihilation i) = -annihilation i := by sorry

lemma hopping_ket (i j : ι) (S : A02.Occupation ι) (hij : i ≠ j)
    (hi : i ∉ S) (hj : j ∈ S) :
    hopping i j (A02.ket S) = (fermionSign j S * fermionSign i (S.erase j)) •
      A02.ket (insert i (S.erase j)) := by sorry

lemma hopping_blocked (i j : ι) (S : A02.Occupation ι)
    (h : j ∉ S ∨ (i ≠ j ∧ i ∈ S)) : hopping i j (A02.ket S) = 0 := by sorry

lemma hopping_diagonal (i : ι) : hopping i i = number i := by sorry

lemma hopping_adjoint (i j : ι) : LinearMap.adjoint (hopping i j) = hopping j i := by sorry

end Bosonize.Ch04
```
