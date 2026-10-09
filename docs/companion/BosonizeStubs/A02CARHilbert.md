# Appendix A02 finite-CAR lab notebook

Status (2026-10-09): **Phase A complete; awaiting interface review.** Lean module: `BosonizeStubs/A02CARHilbert.lean`.

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

## Carrier, contracts and type choices

Namespace `Bosonize.A02`. Ten complete definitions/abbreviations, two complete structures, and 18 theorem stubs.

`Occupation ι := Finset ι`. `FockSpace ι := EuclideanSpace ℂ (Occupation ι)` needs `[Fintype ι] [DecidableEq ι]`. No order is needed in this support carrier. `occupationONB` is the canonical Euclidean orthonormal basis; `occupationBasis` is its algebraic `.toBasis`. `ket S` is that basis vector, not a vector declared orthonormal by assumption. `coordinates` is an algebraic linear equivalence to functions; no incompatible Hilbert instance is installed on that function carrier. `extendBasis images` constructs an endomorphism from basis images.

`commutator A B = A*B-B*A`, `anticommutator A B = A*B+B*A`; multiplication is composition with the right factor first. `AlgebraicCAR ι V` requires decidable equality on modes and a complex module over an additive commutative group, but no finiteness or topology. Its creation/annihilation maps and three relation fields are hypotheses for generic algebraic lemmas. `CAR ι V` extends it on a finite-dimensional complex inner-product space, adding the actual equation `creation i = LinearMap.adjoint (annihilation i)`. No concrete CAR instance is assumed or constructed here.

## Proposed proof order and remaining obligations

| Layer | Proposed obligations | How Phase B should approach them |
| --- | --- | --- |
| Coordinate and basis bridge | `ket_apply`, `coordinates_ket`, `ket_inner`, `ket_norm`, `ket_ne_zero`, `vacuum_ne_zero` | Reuse checked canonical basis/single-vector APIs; explicitly identify equality orientation in indicator coefficients. |
| Finite linear algebra | `fock_inner`, `occupation_expansion`, `extend_basis_ket`, `end_ext_basis` | PiL2 finite-sum inner product, basis reconstruction, constr evaluation and basis extensionality. |
| Adjoint bridge | `adjoint_of_basis_pairing` | Extend the stated basis-pair equation by finite sums, preserving conjugate-linearity in the first argument. Conclude using the actual finite-dimensional adjoint API. |
| Dimension and edge case | `fock_finrank`, `empty_modes_finrank` | Count occupation subsets and use the basis dimension; empty mode type gives dimension one. |
| Algebraic CAR reuse | `car_bilinear_commutator`, number/creation and number/annihilation commutators, number commutativity/idempotency | Expand products with explicit factor order and justified CAR swaps; normalize scalar coefficients separately. The bilinear identity is CAR-specific, not a generic ring formula. |

Every row remains a theorem obligation. The existence of the canonical basis comes from Mathlib; the newly proposed bridge statements have not yet been proved. No new mathematical contradiction was found in these contracts. Before freezing, review that this algebraic/Hilbert split and its public helper names are useful to downstream chapters.

## Exact theorem inventory

Names below are review stubs; exact binder types and statements appear in the source snapshot.

- `Bosonize.A02.car_bilinear_commutator`
- `Bosonize.A02.car_number_creation_commutator`
- `Bosonize.A02.car_number_annihilation_commutator`
- `Bosonize.A02.car_number_commute`
- `Bosonize.A02.car_number_idempotent`
- `Bosonize.A02.ket_apply`
- `Bosonize.A02.coordinates_ket`
- `Bosonize.A02.ket_inner`
- `Bosonize.A02.ket_norm`
- `Bosonize.A02.ket_ne_zero`
- `Bosonize.A02.vacuum_ne_zero`
- `Bosonize.A02.fock_inner`
- `Bosonize.A02.occupation_expansion`
- `Bosonize.A02.extend_basis_ket`
- `Bosonize.A02.end_ext_basis`
- `Bosonize.A02.adjoint_of_basis_pairing`
- `Bosonize.A02.fock_finrank`
- `Bosonize.A02.empty_modes_finrank`

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
'Bosonize.A02.Occupation' depends on axioms: [propext, Quot.sound]
'Bosonize.A02.FockSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A02.occupationONB' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A02.occupationBasis' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A02.ket' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A02.coordinates' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A02.extendBasis' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A02.commutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A02.anticommutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A02.AlgebraicCAR.number' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A02.AlgebraicCAR.mk' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A02.AlgebraicCAR.annihilation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A02.AlgebraicCAR.creation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A02.CAR.mk' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A02.CAR.toAlgebraicCAR' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Exact Lean source snapshot

This block matches the source byte-for-byte, including its final newline.

Module SHA-256: `bff4700bb8c04037b0f2fea4778e15bafeff63e4545cb3682fb170f712378b41`.

```lean
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Data.Finset.Sort

/-!
# A02: finite occupation Hilbert space and CAR contracts
Phase A: complete data, one-sorry review stubs. Polynomial forms and Wick words are deferred.
-/

@[expose] public section

namespace Bosonize.A02

open scoped BigOperators ComplexConjugate

abbrev Occupation (ι : Type*) := Finset ι

abbrev FockSpace (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  EuclideanSpace ℂ (Occupation ι)

noncomputable def occupationONB (ι : Type*) [Fintype ι] [DecidableEq ι] :
    OrthonormalBasis (Occupation ι) ℂ (FockSpace ι) :=
  EuclideanSpace.basisFun (Occupation ι) ℂ

noncomputable def occupationBasis (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Module.Basis (Occupation ι) ℂ (FockSpace ι) :=
  (occupationONB ι).toBasis

noncomputable def ket {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Occupation ι) : FockSpace ι := occupationBasis ι S

/-- Algebraic coordinate transport; the function carrier is not given a new Hilbert norm. -/
noncomputable def coordinates (ι : Type*) [Fintype ι] [DecidableEq ι] :
    FockSpace ι ≃ₗ[ℂ] (Occupation ι → ℂ) :=
  WithLp.linearEquiv 2 ℂ (Occupation ι → ℂ)

noncomputable def extendBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (images : Occupation ι → FockSpace ι) : Module.End ℂ (FockSpace ι) :=
  (occupationBasis ι).constr ℂ images

section Algebraic

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Endomorphism multiplication is composition: the right factor acts first. -/
def commutator (A B : Module.End ℂ V) : Module.End ℂ V := A * B - B * A

def anticommutator (A B : Module.End ℂ V) : Module.End ℂ V := A * B + B * A

/-- Algebraic CAR assumptions; adjoints are deliberately a separate contract. -/
structure AlgebraicCAR (ι : Type*) [DecidableEq ι] (V : Type*)
    [AddCommGroup V] [Module ℂ V] where
  annihilation : ι → Module.End ℂ V
  creation : ι → Module.End ℂ V
  annihilation_car : ∀ i j, anticommutator (annihilation i) (annihilation j) = 0
  creation_car : ∀ i j, anticommutator (creation i) (creation j) = 0
  mixed_car : ∀ i j, anticommutator (annihilation i) (creation j) =
    (if i = j then (1 : ℂ) else 0) • (1 : Module.End ℂ V)

def AlgebraicCAR.number {ι : Type*} [DecidableEq ι]
    (R : AlgebraicCAR ι V) (i : ι) : Module.End ℂ V :=
  R.creation i * R.annihilation i

variable {ι : Type*} [DecidableEq ι]

lemma car_bilinear_commutator (R : AlgebraicCAR ι V) (a b c d : ι) :
    commutator (R.creation a * R.annihilation b) (R.creation c * R.annihilation d) =
      (if b = c then (1 : ℂ) else 0) • (R.creation a * R.annihilation d) -
      (if a = d then (1 : ℂ) else 0) • (R.creation c * R.annihilation b) := by sorry

lemma car_number_creation_commutator (R : AlgebraicCAR ι V) (i j : ι) :
    commutator (R.number i) (R.creation j) =
      (if i = j then (1 : ℂ) else 0) • R.creation j := by sorry

lemma car_number_annihilation_commutator (R : AlgebraicCAR ι V) (i j : ι) :
    commutator (R.number i) (R.annihilation j) =
      -(if i = j then (1 : ℂ) else 0) • R.annihilation j := by sorry

lemma car_number_commute (R : AlgebraicCAR ι V) (i j : ι) :
    R.number i * R.number j = R.number j * R.number i := by sorry

lemma car_number_idempotent (R : AlgebraicCAR ι V) (i : ι) :
    R.number i * R.number i = R.number i := by sorry

end Algebraic

/-- Finite Hilbert CAR includes actual adjoint compatibility, not just algebraic relations. -/
structure CAR (ι : Type*) [DecidableEq ι] (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    extends AlgebraicCAR ι V where
  adjoint_compat : ∀ i, creation i = LinearMap.adjoint (annihilation i)

section Occupations

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma ket_apply (S T : Occupation ι) :
    ket S T = if T = S then (1 : ℂ) else 0 := by sorry

lemma coordinates_ket (S T : Occupation ι) :
    coordinates ι (ket S) T = if T = S then (1 : ℂ) else 0 := by sorry

lemma ket_inner (S T : Occupation ι) :
    inner ℂ (ket S) (ket T) = if S = T then (1 : ℂ) else 0 := by sorry

lemma ket_norm (S : Occupation ι) : ‖ket S‖ = 1 := by sorry

lemma ket_ne_zero (S : Occupation ι) : ket S ≠ 0 := by sorry

lemma vacuum_ne_zero : ket (∅ : Occupation ι) ≠ 0 := by sorry

lemma fock_inner (u v : FockSpace ι) :
    inner ℂ u v = ∑ S : Occupation ι, conj (u S) * v S := by sorry

lemma occupation_expansion (v : FockSpace ι) :
    v = ∑ S : Occupation ι, v S • ket S := by sorry

lemma extend_basis_ket (images : Occupation ι → FockSpace ι) (S : Occupation ι) :
    extendBasis images (ket S) = images S := by sorry

lemma end_ext_basis (A B : Module.End ℂ (FockSpace ι))
    (h : ∀ S : Occupation ι, A (ket S) = B (ket S)) : A = B := by sorry

lemma adjoint_of_basis_pairing (A B : Module.End ℂ (FockSpace ι))
    (h : ∀ S T : Occupation ι, inner ℂ (ket S) (A (ket T)) =
      inner ℂ (B (ket S)) (ket T)) : B = LinearMap.adjoint A := by sorry

lemma fock_finrank : Module.finrank ℂ (FockSpace ι) = 2 ^ Fintype.card ι := by sorry

lemma empty_modes_finrank [IsEmpty ι] : Module.finrank ℂ (FockSpace ι) = 1 := by sorry

end Occupations

end Bosonize.A02
```
