# Appendix A01 lab notebook: Fourier characters and normalization

Status (2026-10-09): **Phase A compiled, unlocked, awaiting human interface review.** Six complete definitions and 30 unproved lemma stubs. Namespace: `Bosonize.A01`. Source: [A01](../../../notes/appendices/a01_fourier_scalars_and_characters.md), supporting [Chapter 3](../../../notes/md/ch03_fourier.md). Lean module: `BosonizeStubs/A01FourierCharacters.lean`.

## Carrier and assumption decisions

Use a field K and signed integer powers. `integerCharacter ζ k x = ζ^(k*x)` is a raw pairing; root and nonzero-size hypotheses live on the claims about it. `residueCharacter` chooses standard `ZMod.val` representatives, and `bandCharacter` keeps the actual signed integer momentum label. Both are complete definitions even before representative independence is proved. No quotient group law or mathematical character law is assumed by defining the raw function.

`[NeZero L]` supplies finite lattice instances and excludes `ZMod 0`. Convert it explicitly to positivity for the frozen Chapter 1 APIs. `bandEquiv` is built from frozen `band_projection_bijective`; no new group instance is installed on `Band L`. The inverse-transform statements in Chapter 3 separately require `(L : K) ≠ 0`; A01 orthogonality does not divide by L. No generic `CharZero K` or square-root field assumption is introduced.

A generic bundled `AddChar` is deferred: its algebraic proof fields would otherwise depend on Phase A stubs. The raw pairing and its full character-law contracts suffice at this gate. For the canonical complex root, `canonical_character_std` connects it to the installed bundled `ZMod.stdAddChar`; that bridge enables reuse of `AddChar`/DFT APIs during proofs.

`canonicalRoot` explicitly chooses exp(2πi/L). `normalization` is the one positive real scalar 1/√L. Generic character algebra uses neither square roots nor trigonometry. Norm, conjugation and scalar-CAR coefficient contracts live over ℂ/ℝ, on their actual types.

## Proposed proof dependency order

| Package | Lemma responsibilities | Proof plan |
| --- | --- | --- |
| Root and representatives | `root_pow_size`, `root_ne_zero`, `character_representative_independent`, `residue_character_int_cast` | Primitive-root laws, nonzero integer powers and shifts by multiples of L. |
| Character laws and witnesses | Addition, zero, negation, subtraction, `character_ne_zero`, `character_nontrivial` | Integer exponent laws, representative independence; evaluate a nonzero frequency at a suitable residue. |
| Band transport | Projection, addition/negation/subtraction, `sum_band_eq_sum_lattice` | Existing Core projection laws, bijection and finite-sum reindexing. |
| Orthogonality | `character_sum`, `character_orthogonality`, `dual_character_orthogonality` | Bundle the proved character in a proof-local construction and apply the nontrivial-character sum theorem, or telescope and cancel; handle the diagonal branch separately. |
| Complex specialization | Primitive canonical root, standard-character bridge, conjugation and unit norm | Installed exponential root and Circle character APIs; arbitrary primitive roots have unit norm but need not preserve canonical frequency labels. |
| Scalar normalization | Positivity, real/complex square identities, conjugation and CAR coefficient | Real sqrt laws followed by checked scalar casts. This is a scalar result, not a construction of CAR operators. |
| Edge cases | `singleton_character`, `nyquist_character_neg` | L=1 has only zero frequency; even Nyquist negation is transported to the same band element. |

The nontriviality, nonzero-character and singleton/Nyquist statements are witness obligations, not proved witness evidence. At L=4 the band keeps +2; integer −2 and +2 must have identical character evaluations, although their integer labels differ. There are no energy-budget margins at this finite Fourier stage.

## Suggestions adopted, adapted and rejected

Adopt the separation in the [revised Fourier guide](../../../docs/stub_suggestion/chapter_3_fourier_stub_draft.md), representative independence before character algebra, distinct carriers and one normalization scalar. Adapt its suggested bundled-character implementation to a raw complete pairing until the character laws are proved. Reuse the frozen band rather than introducing another centered convention.

Reject primitive-order-only orthogonality over rings with zero divisors, guessed sum/root theorem names, a generic quadratic-closure requirement and fractional momentum powers. The current A01 field contract avoids the recorded counterexamples; a more general ring theory is outside this draft. A power ζ^m need not have order L, so a primitive-root geometric-sum result cannot be applied with the wrong order.

Compiler/local-library evidence includes `ZMod.stdAddChar`, `ZMod.stdAddChar_coe`, `ZMod.isPrimitive_stdAddChar`, `ZMod.dft`, and `ZMod.invDFT_apply`. The canonical-root and standard-character equality statements are still unproved. No Chapter 3-specific file exists in `docs/proof_suggestion/`; the revised stub guide, inline source strategies and reconciled proof revision guide are advisory inputs.

## Validation and review gate

The installed compiler is `leanprover/lean4:v4.35.0-rc4`, with the dependency versions in `lake-manifest.json`. Native Lean MCP tools are not exposed in this chat; validation uses the installed compiler and local Mathlib sources. This is compiler evidence, not MCP/LSP evidence.

- `lake build Bosonize` and `lake build BosonizeStubs` pass.
- Fresh `lake env lean` compilation of A01 and Chapter 3 passes, producing respectively 30 and 31 expected `declaration uses sorry` diagnostics and no other diagnostics.
- Structural inspection checks exactly one `:= by sorry` in each lemma, no definition placeholders and exact notebook/source equality.
- Fresh `#print axioms` probes cover all 18 definitions/abbreviations across both modules. Dependencies contain only subsets of `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. Definitions do not depend on the new unproved lemmas. This audit is not a proof of the 61 theorem statements.
- All 69 existing guard tests pass. The non-strict statement guard against the pre-draft committed baseline verifies 52 existing statements and 54 existing commands, reporting only the two new unlocked files. The complete Core source guard passes against the same baseline.
- `make ci` intentionally fails at its strict statement guard on those two unreviewed additions. No lock was generated or accepted, and no guard, Core source or toolchain was changed to hide that result.

Phase A is complete only as a compiled proposal. Review definitions, hypotheses, theorem signatures, kernel orientation, representative convention and downstream usefulness before approving a strict lock. Phase B and Core promotion have not started. Full CI can pass after the approved new interface enters the lock through the ordinary review workflow.

## Provenance

Source baseline before this draft: `6ec5df254fb130a1a1483ceddffdaf22ee3e0d06`. The following hashes identify the exact source material consulted. These are source snapshots, not mathematical certification. Existing dated reviews may describe earlier revisions; the current notes and completion ledger control this draft.

| Source | SHA-256 |
| --- | --- |
| `notes/md/ch03_fourier.md` | `d4da4a800d18e68580fb793a3c8c9ba55d54836cf06253dd69e26ac86b89370e` |
| `notes/appendices/a01_fourier_scalars_and_characters.md` | `0b65cf6f5ed73a59ef5d25b2b502c34c4315cb5ce1df67cb690c3defba70b165` |
| `docs/stub_suggestion/chapter_3_fourier_stub_draft.md` | `793284489dbe77f76ca1a781fea878e2080445aba9375f72ae529c28d4dbe9a1` |
| `note/proof_suggestions_revision_2026-10-09.md` | `1db5f28b3e392d3b400ccc219ac640778fc5ceabc5cba17dfeb44b225a1b383c` |
| `note/notes_review_completion_2026-10-09.md` | `ee96609b0c32346be604041a99e3345c3420b71c830c88ef83ff8d93bd9c1dc1` |
| `Bosonize/Core/Ch01LatticeBand.lean` | `a88cd251573aa8a5416afa583b0a97b1e575ab09d4742b13a5b0be0e8a16b132` |
| `Bosonize/Core/Ch02UmbralCalculus.lean` | `d8d70d75372733aefda49e50baa033aaa5b363a57c0ec67a5a91368ac2d6f425` |
| `lean-toolchain` | `8f89aa44fccdb1a0b6cc768c7c9f54b94cd40e47a08d582f82d1235f13075cf7` |
| `lake-manifest.json` | `237acfc7835876d993b4025c88431d8d39f76db83cab94c9f9a640395f9c61f4` |


## Exact Lean source snapshot

This block is byte-for-byte identical to the corresponding Lean file, including its final newline. It is the complete reviewable interface and includes the structural proofs needed to construct linear maps; every lemma remains a one-sorry stub.

Module SHA-256: `b809a8376853aa5b2efddced8736f69a69ece54f8ee73e3428db3fb519764e42`.

```lean
module

public import Bosonize.Core.Ch01LatticeBand
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Appendix A01: Fourier characters and normalization

Phase A, unlocked: definitions are complete; every lemma is an unproved review stub.
Generic orthogonality uses a field, and division by L has a separate scalar hypothesis.
-/

@[expose] public section

namespace Bosonize.A01

open scoped BigOperators

variable {K : Type*} [Field K]

/-- The integer pairing, including ordinary negative momentum labels. -/
def integerCharacter (ζ : K) (k x : ℤ) : K := ζ ^ (k * x)

/-- Evaluate the integer pairing on the standard residue representatives. -/
def residueCharacter (L : ℕ) (ζ : K) (k x : Ch01.Lattice L) : K :=
  integerCharacter ζ (k.val : ℤ) (x.val : ℤ)

/-- Signed band evaluation; integer negation need not remain in the band. -/
def bandCharacter (L : ℕ) (ζ : K) (k : Ch01.Band L) (x : Ch01.Lattice L) : K :=
  integerCharacter ζ k.val (x.val : ℤ)

/-- The existing positive-Nyquist band equivalence, using only frozen Core proofs. -/
noncomputable def bandEquiv (L : ℕ) [NeZero L] : Ch01.Band L ≃ Ch01.Lattice L :=
  Equiv.ofBijective (Ch01.bandProjection L)
    (Ch01.band_projection_bijective L (Nat.pos_of_ne_zero (NeZero.ne L)))

/-- The canonical root for the physical complex layer. -/
noncomputable def canonicalRoot (L : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (L : ℂ))

/-- The one real normalization scalar; claims below exclude L = 0. -/
noncomputable def normalization (L : ℕ) : ℝ := (Real.sqrt (L : ℝ))⁻¹

lemma root_pow_size (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) :
    ζ ^ L = 1 := by sorry

lemma root_ne_zero (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) :
    ζ ≠ 0 := by sorry

lemma character_representative_independent (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k x s t : ℤ) :
    integerCharacter ζ (k + s * (L : ℤ)) (x + t * (L : ℤ)) =
      integerCharacter ζ k x := by sorry

lemma residue_character_int_cast (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) :
    residueCharacter L ζ (k : Ch01.Lattice L) (x : Ch01.Lattice L) =
      integerCharacter ζ k x := by sorry

lemma residue_character_add_right (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k x y : Ch01.Lattice L) :
    residueCharacter L ζ k (x + y) =
      residueCharacter L ζ k x * residueCharacter L ζ k y := by sorry

lemma residue_character_add_left (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k p x : Ch01.Lattice L) :
    residueCharacter L ζ (k + p) x =
      residueCharacter L ζ k x * residueCharacter L ζ p x := by sorry

lemma residue_character_zero (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (x : Ch01.Lattice L) :
    residueCharacter L ζ 0 x = 1 := by sorry

lemma residue_character_neg (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k x : Ch01.Lattice L) :
    residueCharacter L ζ (-k) x = (residueCharacter L ζ k x)⁻¹ := by sorry

lemma residue_character_sub (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k p x : Ch01.Lattice L) :
    residueCharacter L ζ (k - p) x =
      residueCharacter L ζ k x * (residueCharacter L ζ p x)⁻¹ := by sorry

lemma character_ne_zero (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) : integerCharacter ζ k x ≠ 0 := by sorry

lemma character_nontrivial (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Lattice L) (hk : k ≠ 0) :
    ∃ x : Ch01.Lattice L, residueCharacter L ζ k x ≠ 1 := by sorry

lemma band_character_projection (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) (x : Ch01.Lattice L) :
    bandCharacter L ζ k x = residueCharacter L ζ (Ch01.bandProjection L k) x := by sorry

lemma band_character_add (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k p : Ch01.Band L) (x : Ch01.Lattice L) :
    bandCharacter L ζ (Ch01.bandAdd L (Nat.pos_of_ne_zero (NeZero.ne L)) k p) x =
      bandCharacter L ζ k x * bandCharacter L ζ p x := by sorry

lemma band_character_neg (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) (x : Ch01.Lattice L) :
    bandCharacter L ζ (Ch01.bandNeg L (Nat.pos_of_ne_zero (NeZero.ne L)) k) x =
      integerCharacter ζ (-k.val) (x.val : ℤ) := by sorry

lemma band_character_sub (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k p : Ch01.Band L) (x : Ch01.Lattice L) :
    bandCharacter L ζ
      (Ch01.bandAdd L (Nat.pos_of_ne_zero (NeZero.ne L)) k
        (Ch01.bandNeg L (Nat.pos_of_ne_zero (NeZero.ne L)) p)) x =
      integerCharacter ζ (k.val - p.val) (x.val : ℤ) := by sorry

lemma sum_band_eq_sum_lattice (L : ℕ) [NeZero L] (f : Ch01.Lattice L → K) :
    (∑ k : Ch01.Band L, f (Ch01.bandProjection L k)) = ∑ x : Ch01.Lattice L, f x := by sorry

lemma character_sum (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Lattice L) :
    (∑ x : Ch01.Lattice L, residueCharacter L ζ k x) =
      if k = 0 then (L : K) else 0 := by sorry

lemma character_orthogonality (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k p : Ch01.Band L) :
    (∑ x : Ch01.Lattice L, integerCharacter ζ (k.val - p.val) (x.val : ℤ)) =
      if k = p then (L : K) else 0 := by sorry

lemma dual_character_orthogonality (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (x y : Ch01.Lattice L) :
    (∑ k : Ch01.Band L, integerCharacter ζ k.val ((x.val : ℤ) - (y.val : ℤ))) =
      if x = y then (L : K) else 0 := by sorry

lemma canonical_root_primitive (L : ℕ) [NeZero L] :
    IsPrimitiveRoot (canonicalRoot L) L := by sorry

lemma canonical_character_std (L : ℕ) [NeZero L] (k x : Ch01.Lattice L) :
    residueCharacter L (canonicalRoot L) k x = ZMod.stdAddChar (k * x) := by sorry

lemma complex_character_conj (L : ℕ) [NeZero L] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) :
    star (integerCharacter ζ k x) = integerCharacter ζ (-k) x := by sorry

lemma complex_character_norm (L : ℕ) [NeZero L] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) : ‖integerCharacter ζ k x‖ = 1 := by sorry

lemma normalization_pos (L : ℕ) [NeZero L] : 0 < normalization L := by sorry

lemma normalization_square (L : ℕ) [NeZero L] :
    (L : ℝ) * normalization L ^ 2 = 1 := by sorry

lemma normalization_conj (L : ℕ) :
    star (normalization L : ℂ) = (normalization L : ℂ) := by sorry

lemma normalization_square_complex (L : ℕ) [NeZero L] :
    (L : ℂ) * (normalization L : ℂ) ^ 2 = 1 := by sorry

/-- Scalar contract needed by later position CAR, without asserting a CAR model here. -/
lemma normalization_car_coefficient (L : ℕ) [NeZero L] :
    ‖(normalization L : ℂ)‖ ^ 2 * (L : ℝ) = 1 := by sorry

lemma singleton_character (ζ : K) (hζ : IsPrimitiveRoot ζ 1)
    (k : Ch01.Band 1) (x : Ch01.Lattice 1) : bandCharacter 1 ζ k x = 1 := by sorry

lemma nyquist_character_neg (L : ℕ) [NeZero L] (hEven : Even L)
    (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L)
    (hk : k.val = ((L / 2 : ℕ) : ℤ)) (x : Ch01.Lattice L) :
    integerCharacter ζ (-k.val) (x.val : ℤ) = bandCharacter L ζ k x := by sorry

end Bosonize.A01
```
