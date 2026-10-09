# Appendix A01 lab notebook: Fourier characters and normalization

Status (2026-10-09): **Phase B complete in staging; Phase C promotion awaits authorization.** Six complete definitions and 30 proved lemmas. Namespace: `Bosonize.A01`. Source: [A01](../../../notes/appendices/a01_fourier_scalars_and_characters.md), supporting [Chapter 3](../../../notes/md/ch03_fourier.md). Lean module: `BosonizeStubs/A01FourierCharacters.lean`.

## Carrier and assumption decisions

Use a field K and signed integer powers. `integerCharacter ζ k x = ζ^(k*x)` is a raw pairing; root and nonzero-size hypotheses live on the claims about it. `residueCharacter` chooses standard `ZMod.val` representatives, and `bandCharacter` keeps the actual signed integer momentum label. Representative independence and the character laws are now proved for the stated primitive-root contract. No quotient group law or mathematical character law is assumed by defining the raw function.

`[NeZero L]` supplies finite lattice instances and excludes `ZMod 0`. Convert it explicitly to positivity for the frozen Chapter 1 APIs. `bandEquiv` is built from frozen `band_projection_bijective`; no new group instance is installed on `Band L`. The inverse-transform statements in Chapter 3 separately require `(L : K) ≠ 0`; A01 orthogonality does not divide by L. No generic `CharZero K` or square-root field assumption is introduced.

The locked interface retains the raw pairing. The `character_sum` proof constructs a local bundled `AddChar` from the now-proved character laws; no new public definition was added. For the canonical complex root, `canonical_character_std` connects it to the installed bundled `ZMod.stdAddChar`; that proved bridge enables reuse of Mathlib DFT APIs.

`canonicalRoot` explicitly chooses exp(2πi/L). `normalization` is the one positive real scalar 1/√L. Generic character algebra uses neither square roots nor trigonometry. Norm, conjugation and scalar-CAR coefficient contracts live over ℂ/ℝ, on their actual types.

## Proof dependency order

| Package | Lemma responsibilities | Proof plan |
| --- | --- | --- |
| Root and representatives | `root_pow_size`, `root_ne_zero`, `character_representative_independent`, `residue_character_int_cast` | Primitive-root laws, nonzero integer powers and an exact polynomial expansion of shifts by multiples of L. |
| Character laws and witnesses | Addition, zero, negation, subtraction, `character_ne_zero`, `character_nontrivial` | Integer exponent laws and representative independence; evaluate at residue 1 and use the primitive root lifted to units to rule out the value 1 for a nonzero frequency. |
| Band transport | Projection, addition/negation/subtraction, `sum_band_eq_sum_lattice` | Existing Core projection laws, bijection and finite-sum reindexing. |
| Orthogonality | `character_sum`, `character_orthogonality`, `dual_character_orthogonality` | Bundle the proved character locally and apply `AddChar.sum_eq_zero_of_ne_one`; handle the diagonal branch separately and reindex through the frozen band bijection. |
| Complex specialization | Primitive canonical root, standard-character bridge, conjugation and unit norm | Installed exponential root and Circle character APIs; arbitrary primitive roots have unit norm but need not preserve canonical frequency labels. |
| Scalar normalization | Positivity, real/complex square identities, conjugation and CAR coefficient | Real sqrt laws followed by checked scalar casts. This is a scalar result, not a construction of CAR operators. |
| Edge cases | `singleton_character`, `nyquist_character_neg` | L=1 has only zero frequency; even Nyquist negation is transported to the same band element. |

The nontriviality, nonzero-character and singleton/Nyquist statements are now compiler-checked witness results. At L=4 the band keeps +2; integer −2 and +2 must have identical character evaluations, although their integer labels differ. There are no energy-budget margins at this finite Fourier stage.

## Suggestions adopted, adapted and rejected

Adopt the separation in the [revised Fourier guide](../../../docs/stub_suggestion/chapter_3_fourier_stub_draft.md), representative independence before character algebra, distinct carriers and one normalization scalar. Adapt its suggested bundled-character implementation to the locked raw pairing and a proof-local bundled character. Reuse the frozen band rather than introducing another centered convention.

Reject primitive-order-only orthogonality over rings with zero divisors, guessed sum/root theorem names, a generic quadratic-closure requirement and fractional momentum powers. The current A01 field contract avoids the recorded counterexamples; a more general ring theory is outside this draft. A power ζ^m need not have order L, so a primitive-root geometric-sum result cannot be applied with the wrong order.

Compiler/local-library evidence includes `ZMod.stdAddChar`, `ZMod.stdAddChar_coe`, `ZMod.isPrimitive_stdAddChar`, `ZMod.dft`, and `ZMod.invDFT_apply`. The canonical-root and standard-character equality statements are proved; the equality uses `Complex.exp_int_mul`, the standard character integer-cast formula and exact scalar algebra. No Chapter 3-specific file exists in `docs/proof_suggestion/`; the revised stub guide, inline source strategies and reconciled proof revision guide are advisory inputs.

## Phase B validation and remaining gate

The user approved both interfaces, supplied the updated strict lock, and authorized Phase B. Before proof edits, the supplied lock was compared structurally with the previous committed lock: it added only these two modules and preserved every existing entry. The reviewed lock was committed as `73add9042f2247fcbb1048d3b39f44f844f5e4b1`. It was not regenerated during proof development.

- `STUB_LOCK_BASELINE_REF=73add90 make ci` passes: 69 guard tests, 113 frozen lemma statements, 102 frozen commands, two complete Core source hashes, and both Lean library builds.
- Fresh `lake env lean -DwarningAsError=true BosonizeStubs/A01FourierCharacters.lean` and the corresponding Chapter 3 command exit 0 with empty diagnostics. No warning or lint suppression was introduced.
- All 30 A01 and 31 Chapter 3 lemmas have complete proofs. Structural inspection finds zero `sorry`, `admit` or `axiom` commands in either module; all 18 definitions/abbreviations and all approved headers remain unchanged.
- Fresh `#print axioms` over all 61 theorem names finds only subsets of `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. The module-specific output is recorded below.
- The notebook source block exactly matches the current Lean file. Core, imports, namespaces, toolchain and dependency manifest are unchanged; the strict committed-baseline guard verifies all frozen definitions and statements.
- Native Lean MCP tools are not exposed in this chat. Compiler and local-library checks supply the evidence above; native MCP/LSP transport was not tested.

Phase B is complete. Phase C promotion, migration of module paths/notebooks/aggregators, and complete-source freezing require authorization. No new top-level helper, equivalence bundle or assumption was added. The module's retained Phase A doc-comments describe its original draft; the status and fresh evidence in this notebook describe its completed proofs.

## Theorem axiom audit

```text
'Bosonize.A01.root_pow_size' depends on axioms: [propext, Quot.sound]
'Bosonize.A01.root_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.character_representative_independent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.residue_character_int_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.residue_character_add_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.residue_character_add_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.residue_character_zero' depends on axioms: [propext, Quot.sound]
'Bosonize.A01.residue_character_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.residue_character_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.character_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.character_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.band_character_projection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.band_character_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.band_character_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.band_character_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.sum_band_eq_sum_lattice' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.character_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.character_orthogonality' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.dual_character_orthogonality' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.canonical_root_primitive' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.canonical_character_std' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.complex_character_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.complex_character_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.normalization_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.normalization_square' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.normalization_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.normalization_square_complex' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.normalization_car_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A01.singleton_character' depends on axioms: [propext, Quot.sound]
'Bosonize.A01.nyquist_character_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
```

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

The complete source below is byte-for-byte identical to the current module, including its final newline. All lemma bodies are proved; original definitions and signatures are preserved.

Module SHA-256: `eb4a90141b76b7fda25269545c219b87459cc5fadbc1f9cc836d2048dee6d70c`.

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
    ζ ^ L = 1 := by
  exact hζ.pow_eq_one

lemma root_ne_zero (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) :
    ζ ≠ 0 := by
  exact hζ.ne_zero (NeZero.ne L)

lemma character_representative_independent (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k x s t : ℤ) :
    integerCharacter ζ (k + s * (L : ℤ)) (x + t * (L : ℤ)) =
      integerCharacter ζ k x := by
  have hn := root_ne_zero L ζ hζ
  have hp : ζ ^ (L : ℤ) = 1 := by simpa using hζ.pow_eq_one
  unfold integerCharacter
  have he : (k + s * (L : ℤ)) * (x + t * (L : ℤ)) =
      k * x + (L : ℤ) * (k * t + s * x + s * t * (L : ℤ)) := by ring
  rw [he, zpow_add₀ hn, zpow_mul ζ (L : ℤ), hp, one_zpow, mul_one]

lemma residue_character_int_cast (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) :
    residueCharacter L ζ (k : Ch01.Lattice L) (x : Ch01.Lattice L) =
      integerCharacter ζ k x := by
  unfold residueCharacter
  rw [ZMod.val_intCast, ZMod.val_intCast]
  have he (a : ℤ) : a % (L : ℤ) = a + (-(a / (L : ℤ))) * (L : ℤ) := by
    have h := Int.emod_add_mul_ediv a (L : ℤ)
    nlinarith
  rw [he k, he x]
  exact character_representative_independent L ζ hζ k x _ _

lemma residue_character_add_right (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k x y : Ch01.Lattice L) :
    residueCharacter L ζ k (x + y) =
      residueCharacter L ζ k x * residueCharacter L ζ k y := by
  have hc (r : Ch01.Lattice L) : ((r.val : ℤ) : Ch01.Lattice L) = r := by
    simp
  rw [← hc k, ← hc x, ← hc y, ← Int.cast_add]
  simp only [residue_character_int_cast L ζ hζ, integerCharacter, mul_add,
    zpow_add₀ (root_ne_zero L ζ hζ)]

lemma residue_character_add_left (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k p x : Ch01.Lattice L) :
    residueCharacter L ζ (k + p) x =
      residueCharacter L ζ k x * residueCharacter L ζ p x := by
  have hc (r : Ch01.Lattice L) : ((r.val : ℤ) : Ch01.Lattice L) = r := by
    simp
  rw [← hc k, ← hc p, ← hc x, ← Int.cast_add]
  simp only [residue_character_int_cast L ζ hζ, integerCharacter, add_mul,
    zpow_add₀ (root_ne_zero L ζ hζ)]

lemma residue_character_zero (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (x : Ch01.Lattice L) :
    residueCharacter L ζ 0 x = 1 := by
  cases hζ
  simp [residueCharacter, integerCharacter]

lemma residue_character_neg (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k x : Ch01.Lattice L) :
    residueCharacter L ζ (-k) x = (residueCharacter L ζ k x)⁻¹ := by
  have hc (r : Ch01.Lattice L) : ((r.val : ℤ) : Ch01.Lattice L) = r := by simp
  calc
    residueCharacter L ζ (-k) x = integerCharacter ζ (-(k.val : ℤ)) (x.val : ℤ) := by
      simpa only [Int.cast_neg, hc] using residue_character_int_cast L ζ hζ (-(k.val : ℤ)) (x.val : ℤ)
    _ = (residueCharacter L ζ k x)⁻¹ := by
      rw [show residueCharacter L ζ k x = integerCharacter ζ (k.val : ℤ) (x.val : ℤ) from
        by simpa only [hc] using residue_character_int_cast L ζ hζ (k.val : ℤ) (x.val : ℤ)]
      simp [integerCharacter]

lemma residue_character_sub (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k p x : Ch01.Lattice L) :
    residueCharacter L ζ (k - p) x =
      residueCharacter L ζ k x * (residueCharacter L ζ p x)⁻¹ := by
  rw [sub_eq_add_neg, residue_character_add_left L ζ hζ,
    residue_character_neg L ζ hζ]

lemma character_ne_zero (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) : integerCharacter ζ k x ≠ 0 := by
  exact zpow_ne_zero _ (root_ne_zero L ζ hζ)

lemma character_nontrivial (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Lattice L) (hk : k ≠ 0) :
    ∃ x : Ch01.Lattice L, residueCharacter L ζ k x ≠ 1 := by
  classical
  have he : (L : ℤ) ∣ (k.val : ℤ) → False := by
    intro hd
    apply hk
    have hz : (k.val : ℤ) = 0 := Int.eq_zero_of_dvd_of_nonneg_of_lt
      (by positivity) (by exact_mod_cast ZMod.val_lt k) hd
    simpa using congrArg (fun a : ℤ ↦ (a : Ch01.Lattice L)) hz
  refine ⟨1, ?_⟩
  have hc : ((k.val : ℤ) : Ch01.Lattice L) = k := by simp
  have hr : residueCharacter L ζ k 1 = ζ ^ (k.val : ℤ) := by
    simpa only [hc, Int.cast_one, integerCharacter, mul_one] using
      residue_character_int_cast L ζ hζ (k.val : ℤ) 1
  rw [hr]
  intro h
  have hu := hζ.isUnit (NeZero.ne L)
  have hp : (hu.unit : Kˣ) ^ (k.val : ℤ) = 1 := by
    apply Units.val_injective
    simpa using h
  have hprim : IsPrimitiveRoot hu.unit L := by
    exact (IsPrimitiveRoot.coe_units_iff).mp (by simpa using hζ)
  exact he ((hprim.zpow_eq_one_iff_dvd _).mp hp)

lemma band_character_projection (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) (x : Ch01.Lattice L) :
    bandCharacter L ζ k x = residueCharacter L ζ (Ch01.bandProjection L k) x := by
  have hc : ((x.val : ℤ) : Ch01.Lattice L) = x := by simp
  simpa only [hc, bandCharacter, Ch01.bandProjection, Ch01.quotientMap] using
    (residue_character_int_cast L ζ hζ k.val (x.val : ℤ)).symm

lemma band_character_add (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k p : Ch01.Band L) (x : Ch01.Lattice L) :
    bandCharacter L ζ (Ch01.bandAdd L (Nat.pos_of_ne_zero (NeZero.ne L)) k p) x =
      bandCharacter L ζ k x * bandCharacter L ζ p x := by
  rw [band_character_projection L ζ hζ, Ch01.band_add_projection,
    residue_character_add_left L ζ hζ, ← band_character_projection L ζ hζ,
    ← band_character_projection L ζ hζ]

lemma band_character_neg (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) (x : Ch01.Lattice L) :
    bandCharacter L ζ (Ch01.bandNeg L (Nat.pos_of_ne_zero (NeZero.ne L)) k) x =
      integerCharacter ζ (-k.val) (x.val : ℤ) := by
  rw [band_character_projection L ζ hζ, Ch01.band_neg_projection]
  change residueCharacter L ζ (-(k.val : Ch01.Lattice L)) x = _
  rw [← ZMod.natCast_zmod_val x, ← Int.cast_neg]
  simpa using residue_character_int_cast L ζ hζ (-k.val) (x.val : ℤ)

lemma band_character_sub (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k p : Ch01.Band L) (x : Ch01.Lattice L) :
    bandCharacter L ζ
      (Ch01.bandAdd L (Nat.pos_of_ne_zero (NeZero.ne L)) k
        (Ch01.bandNeg L (Nat.pos_of_ne_zero (NeZero.ne L)) p)) x =
      integerCharacter ζ (k.val - p.val) (x.val : ℤ) := by
  rw [band_character_projection L ζ hζ, Ch01.band_add_projection,
    Ch01.band_neg_projection]
  change residueCharacter L ζ ((k.val : Ch01.Lattice L) + -(p.val : Ch01.Lattice L)) x = _
  rw [← Int.cast_neg, ← Int.cast_add, ← ZMod.natCast_zmod_val x]
  simpa [sub_eq_add_neg] using residue_character_int_cast L ζ hζ (k.val - p.val) (x.val : ℤ)

lemma sum_band_eq_sum_lattice (L : ℕ) [NeZero L] (f : Ch01.Lattice L → K) :
    (∑ k : Ch01.Band L, f (Ch01.bandProjection L k)) = ∑ x : Ch01.Lattice L, f x := by
  exact (bandEquiv L).sum_comp f

lemma character_sum (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Lattice L) :
    (∑ x : Ch01.Lattice L, residueCharacter L ζ k x) =
      if k = 0 then (L : K) else 0 := by
  classical
  by_cases hk : k = 0
  · simp [hk, residue_character_zero L ζ hζ, ZMod.card]
  · let ψ : AddChar (Ch01.Lattice L) K :=
      { toFun := residueCharacter L ζ k
        map_zero_eq_one' := by simp [residueCharacter, integerCharacter]
        map_add_eq_mul' := residue_character_add_right L ζ hζ k }
    have hψ : ψ ≠ 1 := by
      obtain ⟨x, hx⟩ := character_nontrivial L ζ hζ k hk
      intro he
      exact hx (congrArg (fun c : AddChar (Ch01.Lattice L) K ↦ c x) he)
    change (∑ x, ψ x) = _
    rw [ite_eq_right hk]
    exact AddChar.sum_eq_zero_of_ne_one hψ

lemma character_orthogonality (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k p : Ch01.Band L) :
    (∑ x : Ch01.Lattice L, integerCharacter ζ (k.val - p.val) (x.val : ℤ)) =
      if k = p then (L : K) else 0 := by
  classical
  have hc (r : Ch01.Lattice L) : ((r.val : ℤ) : Ch01.Lattice L) = r := by simp
  have he (x : Ch01.Lattice L) : integerCharacter ζ (k.val - p.val) (x.val : ℤ) =
      residueCharacter L ζ (Ch01.bandProjection L k - Ch01.bandProjection L p) x := by
    simpa only [Int.cast_sub, hc, Ch01.bandProjection, Ch01.quotientMap] using
      (residue_character_int_cast L ζ hζ (k.val - p.val) (x.val : ℤ)).symm
  simp_rw [he]
  rw [character_sum L ζ hζ]
  have hi : Ch01.bandProjection L k - Ch01.bandProjection L p = 0 ↔ k = p :=
    sub_eq_zero.trans (Ch01.band_projection_bijective L
      (Nat.pos_of_ne_zero (NeZero.ne L))).injective.eq_iff
  simp only [hi]

lemma dual_character_orthogonality (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (x y : Ch01.Lattice L) :
    (∑ k : Ch01.Band L, integerCharacter ζ k.val ((x.val : ℤ) - (y.val : ℤ))) =
      if x = y then (L : K) else 0 := by
  classical
  have hc (r : Ch01.Lattice L) : ((r.val : ℤ) : Ch01.Lattice L) = r := by simp
  have he (k : Ch01.Band L) : integerCharacter ζ k.val ((x.val : ℤ) - (y.val : ℤ)) =
      residueCharacter L ζ (x - y) (Ch01.bandProjection L k) := by
    have h := residue_character_int_cast L ζ hζ ((x.val : ℤ) - (y.val : ℤ)) k.val
    simpa only [Int.cast_sub, hc, Ch01.bandProjection, Ch01.quotientMap,
      integerCharacter, mul_comm] using h.symm
  simp_rw [he]
  rw [sum_band_eq_sum_lattice, character_sum L ζ hζ]
  simp only [sub_eq_zero]

lemma canonical_root_primitive (L : ℕ) [NeZero L] :
    IsPrimitiveRoot (canonicalRoot L) L := by
  exact Complex.isPrimitiveRoot_exp L (NeZero.ne L)

lemma canonical_character_std (L : ℕ) [NeZero L] (k x : Ch01.Lattice L) :
    residueCharacter L (canonicalRoot L) k x = ZMod.stdAddChar (k * x) := by
  have hc (r : Ch01.Lattice L) : ((r.val : ℤ) : Ch01.Lattice L) = r := by simp
  rw [← hc k, ← hc x, residue_character_int_cast L (canonicalRoot L)
    (canonical_root_primitive L), ← Int.cast_mul, ZMod.stdAddChar_coe]
  unfold integerCharacter canonicalRoot
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

lemma complex_character_conj (L : ℕ) [NeZero L] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) :
    star (integerCharacter ζ k x) = integerCharacter ζ (-k) x := by
  have hn : ‖integerCharacter ζ k x‖ = 1 := by
    unfold integerCharacter
    rw [norm_zpow, hζ.norm'_eq_one (NeZero.ne L), one_zpow]
  have hi : star (integerCharacter ζ k x) = (integerCharacter ζ k x)⁻¹ :=
    (Complex.inv_eq_conj hn).symm
  rw [hi]
  simp [integerCharacter]

lemma complex_character_norm (L : ℕ) [NeZero L] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) : ‖integerCharacter ζ k x‖ = 1 := by
  unfold integerCharacter
  rw [norm_zpow, hζ.norm'_eq_one (NeZero.ne L), one_zpow]

lemma normalization_pos (L : ℕ) [NeZero L] : 0 < normalization L := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)))

lemma normalization_square (L : ℕ) [NeZero L] :
    (L : ℝ) * normalization L ^ 2 = 1 := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold normalization
  rw [inv_pow, Real.sq_sqrt hL.le]
  exact mul_inv_cancel₀ hL.ne'

lemma normalization_conj (L : ℕ) :
    star (normalization L : ℂ) = (normalization L : ℂ) := by
  simp

lemma normalization_square_complex (L : ℕ) [NeZero L] :
    (L : ℂ) * (normalization L : ℂ) ^ 2 = 1 := by
  exact_mod_cast normalization_square L

/-- Scalar contract needed by later position CAR, without asserting a CAR model here. -/
lemma normalization_car_coefficient (L : ℕ) [NeZero L] :
    ‖(normalization L : ℂ)‖ ^ 2 * (L : ℝ) = 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (normalization_pos L)]
  nlinarith [normalization_square L]

lemma singleton_character (ζ : K) (hζ : IsPrimitiveRoot ζ 1)
    (k : Ch01.Band 1) (x : Ch01.Lattice 1) : bandCharacter 1 ζ k x = 1 := by
  cases hζ
  simp [bandCharacter, integerCharacter, Ch01.singleton_band k]

lemma nyquist_character_neg (L : ℕ) [NeZero L] (hEven : Even L)
    (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L)
    (hk : k.val = ((L / 2 : ℕ) : ℤ)) (x : Ch01.Lattice L) :
    integerCharacter ζ (-k.val) (x.val : ℤ) = bandCharacter L ζ k x := by
  rw [← band_character_neg L ζ hζ,
    Ch01.nyquist_neg L (Nat.pos_of_ne_zero (NeZero.ne L)) hEven k hk]

end Bosonize.A01
```
