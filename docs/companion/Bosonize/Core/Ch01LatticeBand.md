# Chapter 1 lab notebook: Lattice and band geometry

Status (2026-10-08): **Phase C complete. All 20 lemmas are proved, audited, and promoted to `Bosonize/Core/Ch01LatticeBand.lean`.** The approved definitions, instances, lemma names, hypotheses, and conclusions are preserved. The v2 lock entry was migrated from staging to Core with every header/command/context hash unchanged, and `core_locks.json` now freezes the complete source, including proof bodies. The Lean namespace remains `Bosonize.Ch01`.

Source: `notes/md/ch01_lattice_band_geometry.md`, definitions 1.1–1.3 and lemma 1.4, equations (1.1)–(1.10). `notes/md/TOC.md` places this chapter before umbral calculus and Fourier transforms.

## Representation and rationale

The namespace is `Bosonize.Ch01`. `Lattice L` is Mathlib's `ZMod L`. Geometric operations and claims explicitly require `hL : 0 < L`; `ZMod 0` is not treated as a finite spatial lattice.

`Band L` is the subtype of signed integers satisfying `inBandPredicate L k`, exactly `-(L : ℤ) < 2*k ∧ 2*k ≤ (L : ℤ)`. The strict lower and inclusive upper bounds preserve the positive Nyquist endpoint. `bandFinset` enumerates these labels by filtering `[-L,L]`. Its complete `Fintype` instance supports downstream finite sums.

`quotientMap` casts an integer into `ZMod L`, and `bandProjection` restricts this map to the band. `representative` returns the standard residue `a = x.val` when `2*a ≤ L`, and `a-L` otherwise. Its membership proofs are part of the approved definition. `bandAdd` and `bandNeg` transport quotient addition and negation through this representative. `zeroMomentum` is a completely constructed witness for every positive `L`.

All these definitions and instances are unchanged. No global `Equiv` or group instance was added: the cardinality proof constructs an equivalence locally, and the arithmetic proofs use projection injectivity. Physical scaling by `2π/L` remains context rather than a new real-valued definition in this chapter.

## Proof strategy and dependencies

The source states the exact claims but supplies no detailed tactic-level sketches. The proof suggestion's broad dependency order was considered; the final proofs use elementary integer bounds and quotient uniqueness instead of repeated case analysis on raw residue values.

1. **Elementary geometry.** `mem_band_finset` unfolds the enumeration and checks the surrounding interval is redundant. `zero_mem_band`, `singleton_band`, and `even_band_bounds` use exact integer arithmetic (`omega`), with parity expanded into its witness. This establishes the singleton and even-boundary cases without changing any hypotheses.
2. **Quotient/representative inverse identities.** `projection_representative` splits the representative's two branches. Casting a residue gives back its quotient class; subtracting `L` gives the same class. `representative_projection` then avoids expanding dependent subtype terms: both labels lie in the centered band and have the same quotient class, so `L` divides their difference. The band inequalities bound either nonnegative difference strictly below `L`. Mathlib's `Int.eq_zero_of_dvd_of_nonneg_of_lt` forces that difference to be zero. These two identities give `band_projection_bijective` and `representative_unique`.
3. **Cardinality.** `card_band` constructs `Band L ≃ ZMod L` locally from the bijection and applies `Fintype.card_congr` followed by `ZMod.card`. Positivity supplies the local `NeZero L` instance. `card_band_finset` uses `Fintype.card_of_subtype` and `mem_band_finset`; finset cardinality and subtype cardinality are related by a proved theorem rather than assumed definitionally equal.
4. **Transported arithmetic.** The projection of band addition or negation equals the corresponding quotient operation by `projection_representative`. Apply projection injectivity to prove associativity, commutativity, zero addition, and negation cancellation using the ordinary `ZMod` laws. Projection of zero is simplified from the actual definitions rather than asserted with `rfl`.
5. **Wrapping.** Put `s = k.val + p.val`. If `2*s ≤ -L`, choose `w = -1` and candidate `s+L`. If `L < 2*s`, choose `w = 1` and candidate `s-L`. Otherwise choose `w = 0` and candidate `s`. The two input-band bounds show each selected candidate lies in the band. Its quotient is the sum of the original quotient classes, so representative uniqueness identifies it with `bandAdd`. If two wrapping integers give the same result, their products with `L` agree; since `L > 0`, multiplication cancellation proves uniqueness. The candidate and uniqueness arguments are local proof facts, not new top-level declarations.
6. **Nyquist and odd negation.** At the even Nyquist label, `-k.val = k.val-L`, so the two integer labels project to the same quotient class; injectivity proves self-negation. Away from that endpoint, the even-band bounds show `-k.val` itself lies in the band. For odd `L`, the symmetric bounds do so for every band label. In both cases representative uniqueness identifies the negated label with `bandNeg`.

Lemmas were reordered within their common frozen context to respect dependencies. The guard permits this, and all 20 locked headers and 24 non-lemma command entries still match the committed baseline. No import, definition, instance, or new top-level helper was needed.

## Source coverage

| Source | Lean declarations |
| --- | --- |
| (1.1) | `Lattice` |
| (1.2) | `inBandPredicate`, `Band`, `bandFinset` |
| (1.3) | `quotientMap`, `bandProjection` |
| (1.4) | `representative`, `projection_representative` |
| (1.5), (1.6) | `bandAdd`, `bandNeg` |
| (1.7) | `card_band_finset`, `card_band` |
| Lemma 1.4(2) | `representative_projection`, `band_projection_bijective`, `representative_unique` |
| (1.8) | `band_add_wrap` |
| (1.9) | `nyquist_neg` |
| (1.10) | `band_neg_of_ne_nyquist` |

Supporting lemmas cover finite enumeration, a zero witness, transported group laws, odd negation, and `L=1`. Evenness is restricted to the even-band/Nyquist statements. No energy or Fermi-sea constraints are introduced in this chapter.

## Critical use of suggestions

Consulted `docs/proof_suggestion/Ch01LatticeBand_GeminiPro.md`. Its order of basic geometry, inverse identities, transported laws, and exceptional modes was useful. Its supplied code previously failed compiler checks: the wrong arguments to `ZMod.val_natCast`, missing positivity instances, dependent rewrites, projection-of-zero `rfl` claims, and a finset/subtype cardinality `change` did not work with the installed toolchain. The final proofs avoid those steps. In particular, quotient uniqueness replaces its raw-residue helper and long residue case analysis; no suggested top-level helper was added.

`docs/stub_suggestion/chapter_2_umbral_calculus_core.md` concerns the next chapter. It was not adopted here. Its unfinished `umbralMap`/`polyForwardDiff` definitions and unrestricted finite-lattice summation remain issues for a future chapter-2 interface review.

## Validation

The native Lean MCP tools are not exposed in this chat, so validation used the installed project compiler and local Mathlib sources. No remote search or extra installation was required.

- Before promotion, strict verification against commit `d5af479` confirmed all 20 statement headers and 24 command entries. Promotion preserved the entire recorded entry, changing only its source path.
- After promotion, `make ci`: all 65 guard tests, both freeze guards, and both Lean library builds pass without warnings. The Core build treats warnings as errors.
- `core_lock.py` verifies the complete promoted source hash; its regression tests reject proof-body, comment, file-deletion, and unreviewed-file changes.
- No `sorry`, `admit`, custom `axiom`, or `unsafe` token remains in the chapter.
- `#print axioms` for every lemma reports only standard Lean axioms; no lemma depends on `sorryAx`.

The audit commands were run from the project root. The axiom inspection imported the freshly built chapter in a temporary file, removed after execution. The complete output is recorded below. The final axiom audit imports `Bosonize`, verifying all 20 declarations through the Core aggregator. The legacy v1 baseline remains historical evidence. The active v2 entry changes only its source path, while the new Core manifest records the complete source hash. Both guards can verify against the resulting promotion commit using `--baseline-ref`.

## Core promotion and immutable source

The Lean file was moved without changing its bytes. `Bosonize.lean` imports `Bosonize.Core.Ch01LatticeBand`; staging imports `Bosonize` and no longer contains a chapter-1 stub. The companion notebook follows the source under `docs/companion/Bosonize/Core/`.

`stub_lock.py` scans staging and Core, preserving the approved interface record. `core_lock.py` checks a SHA-256 manifest for every complete Core source file and has no update command. Core files are now protected against proof edits as well as definition/statement edits. Explicitly authorized future promotions may add new Core files and manifest entries while preserving existing entries. CI runs both guards.

## Axiom audit output

```text
'Bosonize.Ch01.mem_band_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch01.zero_mem_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch01.singleton_band' depends on axioms: [propext, Quot.sound]
'Bosonize.Ch01.even_band_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch01.projection_representative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch01.representative_projection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch01.band_projection_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch01.representative_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch01.card_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch01.card_band_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch01.band_add_projection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch01.band_neg_projection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch01.band_add_assoc' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch01.band_add_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch01.band_zero_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch01.band_neg_add_cancel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch01.band_add_wrap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch01.nyquist_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch01.band_neg_of_ne_nyquist' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch01.odd_band_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Exact proved source

```lean
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-!
# Chapter 1: Lattice and band geometry

Phase B proofs, following `notes/md/ch01_lattice_band_geometry.md`.
All 20 lemma bodies are proved; definitions and statements preserve the approved freeze.
The positive boundary is included and the negative boundary is excluded.
-/

@[expose] public section

namespace Bosonize.Ch01

/-- The periodic spatial lattice. All geometric claims require `0 < L`. -/
abbrev Lattice (L : ℕ) := ZMod L

/-- The predicate for centered-band. -/
def inBandPredicate (L : ℕ) (k : ℤ) : Prop := -(L : ℤ) < 2 * k ∧ 2 * k ≤ (L : ℤ)

instance (L : ℕ) (k : ℤ) : Decidable (inBandPredicate L k) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Band subtype. Actual signed integer labels. -/
abbrev Band (L : ℕ) := {k : ℤ // inBandPredicate L k}

/-- A computable enumeration of the exact band, without a parity assumption. -/
def bandFinset (L : ℕ) : Finset ℤ :=
  (Finset.Icc (-(L : ℤ)) (L : ℤ)).filter (inBandPredicate L)

instance (L : ℕ) : Fintype (Band L) :=
  Fintype.ofFinset (bandFinset L) (by
    intro k
    change k ∈ bandFinset L ↔ inBandPredicate L k
    simp only [bandFinset, Finset.mem_filter, Finset.mem_Icc]
    unfold inBandPredicate
    omega)

/-- The canonical quotient projection. -/
def quotientMap (L : ℕ) (k : ℤ) : Lattice L := (k : ZMod L)

/-- The quotient projection restricted to the band. -/
def bandProjection (L : ℕ) (k : Band L) : Lattice L := quotientMap L k.val

/-- Center the standard residue in `[0,L)` at the positive Nyquist endpoint. -/
def representative (L : ℕ) (hL : 0 < L) (x : Lattice L) : Band L := by
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  have hx := ZMod.val_lt x
  exact if h : 2 * (x.val : ℤ) ≤ (L : ℤ) then
    ⟨(x.val : ℤ), by unfold inBandPredicate; omega⟩
  else
    ⟨(x.val : ℤ) - (L : ℤ), by unfold inBandPredicate; omega⟩

/-- Transported band addition, equation (1.5). -/
def bandAdd (L : ℕ) (hL : 0 < L) (k p : Band L) : Band L :=
  representative L hL (bandProjection L k + bandProjection L p)

/-- Transported band negation, equation (1.6). -/
def bandNeg (L : ℕ) (hL : 0 < L) (k : Band L) : Band L :=
  representative L hL (-bandProjection L k)

/-- A concrete zero momentum witnesses that every positive-size band is inhabited. -/
def zeroMomentum (L : ℕ) (hL : 0 < L) : Band L :=
  ⟨0, by unfold inBandPredicate; omega⟩

lemma mem_band_finset (L : ℕ) (k : ℤ) :
    k ∈ bandFinset L ↔ inBandPredicate L k := by
  simp only [bandFinset, Finset.mem_filter, Finset.mem_Icc]
  unfold inBandPredicate
  omega

lemma zero_mem_band (L : ℕ) (hL : 0 < L) : inBandPredicate L 0 := by
  unfold inBandPredicate
  omega

/-- At `L = 1`, the entire band consists of zero. -/
lemma singleton_band (k : Band 1) : k.val = 0 := by
  have hk := k.property
  unfold inBandPredicate at hk
  omega

/-- The even-size interval includes the positive endpoint and omits the negative one. -/
lemma even_band_bounds (L : ℕ) (hL : 0 < L) (hEven : Even L) (k : ℤ) :
    inBandPredicate L k ↔ -((L / 2 : ℕ) : ℤ) + 1 ≤ k ∧ k ≤ ((L / 2 : ℕ) : ℤ) := by
  have hne := Nat.ne_of_gt hL
  obtain ⟨n, hn⟩ := hEven
  unfold inBandPredicate
  omega

/-- First inverse identity, including the section condition in equation (1.4). -/
lemma projection_representative (L : ℕ) (hL : 0 < L) (x : Lattice L) :
    bandProjection L (representative L hL x) = x := by
  let _ : NeZero L := ⟨Nat.ne_of_gt hL⟩
  unfold bandProjection quotientMap representative
  split
  · simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val x
  · simpa only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_self, sub_zero]
      using ZMod.natCast_zmod_val x

/-- Second inverse identity establishes uniqueness of the centered representative. -/
lemma representative_projection (L : ℕ) (hL : 0 < L) (k : Band L) :
    representative L hL (bandProjection L k) = k := by
  apply Subtype.ext
  have ha := (representative L hL (bandProjection L k)).property
  have hk := k.property
  have he := projection_representative L hL (bandProjection L k)
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ L).mp he
  unfold inBandPredicate at ha hk
  by_cases h : (representative L hL (bandProjection L k)).val ≤ k.val
  · have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) hd
    omega
  · have hd' : (L : ℤ) ∣ (representative L hL (bandProjection L k)).val - k.val := by
      simpa only [neg_sub] using (dvd_neg.mpr hd)
    have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) hd'
    omega

lemma band_projection_bijective (L : ℕ) (hL : 0 < L) :
    Function.Bijective (bandProjection L) := by
  constructor
  · intro k p h
    have he := congrArg (representative L hL) h
    simpa only [representative_projection] using he
  · intro x
    exact ⟨representative L hL x, projection_representative L hL x⟩

lemma representative_unique (L : ℕ) (hL : 0 < L) (x : Lattice L) (k : Band L)
    (hk : bandProjection L k = x) : k = representative L hL x := by
  have he := congrArg (representative L hL) hk
  simpa only [representative_projection] using he

lemma card_band (L : ℕ) (hL : 0 < L) :
    Fintype.card (Band L) = L := by
  let _ : NeZero L := ⟨Nat.ne_of_gt hL⟩
  let e : Band L ≃ Lattice L := Equiv.ofBijective _ (band_projection_bijective L hL)
  exact (Fintype.card_congr e).trans (ZMod.card L)

lemma card_band_finset (L : ℕ) (hL : 0 < L) :
    (bandFinset L).card = L := by
  have hc : Fintype.card (Band L) = (bandFinset L).card :=
    Fintype.card_of_subtype (bandFinset L) (mem_band_finset L)
  rw [← hc]
  exact card_band L hL

lemma band_add_projection (L : ℕ) (hL : 0 < L) (k p : Band L) :
    bandProjection L (bandAdd L hL k p) =
      bandProjection L k + bandProjection L p := by
  exact projection_representative L hL _

lemma band_neg_projection (L : ℕ) (hL : 0 < L) (k : Band L) :
    bandProjection L (bandNeg L hL k) = -bandProjection L k := by
  exact projection_representative L hL _

lemma band_add_assoc (L : ℕ) (hL : 0 < L) (k p q : Band L) :
    bandAdd L hL (bandAdd L hL k p) q = bandAdd L hL k (bandAdd L hL p q) := by
  apply (band_projection_bijective L hL).injective
  simp only [band_add_projection, add_assoc]

lemma band_add_comm (L : ℕ) (hL : 0 < L) (k p : Band L) :
    bandAdd L hL k p = bandAdd L hL p k := by
  apply (band_projection_bijective L hL).injective
  simp only [band_add_projection, add_comm]

lemma band_zero_add (L : ℕ) (hL : 0 < L) (k : Band L) :
    bandAdd L hL (zeroMomentum L hL) k = k := by
  apply (band_projection_bijective L hL).injective
  rw [band_add_projection]
  have hz : bandProjection L (zeroMomentum L hL) = 0 := by
    simp [bandProjection, quotientMap, zeroMomentum]
  rw [hz, zero_add]

lemma band_neg_add_cancel (L : ℕ) (hL : 0 < L) (k : Band L) :
    bandAdd L hL (bandNeg L hL k) k = zeroMomentum L hL := by
  apply (band_projection_bijective L hL).injective
  rw [band_add_projection, band_neg_projection]
  have hz : bandProjection L (zeroMomentum L hL) = 0 := by
    simp [bandProjection, quotientMap, zeroMomentum]
  rw [hz, neg_add_cancel]

/-- The wrapping integer lies in `{-1,0,1}` and is unique with this property. -/
lemma band_add_wrap (L : ℕ) (hL : 0 < L) (k p : Band L) :
    ∃! w : ℤ, (-1 ≤ w ∧ w ≤ 1) ∧
      (bandAdd L hL k p).val = k.val + p.val - w * (L : ℤ) := by
  have hk := k.property
  have hp := p.property
  unfold inBandPredicate at hk hp
  have hcandidate (w : ℤ)
      (hb : inBandPredicate L (k.val + p.val - w * (L : ℤ))) :
      (bandAdd L hL k p).val = k.val + p.val - w * (L : ℤ) := by
    let q : Band L := ⟨k.val + p.val - w * (L : ℤ), hb⟩
    have he : bandProjection L q = bandProjection L k + bandProjection L p := by
      simp [q, bandProjection, quotientMap, Int.cast_sub, Int.cast_add, Int.cast_mul]
    have hr := representative_unique L hL (bandProjection L k + bandProjection L p) q he
    exact (congrArg Subtype.val hr).symm
  have hunique (w : ℤ) (he :
      (bandAdd L hL k p).val = k.val + p.val - w * (L : ℤ)) :
      ∀ w' : ℤ, (-1 ≤ w' ∧ w' ≤ 1) ∧
        (bandAdd L hL k p).val = k.val + p.val - w' * (L : ℤ) → w' = w := by
    intro w' ⟨hb, he'⟩
    have hm : w' * (L : ℤ) = w * (L : ℤ) := by omega
    exact (mul_right_cancel₀ (by omega : (L : ℤ) ≠ 0)) hm
  by_cases hlow : 2 * (k.val + p.val) ≤ -(L : ℤ)
  · have hb : inBandPredicate L (k.val + p.val - (-1) * (L : ℤ)) := by
      unfold inBandPredicate
      simp only [neg_one_mul, sub_neg_eq_add]
      omega
    have he := hcandidate (-1) hb
    exact ⟨-1, ⟨by omega, he⟩, hunique (-1) he⟩
  · by_cases hhigh : (L : ℤ) < 2 * (k.val + p.val)
    · have hb : inBandPredicate L (k.val + p.val - 1 * (L : ℤ)) := by
        unfold inBandPredicate
        simp only [one_mul]
        omega
      have he := hcandidate 1 hb
      exact ⟨1, ⟨by omega, he⟩, hunique 1 he⟩
    · have hb : inBandPredicate L (k.val + p.val - 0 * (L : ℤ)) := by
        unfold inBandPredicate
        simp only [zero_mul, sub_zero]
        omega
      have he := hcandidate 0 hb
      exact ⟨0, ⟨by omega, he⟩, hunique 0 he⟩

/-- Equation (1.9), stated for a band element with the Nyquist integer label. -/
lemma nyquist_neg (L : ℕ) (hL : 0 < L) (hEven : Even L) (k : Band L)
    (hk : k.val = ((L / 2 : ℕ) : ℤ)) : bandNeg L hL k = k := by
  apply (band_projection_bijective L hL).injective
  rw [band_neg_projection]
  have he : -k.val = k.val - (L : ℤ) := by
    obtain ⟨n, hn⟩ := hEven
    omega
  change -(k.val : ZMod L) = (k.val : ZMod L)
  rw [← Int.cast_neg, he]
  simp

/-- Equation (1.10): ordinary integer negation away from the even Nyquist mode. -/
lemma band_neg_of_ne_nyquist (L : ℕ) (hL : 0 < L) (hEven : Even L)
    (k : Band L) (hk : k.val ≠ ((L / 2 : ℕ) : ℤ)) :
    (bandNeg L hL k).val = -k.val := by
  have hb : inBandPredicate L (-k.val) := by
    have hbounds := (even_band_bounds L hL hEven k.val).mp k.property
    apply (even_band_bounds L hL hEven (-k.val)).mpr
    omega
  let p : Band L := ⟨-k.val, hb⟩
  have he : bandProjection L p = -bandProjection L k := by
    simp [p, bandProjection, quotientMap]
  have hr := representative_unique L hL (-bandProjection L k) p he
  exact (congrArg Subtype.val hr).symm

lemma odd_band_neg (L : ℕ) (hL : 0 < L) (hOdd : Odd L) (k : Band L) :
    (bandNeg L hL k).val = -k.val := by
  have hb : inBandPredicate L (-k.val) := by
    have hk := k.property
    unfold inBandPredicate at hk ⊢
    obtain ⟨n, hn⟩ := hOdd
    omega
  let p : Band L := ⟨-k.val, hb⟩
  have he : bandProjection L p = -bandProjection L k := by
    simp [p, bandProjection, quotientMap]
  have hr := representative_unique L hL (-bandProjection L k) p he
  exact (congrArg Subtype.val hr).symm

end Bosonize.Ch01

```
