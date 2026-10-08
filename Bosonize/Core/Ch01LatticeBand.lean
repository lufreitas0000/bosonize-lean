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
