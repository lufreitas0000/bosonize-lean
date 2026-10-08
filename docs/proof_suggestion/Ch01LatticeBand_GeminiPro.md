module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-!
# Chapter 1: Lattice and band geometry

Phase A interface, following `notes/md/ch01_lattice_band_geometry.md`.
Definitions are complete; lemma bodies are rigorously implemented.
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

-- ==============================================================================
-- PHASE 1: Basic Presburger Arithmetic (Kinematics)
-- ==============================================================================

lemma mem_band_finset (L : ℕ) (k : ℤ) :
    k ∈ bandFinset L ↔ inBandPredicate L k := by
  simp only [bandFinset, Finset.mem_filter, Finset.mem_Icc]
  unfold inBandPredicate
  omega

lemma zero_mem_band (L : ℕ) (hL : 0 < L) : inBandPredicate L 0 := by
  unfold inBandPredicate
  omega

lemma singleton_band (k : Band 1) : k.val = 0 := by
  have hk := k.property
  unfold inBandPredicate at hk
  omega

lemma even_band_bounds (L : ℕ) (hL : 0 < L) (hEven : Even L) (k : ℤ) :
    inBandPredicate L k ↔ -((L / 2 : ℕ) : ℤ) + 1 ≤ k ∧ k ≤ ((L / 2 : ℕ) : ℤ) := by
  obtain ⟨n, rfl⟩ := hEven
  unfold inBandPredicate
  omega

-- ==============================================================================
-- HELPER LEMMA FOR ZMOD ARITHMETIC AVOIDANCE
-- ==============================================================================

/-- A highly robust helper to evaluate internal ZMod integer values dynamically. -/
private lemma zmod_val_of_bounds (L : ℕ) (x : ℤ) (h1 : 0 ≤ x) (h2 : x < (L : ℤ)) :
    (((x : ZMod L).val : ℤ)) = x := by
  lift x to ℕ using h1
  norm_cast at h2
  have h_cast : ((x : ℤ) : ZMod L) = (x : ZMod L) := by push_cast; rfl
  rw [h_cast]
  have h_val : (x : ZMod L).val = x % L := ZMod.val_natCast x
  rw [h_val, Nat.mod_eq_of_lt h2]

-- ==============================================================================
-- PHASE 2: Quotient-Section Isomorphism (The Bridge)
-- ==============================================================================

lemma projection_representative (L : ℕ) (hL : 0 < L) (x : Lattice L) :
    bandProjection L (representative L hL x) = x := by
  unfold bandProjection quotientMap representative
  split_ifs
  · exact ZMod.natCast_zmod_val x
  · push_cast
    have h_L : ((L : ℤ) : ZMod L) = 0 := by simp
    rw [h_L, sub_zero]
    exact ZMod.natCast_zmod_val x

lemma representative_projection (L : ℕ) (hL : 0 < L) (k : Band L) :
    representative L hL (bandProjection L k) = k := by
  apply Subtype.ext
  have hk := k.property
  unfold inBandPredicate at hk
  unfold representative bandProjection quotientMap
  dsimp only
  have h_val : (((k.val : ZMod L).val : ℤ)) = if 0 ≤ k.val then k.val else k.val + (L : ℤ) := by
    split_ifs with h_pos
    · exact zmod_val_of_bounds L k.val h_pos (by omega)
    · have h_cast : (k.val : ZMod L) = ((k.val + (L : ℤ) : ℤ) : ZMod L) := by push_cast; simp
      rw [h_cast]
      exact zmod_val_of_bounds L (k.val + (L : ℤ)) (by omega) (by omega)
  rw [h_val]
  split_ifs <;> omega

lemma band_projection_bijective (L : ℕ) (hL : 0 < L) :
    Function.Bijective (bandProjection L) := by
  rw [Function.bijective_iff_has_inverse]
  use (representative L hL)
  constructor
  · intro k; exact representative_projection L hL k
  · intro x; exact projection_representative L hL x

lemma representative_unique (L : ℕ) (hL : 0 < L) (x : Lattice L) (k : Band L)
    (hk : bandProjection L k = x) : k = representative L hL x := by
  have h_app := congrArg (representative L hL) hk
  rw [representative_projection L hL k] at h_app
  exact h_app

-- ==============================================================================
-- PHASE 3: Homomorphic Transport (Dynamics)
-- ==============================================================================

lemma band_add_projection (L : ℕ) (hL : 0 < L) (k p : Band L) :
    bandProjection L (bandAdd L hL k p) =
      bandProjection L k + bandProjection L p := by
  unfold bandAdd
  rw [projection_representative L hL]

lemma band_neg_projection (L : ℕ) (hL : 0 < L) (k : Band L) :
    bandProjection L (bandNeg L hL k) = -bandProjection L k := by
  unfold bandNeg
  rw [projection_representative L hL]

lemma band_add_assoc (L : ℕ) (hL : 0 < L) (k p q : Band L) :
    bandAdd L hL (bandAdd L hL k p) q = bandAdd L hL k (bandAdd L hL p q) := by
  apply (band_projection_bijective L hL).injective
  repeat rw [band_add_projection]
  exact add_assoc _ _ _

lemma band_add_comm (L : ℕ) (hL : 0 < L) (k p : Band L) :
    bandAdd L hL k p = bandAdd L hL p k := by
  apply (band_projection_bijective L hL).injective
  repeat rw [band_add_projection]
  exact add_comm _ _

lemma band_zero_add (L : ℕ) (hL : 0 < L) (k : Band L) :
    bandAdd L hL (zeroMomentum L hL) k = k := by
  apply (band_projection_bijective L hL).injective
  rw [band_add_projection]
  have h_zero : bandProjection L (zeroMomentum L hL) = 0 := rfl
  rw [h_zero, zero_add]

lemma band_neg_add_cancel (L : ℕ) (hL : 0 < L) (k : Band L) :
    bandAdd L hL (bandNeg L hL k) k = zeroMomentum L hL := by
  apply (band_projection_bijective L hL).injective
  rw [band_add_projection, band_neg_projection]
  have h_zero : bandProjection L (zeroMomentum L hL) = 0 := rfl
  rw [h_zero]
  exact neg_add_cancel _

-- ==============================================================================
-- PHASE 4: Cardinality & Fine Geometric Exceptions
-- ==============================================================================

lemma card_band (L : ℕ) (hL : 0 < L) :
    Fintype.card (Band L) = L := by
  have e : Band L ≃ Lattice L := Equiv.ofBijective _ (band_projection_bijective L hL)
  rw [Fintype.card_congr e]
  exact ZMod.card L

lemma card_band_finset (L : ℕ) (hL : 0 < L) :
    (bandFinset L).card = L := by
  change Fintype.card (Band L) = L
  exact card_band L hL

lemma band_add_wrap (L : ℕ) (hL : 0 < L) (k p : Band L) :
    ∃! w : ℤ, (-1 ≤ w ∧ w ≤ 1) ∧
      (bandAdd L hL k p).val = k.val + p.val - w * (L : ℤ) := by
  have hk := k.property; have hp := p.property
  unfold inBandPredicate at hk hp
  unfold bandAdd representative bandProjection quotientMap
  dsimp only
  have h_val : (((k.val + p.val : ℤ) : ZMod L).val : ℤ) =
      if k.val + p.val < 0 then k.val + p.val + (L : ℤ)
      else if k.val + p.val < (L : ℤ) then k.val + p.val
      else k.val + p.val - (L : ℤ) := by
    split_ifs with h1 h2
    · have h_cast : ((k.val + p.val : ℤ) : ZMod L) = ((k.val + p.val + (L : ℤ) : ℤ) : ZMod L) := by push_cast; simp
      rw [h_cast]; exact zmod_val_of_bounds L _ (by omega) (by omega)
    · exact zmod_val_of_bounds L _ (by omega) (by omega)
    · have h_cast : ((k.val + p.val : ℤ) : ZMod L) = ((k.val + p.val - (L : ℤ) : ℤ) : ZMod L) := by push_cast; simp
      rw [h_cast]; exact zmod_val_of_bounds L _ (by omega) (by omega)
  rw [h_val]
  split_ifs
  any_goals { use -1; constructor; omega; intro w' hw'; omega }
  any_goals { use 0; constructor; omega; intro w' hw'; omega }
  any_goals { use 1; constructor; omega; intro w' hw'; omega }

lemma nyquist_neg (L : ℕ) (hL : 0 < L) (hEven : Even L) (k : Band L)
    (hk : k.val = ((L / 2 : ℕ) : ℤ)) : bandNeg L hL k = k := by
  obtain ⟨n, rfl⟩ := hEven
  apply Subtype.ext
  unfold bandNeg representative bandProjection quotientMap
  dsimp only
  have h_val : (((-k.val : ℤ) : ZMod (2 * n)).val : ℤ) = k.val := by
    have h_cast : ((-k.val : ℤ) : ZMod (2 * n)) = ((k.val : ℤ) : ZMod (2 * n)) := by
      rw [hk]
      have : (-(n : ℤ) : ZMod (2 * n)) = ((-(n : ℤ) + (2 * n : ℤ) : ℤ) : ZMod (2 * n)) := by push_cast; simp
      rw [this]
      have : -(n : ℤ) + (2 * n : ℤ) = (n : ℤ) := by omega
      rw [this]
    rw [h_cast]
    exact zmod_val_of_bounds (2 * n) k.val (by omega) (by rw [hk]; omega)
  rw [h_val]
  split_ifs <;> omega

lemma band_neg_of_ne_nyquist (L : ℕ) (hL : 0 < L) (hEven : Even L)
    (k : Band L) (hk : k.val ≠ ((L / 2 : ℕ) : ℤ)) :
    (bandNeg L hL k).val = -k.val := by
  obtain ⟨n, rfl⟩ := hEven
  unfold bandNeg representative bandProjection quotientMap
  dsimp only
  have hk_prop := k.property
  unfold inBandPredicate at hk_prop
  have h_val : (((-k.val : ℤ) : ZMod (2 * n)).val : ℤ) =
      if -k.val < 0 then -k.val + (2 * n : ℤ) else -k.val := by
    split_ifs with h_neg
    · have h_cast : ((-k.val : ℤ) : ZMod (2 * n)) = ((-k.val + (2 * n : ℤ) : ℤ) : ZMod (2 * n)) := by push_cast; simp
      rw [h_cast]
      exact zmod_val_of_bounds (2 * n) _ (by omega) (by omega)
    · exact zmod_val_of_bounds (2 * n) _ (by omega) (by omega)
  rw [h_val]
  split_ifs <;> omega

lemma odd_band_neg (L : ℕ) (hL : 0 < L) (hOdd : Odd L) (k : Band L) :
    (bandNeg L hL k).val = -k.val := by
  obtain ⟨n, rfl⟩ := hOdd
  unfold bandNeg representative bandProjection quotientMap
  dsimp only
  have hk_prop := k.property
  unfold inBandPredicate at hk_prop
  have h_val : (((-k.val : ℤ) : ZMod (2 * n + 1)).val : ℤ) =
      if -k.val < 0 then -k.val + (2 * n + 1 : ℤ) else -k.val := by
    split_ifs with h_neg
    · have h_cast : ((-k.val : ℤ) : ZMod (2 * n + 1)) = ((-k.val + (2 * n + 1 : ℤ) : ℤ) : ZMod (2 * n + 1)) := by push_cast; simp
      rw [h_cast]
      exact zmod_val_of_bounds (2 * n + 1) _ (by omega) (by omega)
    · exact zmod_val_of_bounds (2 * n + 1) _ (by omega) (by omega)
  rw [h_val]
  split_ifs <;> omega

end Bosonize.Ch01