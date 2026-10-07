module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-!
# Chapter 1: Lattice and band geometry

Phase A interface, following `notes/md/ch01_lattice_band_geometry.md`.
Definitions are complete; theorem bodies are intentionally staged for review.
The positive boundary is included and the negative boundary is excluded.
-/

@[expose] public section

namespace Bosonize.Ch01

/-- The periodic spatial lattice. All geometric claims require `0 < L`. -/
abbrev Lattice (L : ℕ) := ZMod L

/-- The exact centered-band condition from equation (1.2). -/
def inBand (L : ℕ) (k : ℤ) : Prop := -(L : ℤ) < 2 * k ∧ 2 * k ≤ (L : ℤ)

instance (L : ℕ) (k : ℤ) : Decidable (inBand L k) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Band momenta retain their actual signed integer labels. -/
abbrev Band (L : ℕ) := {k : ℤ // inBand L k}

/-- A computable enumeration of the exact band, without a parity assumption. -/
def bandFinset (L : ℕ) : Finset ℤ :=
  (Finset.Icc (-(L : ℤ)) (L : ℤ)).filter (inBand L)

instance (L : ℕ) : Fintype (Band L) :=
  Fintype.ofFinset (bandFinset L) (by
    intro k
    change k ∈ bandFinset L ↔ inBand L k
    simp only [bandFinset, Finset.mem_filter, Finset.mem_Icc]
    unfold inBand
    omega)

/-- The canonical quotient projection, equation (1.3). -/
def quotientMap (L : ℕ) (k : ℤ) : Lattice L := (k : ZMod L)

/-- The quotient projection restricted to the band. -/
def bandProjection (L : ℕ) (k : Band L) : Lattice L := quotientMap L k.val

/-- Center the standard residue in `[0,L)` at the positive Nyquist endpoint. -/
def representative (L : ℕ) (hL : 0 < L) (x : Lattice L) : Band L := by
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  have hx := ZMod.val_lt x
  exact if h : 2 * (x.val : ℤ) ≤ (L : ℤ) then
    ⟨(x.val : ℤ), by unfold inBand; omega⟩
  else
    ⟨(x.val : ℤ) - (L : ℤ), by unfold inBand; omega⟩

/-- Transported band addition, equation (1.5). -/
def bandAdd (L : ℕ) (hL : 0 < L) (k p : Band L) : Band L :=
  representative L hL (bandProjection L k + bandProjection L p)

/-- Transported band negation, equation (1.6). -/
def bandNeg (L : ℕ) (hL : 0 < L) (k : Band L) : Band L :=
  representative L hL (-bandProjection L k)

/-- A concrete zero momentum witnesses that every positive-size band is inhabited. -/
def zeroMomentum (L : ℕ) (hL : 0 < L) : Band L :=
  ⟨0, by unfold inBand; omega⟩

theorem mem_band_finset (L : ℕ) (k : ℤ) :
    k ∈ bandFinset L ↔ inBand L k := by sorry

theorem zero_mem_band (L : ℕ) (hL : 0 < L) : inBand L 0 := by sorry

theorem card_band_finset (L : ℕ) (hL : 0 < L) :
    (bandFinset L).card = L := by sorry

theorem card_band (L : ℕ) (hL : 0 < L) :
    Fintype.card (Band L) = L := by sorry

/-- First inverse identity, including the section condition in equation (1.4). -/
theorem projection_representative (L : ℕ) (hL : 0 < L) (x : Lattice L) :
    bandProjection L (representative L hL x) = x := by sorry

/-- Second inverse identity establishes uniqueness of the centered representative. -/
theorem representative_projection (L : ℕ) (hL : 0 < L) (k : Band L) :
    representative L hL (bandProjection L k) = k := by sorry

theorem band_projection_bijective (L : ℕ) (hL : 0 < L) :
    Function.Bijective (bandProjection L) := by sorry

theorem representative_unique (L : ℕ) (hL : 0 < L) (x : Lattice L) (k : Band L)
    (hk : bandProjection L k = x) : k = representative L hL x := by sorry

/-- The wrapping integer lies in `{-1,0,1}` and is unique with this property. -/
theorem band_add_wrap (L : ℕ) (hL : 0 < L) (k p : Band L) :
    ∃! w : ℤ, (-1 ≤ w ∧ w ≤ 1) ∧
      (bandAdd L hL k p).val = k.val + p.val - w * (L : ℤ) := by sorry

theorem band_add_projection (L : ℕ) (hL : 0 < L) (k p : Band L) :
    bandProjection L (bandAdd L hL k p) =
      bandProjection L k + bandProjection L p := by sorry

theorem band_neg_projection (L : ℕ) (hL : 0 < L) (k : Band L) :
    bandProjection L (bandNeg L hL k) = -bandProjection L k := by sorry

theorem band_add_assoc (L : ℕ) (hL : 0 < L) (k p q : Band L) :
    bandAdd L hL (bandAdd L hL k p) q = bandAdd L hL k (bandAdd L hL p q) := by sorry

theorem band_add_comm (L : ℕ) (hL : 0 < L) (k p : Band L) :
    bandAdd L hL k p = bandAdd L hL p k := by sorry

theorem band_zero_add (L : ℕ) (hL : 0 < L) (k : Band L) :
    bandAdd L hL (zeroMomentum L hL) k = k := by sorry

theorem band_neg_add_cancel (L : ℕ) (hL : 0 < L) (k : Band L) :
    bandAdd L hL (bandNeg L hL k) k = zeroMomentum L hL := by sorry

/-- The even-size interval includes the positive endpoint and omits the negative one. -/
theorem even_band_bounds (L : ℕ) (hL : 0 < L) (hEven : Even L) (k : ℤ) :
    inBand L k ↔ -((L / 2 : ℕ) : ℤ) + 1 ≤ k ∧ k ≤ ((L / 2 : ℕ) : ℤ) := by sorry

/-- Equation (1.9), stated for a band element with the Nyquist integer label. -/
theorem nyquist_neg (L : ℕ) (hL : 0 < L) (hEven : Even L) (k : Band L)
    (hk : k.val = ((L / 2 : ℕ) : ℤ)) : bandNeg L hL k = k := by sorry

/-- Equation (1.10): ordinary integer negation away from the even Nyquist mode. -/
theorem band_neg_of_ne_nyquist (L : ℕ) (hL : 0 < L) (hEven : Even L)
    (k : Band L) (hk : k.val ≠ ((L / 2 : ℕ) : ℤ)) :
    (bandNeg L hL k).val = -k.val := by sorry

theorem odd_band_neg (L : ℕ) (hL : 0 < L) (hOdd : Odd L) (k : Band L) :
    (bandNeg L hL k).val = -k.val := by sorry

/-- At `L = 1`, the entire band consists of zero. -/
theorem singleton_band (k : Band 1) : k.val = 0 := by sorry

end Bosonize.Ch01
