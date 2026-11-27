module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Finset.Range
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Coupled-Wire Duality Matrix Core Algebra (Mross–Alicea–Motrunich, arXiv:1510.08455)

Constructive finite-`N` parity, skew-sign, duality, and interior link-difference algebra over `ℤ`
built on pinned Mathlib4 `Finset.sum`:
- `P_{y,z} = (-1)^y δ_{y,z}`, `A_{y,z} = (1 - δ_{y,z}) sgn(y - z)`, `D = A P`;
- exact even-wire involution `D^2 = I_{2m}` vs. odd-wire diagonal failure & constant kernel;
- universal chirality factorizations `D P D^T = -D^2 P`, `D^T P D = -P D^2`, `P D = -(D^T P)`,
  `D P D^T = D^T P D = -P` (even `2m`), `Tr(D^2) = 2m`, `P S P = -Δ`, and `Δ D = -P Δ`.
-/

@[expose] public section

namespace Bosonize.CoupledWire

open scoped BigOperators

/-- Alternating wire parity `(-1)^y` over `ℤ`. -/
def paritySign (y : ℕ) : ℤ :=
  if y % 2 = 0 then 1 else -1

/-- Antisymmetric off-diagonal wire sign matrix `A_{y,z} = (1 - δ_{y,z}) sgn(y - z)`. -/
def skewSignEntry (y z : ℕ) : ℤ :=
  if y = z then 0 else if z < y then 1 else -1

/-- Non-local Mross–Alicea–Motrunich duality matrix entry
`D_{y,z} = (1 - δ_{y,z}) sgn(y - z) (-1)^z = A_{y,z} (-1)^z`. -/
def dualityEntry (y z : ℕ) : ℤ :=
  skewSignEntry y z * paritySign z

/-- Interior forward difference matrix entry `Δ_{y,z} = δ_{y+1,z} - δ_{y,z}`. -/
def diffLinkEntry (y z : ℕ) : ℤ :=
  if y + 1 = z then 1 else if y = z then -1 else 0

/-- Interior forward sum matrix entry `S_{y,z} = δ_{y+1,z} + δ_{y,z}`. -/
def shiftLinkEntry (y z : ℕ) : ℤ :=
  if y + 1 = z then 1 else if y = z then 1 else 0

/-! ### 1. Wire Parity & Skew-Sign Identities -/

theorem paritySign_sq (y : ℕ) : paritySign y * paritySign y = 1 := by
  unfold paritySign; split_ifs <;> norm_num

theorem paritySign_succ (y : ℕ) : paritySign (y + 1) = -paritySign y := by
  unfold paritySign; split_ifs <;> omega

theorem paritySign_add_two (y : ℕ) : paritySign (y + 2) = paritySign y := by
  rw [paritySign_succ, paritySign_succ, neg_neg]

theorem paritySign_add_three (y : ℕ) : paritySign (y + 3) = -paritySign y := by
  rw [show y + 3 = (y + 2) + 1 by omega, paritySign_succ, paritySign_add_two]

theorem paritySign_add_six (y : ℕ) : paritySign (y + 6) = paritySign y := by
  rw [show y + 6 = (y + 3) + 3 by omega, paritySign_add_three, paritySign_add_three, neg_neg]

theorem paritySign_mul_succ (y : ℕ) : paritySign y * paritySign (y + 1) = -1 := by
  rw [paritySign_succ, mul_neg, paritySign_sq]

theorem paritySign_three_mul_add (y r : ℕ) :
    paritySign (3 * y + r) = paritySign y * paritySign r := by
  unfold paritySign; split_ifs <;> omega

theorem skewSignEntry_diag (y : ℕ) : skewSignEntry y y = 0 := by
  simp [skewSignEntry]

theorem skewSignEntry_skew (y z : ℕ) : skewSignEntry z y = -skewSignEntry y z := by
  unfold skewSignEntry; split_ifs <;> omega

theorem dualityEntry_eq_skewSign_mul_parity (y z : ℕ) :
    dualityEntry y z = skewSignEntry y z * paritySign z :=
  rfl

theorem dualityEntry_mul_parity_eq_skewSign (y z : ℕ) :
    dualityEntry y z * paritySign z = skewSignEntry y z := by
  rw [dualityEntry, mul_assoc, paritySign_sq, mul_one]

theorem dualityEntry_diag (y : ℕ) : dualityEntry y y = 0 := by
  simp [dualityEntry, skewSignEntry]

/-- Signed parity sum `∑_{k=0}^{n-1} (-1)^k`: `0` if `n` is even, `1` if `n` is odd. -/
theorem sum_range_paritySign (n : ℕ) :
    ∑ k ∈ Finset.range n, paritySign k = if n % 2 = 0 then 0 else 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    unfold paritySign; split_ifs <;> omega

theorem sum_paritySign_even (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m), paritySign k = 0 := by
  rw [sum_range_paritySign]; simp

private theorem sum_range_sub_indicator (n a b : ℕ) (hab : a ≤ b) (hb : b ≤ n) (f : ℕ → ℤ) :
    ∑ k ∈ Finset.range n, (if a ≤ k ∧ k < b then f k else 0) =
      (∑ k ∈ Finset.range b, f k) - ∑ k ∈ Finset.range a, f k := by
  have hsub : (Finset.range n).filter (fun k => a ≤ k ∧ k < b) = Finset.Ico a b := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [← Finset.sum_filter, hsub]
  have hsplit := Finset.sum_range_add_sum_Ico f hab
  omega

/-! ### 2. Even-Wire Involution `D^2 = I_{2m}`, Odd Failure & Chirality Factorizations -/

private theorem dualityProd_diag_general (n y : ℕ) (hy : y < n) :
    ∑ k ∈ Finset.range n, dualityEntry y k * dualityEntry k y =
      -(∑ k ∈ Finset.range n, paritySign k) * paritySign y + 1 := by
  have hrew : ∀ k ∈ Finset.range n,
      dualityEntry y k * dualityEntry k y =
        -(paritySign k * paritySign y) + (if k = y then 1 else 0) := by
    intro k _
    by_cases hky : k = y
    · subst hky; simp [dualityEntry, skewSignEntry, paritySign_sq]
    · simp only [dualityEntry, skewSignEntry, hky, Ne.symm hky, ↓reduceIte]
      by_cases hlt : k < y
      · have hgt : ¬ (y < k) := by omega
        simp [hlt, hgt]
      · have hgt : y < k := by omega
        simp [hlt, hgt]
  rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.sum_mul, Finset.sum_ite_eq' (Finset.range n) y]
  simp [Finset.mem_range.mpr hy]

private theorem dualityProd_lt (m y z : ℕ) (hyz : y < z) (hz : z < 2 * m) :
    ∑ k ∈ Finset.range (2 * m), dualityEntry y k * dualityEntry k z = 0 := by
  have hy : y < 2 * m := Nat.lt_trans hyz hz
  have hrew : ∀ k ∈ Finset.range (2 * m),
      dualityEntry y k * dualityEntry k z =
        -(paritySign k * paritySign z)
        + (if k = y then paritySign y * paritySign z else 0)
        + (if k = z then (1 : ℤ) else 0)
        + 2 * ((if y + 1 ≤ k ∧ k < z then paritySign k else 0) * paritySign z) := by
    intro k _
    by_cases hky : k = y
    · subst hky
      simp [dualityEntry, skewSignEntry, Nat.ne_of_lt hyz]
    · by_cases hkz : k = z
      · subst hkz
        simp [dualityEntry, skewSignEntry, hky, Nat.ne_of_lt hyz, paritySign_sq]
      · simp only [dualityEntry, skewSignEntry, hky, Ne.symm hky, hkz, ↓reduceIte]
        by_cases hk1 : k < y
        · have hk2 : k < z := Nat.lt_trans hk1 hyz
          have hgtz : ¬ (z < k) := by omega
          have hny : ¬ (y < k) := by omega
          simp [hk1, hk2, hgtz, hny]
        · by_cases hk2 : k < z
          · have hmem : y + 1 ≤ k ∧ k < z := ⟨by omega, hk2⟩
            have hgtz : ¬ (z < k) := by omega
            simp [hk1, hk2, hgtz, hmem]; ring
          · have hgtz : z < k := by omega
            simp [hk1, hk2, hgtz]
  rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul, sum_paritySign_even,
    Finset.sum_ite_eq' (Finset.range (2 * m)) y, Finset.sum_ite_eq' (Finset.range (2 * m)) z,
    ← Finset.mul_sum, ← Finset.sum_mul,
    sum_range_sub_indicator (2 * m) (y + 1) z (by omega) (Nat.le_of_lt hz) paritySign,
    sum_range_paritySign z, sum_range_paritySign (y + 1)]
  simp only [Finset.mem_range.mpr hy, Finset.mem_range.mpr hz, ↓reduceIte]
  unfold paritySign; split_ifs <;> omega

/-- Exact finite-lattice involution `D^2 = I_{2m}` for ALL even wire counts `N = 2m`. -/
theorem dualitySq_even (m y z : ℕ) (hy : y < 2 * m) (hz : z < 2 * m) :
    ∑ k ∈ Finset.range (2 * m), dualityEntry y k * dualityEntry k z =
      if y = z then 1 else 0 := by
  by_cases hyz : y = z
  · subst hyz
    simp only [↓reduceIte]
    rw [dualityProd_diag_general (2 * m) y hy, sum_paritySign_even]; ring
  · simp only [hyz, ↓reduceIte]
    by_cases hlt : y < z
    · exact dualityProd_lt m y z hlt hz
    · have hgt : z < y := by omega
      have hsym : ∀ k ∈ Finset.range (2 * m),
          dualityEntry y k * dualityEntry k z =
            (paritySign z * paritySign y) * (dualityEntry z k * dualityEntry k y) := by
        intro k _
        have h1 : skewSignEntry y k * skewSignEntry k z =
            skewSignEntry z k * skewSignEntry k y := by
          unfold skewSignEntry; split_ifs <;> omega
        have hpy := paritySign_sq y
        simp only [dualityEntry]
        linear_combination (paritySign k * paritySign z) * h1 -
          (skewSignEntry z k * skewSignEntry k y * paritySign k * paritySign z) * hpy
      rw [Finset.sum_congr rfl hsym, ← Finset.mul_sum, dualityProd_lt m z y hgt hy, mul_zero]

/-- General odd-wire diagonal failure: `(D^2)_{y,y}` alternates `0` (even `y`) and `2` (odd `y`). -/
theorem dualitySq_diag_odd (n y : ℕ) (hn : n % 2 = 1) (hy : y < n) :
    ∑ k ∈ Finset.range n, dualityEntry y k * dualityEntry k y =
      if y % 2 = 0 then 0 else 2 := by
  rw [dualityProd_diag_general n y hy, sum_range_paritySign n]
  unfold paritySign; split_ifs <;> omega

private theorem duality_row_sum_general (n y : ℕ) (hy : y < n) :
    ∑ k ∈ Finset.range n, dualityEntry y k =
      -(∑ k ∈ Finset.range n, paritySign k) + paritySign y +
        2 * (∑ k ∈ Finset.range y, paritySign k) := by
  have hrew : ∀ k ∈ Finset.range n,
      dualityEntry y k =
        -paritySign k + (if k = y then paritySign y else 0) +
          2 * (if 0 ≤ k ∧ k < y then paritySign k else 0) := by
    intro k _
    unfold dualityEntry skewSignEntry
    by_cases hky : k = y
    · subst hky; simp
    · by_cases hlt : k < y
      · simp [hky, Ne.symm hky, hlt]; ring
      · simp [hky, Ne.symm hky, hlt]
  rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, Finset.sum_ite_eq' (Finset.range n) y,
    ← Finset.mul_sum,
    sum_range_sub_indicator n 0 y (Nat.zero_le y) (Nat.le_of_lt hy) paritySign]
  simp [Finset.mem_range.mpr hy]

/-- For ANY odd `n`, the all-ones vector lies in `ker(D)`: `∑_{k < n} D_{y,k} = 0`. -/
theorem duality_const_kernel_odd (n y : ℕ) (hn : n % 2 = 1) (hy : y < n) :
    ∑ k ∈ Finset.range n, dualityEntry y k = 0 := by
  rw [duality_row_sum_general n y hy, sum_range_paritySign n, sum_range_paritySign y]
  unfold paritySign; split_ifs <;> omega

/-- Row-sum identity on any even array `N = 2m`: `∑_{z < 2m} D_{k,z} = 1`. -/
theorem duality_row_sum_even (m k : ℕ) (hk : k < 2 * m) :
    ∑ z ∈ Finset.range (2 * m), dualityEntry k z = 1 := by
  rw [duality_row_sum_general (2 * m) k hk, sum_paritySign_even, sum_range_paritySign k]
  unfold paritySign; split_ifs <;> omega

/-- Staggered parity transpose symmetry `P D = -(D^T P)` entrywise. -/
theorem dualityEntry_transpose_parity (y z : ℕ) :
    paritySign y * dualityEntry y z = -(dualityEntry z y * paritySign z) := by
  simp only [dualityEntry, skewSignEntry_skew y z]; ring

/-- Skew-symmetry `(P D)^T = -(P D)` entrywise. -/
theorem parityMulDuality_skew (y z : ℕ) :
    paritySign y * dualityEntry y z = -(paritySign z * dualityEntry z y) := by
  rw [dualityEntry_transpose_parity, mul_comm (dualityEntry z y)]

/-- Skew-symmetry `(D P)^T = -(D P)` entrywise. -/
theorem dualityMulParity_skew (y z : ℕ) :
    dualityEntry y z * paritySign z = -(dualityEntry z y * paritySign y) := by
  rw [dualityEntry_mul_parity_eq_skewSign, dualityEntry_mul_parity_eq_skewSign,
    skewSignEntry_skew y z, neg_neg]

/-- Theorem A (Universal Chirality-Square Factorization): `D P D^T = -D^2 P` for ALL `n`. -/
theorem duality_chirality_sq_factorization (n y z : ℕ) :
    ∑ k ∈ Finset.range n, dualityEntry y k * paritySign k * dualityEntry z k =
      -(∑ k ∈ Finset.range n, dualityEntry y k * dualityEntry k z) * paritySign z := by
  rw [← Finset.sum_neg_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  have hsym : paritySign k * dualityEntry z k = -(dualityEntry k z * paritySign z) := by
    rw [dualityEntry_eq_skewSign_mul_parity z k, dualityEntry_mul_parity_eq_skewSign k z,
      skewSignEntry_skew k z]
    have hpk := paritySign_sq k
    linear_combination -(skewSignEntry k z) * hpk
  linear_combination dualityEntry y k * hsym

/-- Transpose chirality-square factorization `D^T P D = -P D^2` for ALL `n`. -/
theorem duality_transpose_chirality_sq_factorization (n y z : ℕ) :
    ∑ k ∈ Finset.range n, dualityEntry k y * paritySign k * dualityEntry k z =
      -(paritySign y * ∑ k ∈ Finset.range n, dualityEntry y k * dualityEntry k z) := by
  rw [← neg_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have h := dualityEntry_transpose_parity y k
  linear_combination (dualityEntry k z) * h

/-- Exact chirality reversal `D P D^T = -P` for ALL even wire counts `N = 2m`. -/
theorem duality_chirality_flip_even (m y z : ℕ) (hy : y < 2 * m) (hz : z < 2 * m) :
    ∑ k ∈ Finset.range (2 * m), dualityEntry y k * paritySign k * dualityEntry z k =
      if y = z then -paritySign z else 0 := by
  rw [duality_chirality_sq_factorization, dualitySq_even m y z hy hz]
  split_ifs <;> simp

/-- Dual chirality compatibility `D^T P D = -P` for ALL even wire counts `N = 2m`. -/
theorem obc_dual_chirality_compatibility (m y z : ℕ) (hy : y < 2 * m) (hz : z < 2 * m) :
    ∑ k ∈ Finset.range (2 * m), dualityEntry k y * paritySign k * dualityEntry k z =
      if y = z then -paritySign y else 0 := by
  rw [duality_transpose_chirality_sq_factorization, dualitySq_even m y z hy hz]
  split_ifs <;> simp

/-- Trace of `D^2` on any finite even wire array `N = 2m` equals `2m`. -/
theorem duality_sq_sum_even_diag_trace (m : ℕ) :
    ∑ y ∈ Finset.range (2 * m), ∑ k ∈ Finset.range (2 * m),
      dualityEntry y k * dualityEntry k y = (2 * m : ℤ) := by
  have h : ∀ y ∈ Finset.range (2 * m),
      ∑ k ∈ Finset.range (2 * m), dualityEntry y k * dualityEntry k y = (1 : ℤ) := by
    intro y hy
    simpa using dualitySq_even m y y (Finset.mem_range.mp hy) (Finset.mem_range.mp hy)
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range]; simp

/-- Exact lattice identity `P S P = -Δ` on every interior link row `y` and site `z`. -/
theorem pspp_eq_neg_delta (y z : ℕ) :
    paritySign y * shiftLinkEntry y z * paritySign z = -diffLinkEntry y z := by
  unfold shiftLinkEntry diffLinkEntry
  by_cases h1 : y + 1 = z
  · subst h1; simp [paritySign_succ, paritySign_sq]
  · by_cases h2 : y = z
    · subst h2; simp [paritySign_sq]
    · simp [h1, h2]

/-- Exact interior link-row duality `(Δ D)_{y,z} = (-P Δ)_{y,z}` for all `y, z`. -/
theorem interior_delta_duality_exact (y z : ℕ) :
    dualityEntry (y + 1) z - dualityEntry y z = -paritySign y * diffLinkEntry y z := by
  unfold dualityEntry skewSignEntry diffLinkEntry
  by_cases h1 : z = y
  · subst h1; simp
  · by_cases h2 : z = y + 1
    · subst h2; simp [paritySign_succ]
    · simp only [show y + 1 ≠ z from Ne.symm h2, show y ≠ z from Ne.symm h1, ↓reduceIte, mul_zero]
      by_cases hlt : z < y
      · have hlt1 : z < y + 1 := Nat.lt_succ_of_lt hlt
        simp [hlt, hlt1]
      · have hgt : ¬ (z < y + 1) := by omega
        simp [hlt, hgt]

end Bosonize.CoupledWire
