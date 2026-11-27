module

public import Bosonize.Core.CoupledWire.DualityMatrix
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Coupled-Wire Boundary Defects, Summation by Parts & `D^T` Transpose Algebra

Extends `DualityMatrix` with OBC/PBC link-operator boundary theorems and the finite-`2m`
duality-transpose operator map:
- discrete summation by parts under both PBC (`S_PBC^T Δ_PBC = -Δ_PBC^T S_PBC`) and OBC;
- exact interior vanishing `(Δ_OBC D + P Δ_OBC)_{y,z} = 0` (`y + 1 < n`), rank-1 OBC/PBC
  closing-row boundary defects, and squared Frobenius norms (`n` for OBC, `4n` for even PBC);
- `dualityTransposeApply`: exact U(1) charge conservation, even-wire involution `(D^T)^2 = I_{2m}`,
  strict locality for neutral operators, and `(D A D^T)_{y,z} = -A_{y,z}`.
-/

@[expose] public section

namespace Bosonize.CoupledWire

open scoped BigOperators

/-- Open-boundary square difference operator `Δ_OBC` (`n × n`). -/
def obcDiffEntry (n y z : ℕ) : ℤ :=
  if y + 1 < n then diffLinkEntry y z
  else if y + 1 = n then (if y = z then -1 else 0)
  else 0

/-- Naive periodic-difference operator `Δ_PBC` (`n × n`) with wrap link `n - 1 → 0`. -/
def pbcDiffEntry (n y z : ℕ) : ℤ :=
  if y + 1 < n then diffLinkEntry y z
  else if y + 1 = n then (if z = 0 then 1 else 0) - (if y = z then 1 else 0)
  else 0

/-- Naive periodic-sum operator `S_PBC` (`n × n`) with wrap link `n - 1 → 0`. -/
def pbcShiftEntry (n y z : ℕ) : ℤ :=
  if y + 1 < n then shiftLinkEntry y z
  else if y + 1 = n then (if z = 0 then 1 else 0) + (if y = z then 1 else 0)
  else 0

/-- Action of `D^T` mapping a dual-fermion exponent vector `q` to its electron exponent
vector `(D^T q)_z = ∑_{k < n} q_k D_{k,z}`. -/
def dualityTransposeApply (n : ℕ) (q : ℕ → ℤ) (z : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, q k * dualityEntry k z

/-! ### 1. Discrete Summation by Parts (PBC & OBC) -/

/-- Discrete summation by parts under PBC (MAM Eq. B7): `S_PBC^T Δ_PBC = -Δ_PBC^T S_PBC`. -/
theorem summation_by_parts_pbc (n i j : ℕ) (hn : 2 ≤ n) :
    ∑ y ∈ Finset.range n, pbcShiftEntry n y i * pbcDiffEntry n y j =
      -∑ y ∈ Finset.range n, pbcDiffEntry n y i * pbcShiftEntry n y j := by
  have hsum_zero :
      ∑ y ∈ Finset.range n,
        (pbcShiftEntry n y i * pbcDiffEntry n y j + pbcDiffEntry n y i * pbcShiftEntry n y j) = 0 := by
    have hstep : ∀ y ∈ Finset.range n,
        pbcShiftEntry n y i * pbcDiffEntry n y j + pbcDiffEntry n y i * pbcShiftEntry n y j =
          2 * ((if (y + 1) % n = i ∧ (y + 1) % n = j then (1 : ℤ) else 0) -
               (if y = i ∧ y = j then (1 : ℤ) else 0)) := by
      intro y hy
      have hy' : y < n := Finset.mem_range.mp hy
      by_cases hlt : y + 1 < n
      · have hmod : (y + 1) % n = y + 1 := Nat.mod_eq_of_lt hlt
        simp only [pbcShiftEntry, pbcDiffEntry, shiftLinkEntry, diffLinkEntry, hlt, hmod, ↓reduceIte]
        split_ifs <;> omega
      · have heq : y + 1 = n := by omega
        have hmod : (y + 1) % n = 0 := by rw [heq, Nat.mod_self]
        rw [hmod]
        simp only [pbcShiftEntry, pbcDiffEntry, heq, lt_self_iff_false, ↓reduceIte]
        split_ifs <;> omega
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
    have htele : ∀ k ≤ n,
        ∑ y ∈ Finset.range k,
          ((if (y + 1) % n = i ∧ (y + 1) % n = j then (1 : ℤ) else 0) -
           (if y = i ∧ y = j then (1 : ℤ) else 0)) =
        (if k % n = i ∧ k % n = j then (1 : ℤ) else 0) - (if 0 = i ∧ 0 = j then (1 : ℤ) else 0) := by
      intro k hk
      induction k with
      | zero => simp; omega
      | succ k ih =>
        rw [Finset.sum_range_succ, ih (Nat.le_of_lt hk), Nat.mod_eq_of_lt hk]; ring
    rw [htele n (le_refl n), Nat.mod_self, sub_self, mul_zero]
  rw [Finset.sum_add_distrib] at hsum_zero
  omega

/-- Open-link discrete summation by parts:
`S_link^T Δ_link + Δ_link^T S_link = 2 (e_{n-1} e_{n-1}^T - e_0 e_0^T)` for `n ≥ 2`. -/
theorem summation_by_parts_obc (n i j : ℕ) (_hn : 2 ≤ n) :
    ∑ y ∈ Finset.range (n - 1),
      (shiftLinkEntry y i * diffLinkEntry y j + diffLinkEntry y i * shiftLinkEntry y j) =
      (if i = n - 1 ∧ j = n - 1 then 2 else 0) - (if i = 0 ∧ j = 0 then 2 else 0) := by
  have hstep : ∀ y ∈ Finset.range (n - 1),
      shiftLinkEntry y i * diffLinkEntry y j + diffLinkEntry y i * shiftLinkEntry y j =
        (if i = y + 1 ∧ j = y + 1 then (2 : ℤ) else 0) -
          (if i = y ∧ j = y then (2 : ℤ) else 0) := by
    intro y _; unfold shiftLinkEntry diffLinkEntry; split_ifs <;> omega
  rw [Finset.sum_congr rfl hstep]
  exact Finset.sum_range_sub (fun m => if i = m ∧ j = m then (2 : ℤ) else 0) (n - 1)

/-! ### 2. Rank-1 Closing-Row Defects & Squared Frobenius Norms (OBC & PBC) -/

/-- Exact vanishing of `(Δ_OBC D + P Δ_OBC)_{y,z}` on every interior link row `y < n - 1`. -/
theorem obc_interior_row_defect_zero (n y z : ℕ) (hy : y + 1 < n) :
    (∑ k ∈ Finset.range n, obcDiffEntry n y k * dualityEntry k z) +
      paritySign y * obcDiffEntry n y z = 0 := by
  have hrew : ∀ k ∈ Finset.range n,
      obcDiffEntry n y k * dualityEntry k z =
        (if k = y + 1 then dualityEntry (y + 1) z else 0) +
        (if k = y then -dualityEntry y z else 0) := by
    intro k _
    simp only [obcDiffEntry, hy, ↓reduceIte, diffLinkEntry]
    by_cases h1 : k = y + 1
    · subst h1; simp
    · by_cases h2 : k = y
      · rw [h2]; simp
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range n) (y + 1), Finset.sum_ite_eq' (Finset.range n) y]
  simp only [Finset.mem_range.mpr hy, Finset.mem_range.mpr (by omega : y < n),
    obcDiffEntry, hy, ↓reduceIte]
  have hint := interior_delta_duality_exact y z
  linarith

/-- Full rank-1 OBC closing-row defect: `(Δ_OBC D + P Δ_OBC)_{n-1,z} = -(-1)^z`. -/
theorem obc_defect_row (n z : ℕ) (hn : 2 ≤ n) (hz : z < n) :
    (∑ k ∈ Finset.range n, obcDiffEntry n (n - 1) k * dualityEntry k z) +
      paritySign (n - 1) * obcDiffEntry n (n - 1) z = -paritySign z := by
  have heq : (n - 1) + 1 = n := by omega
  have hrew : ∀ k ∈ Finset.range n,
      obcDiffEntry n (n - 1) k * dualityEntry k z =
        if k = n - 1 then -dualityEntry (n - 1) z else 0 := by
    intro k _
    simp only [obcDiffEntry, heq, lt_self_iff_false, ↓reduceIte]
    by_cases hk : k = n - 1
    · subst hk; simp
    · simp [hk, Ne.symm hk]
  rw [Finset.sum_congr rfl hrew, Finset.sum_ite_eq' (Finset.range n) (n - 1)]
  simp only [Finset.mem_range.mpr (by omega : n - 1 < n), obcDiffEntry, heq,
    lt_self_iff_false, ↓reduceIte]
  unfold dualityEntry skewSignEntry
  by_cases hzn : n - 1 = z
  · subst hzn; simp
  · simp [hzn, show z < n - 1 by omega]

theorem obc_boundary_defect_nonzero (N : ℕ) (hN : 2 ≤ N) :
    (∑ k ∈ Finset.range N, obcDiffEntry N (N - 1) k * dualityEntry k 0) +
      paritySign (N - 1) * obcDiffEntry N (N - 1) 0 = -1 := by
  simpa [paritySign] using obc_defect_row N 0 hN (by omega)

/-- Squared Frobenius norm of the OBC closing-row defect equals `n` for all `n ≥ 2`. -/
theorem obc_defect_row_frobenius_sq (n : ℕ) (hn : 2 ≤ n) :
    ∑ z ∈ Finset.range n,
      ((∑ k ∈ Finset.range n, obcDiffEntry n (n - 1) k * dualityEntry k z) +
        paritySign (n - 1) * obcDiffEntry n (n - 1) z) ^ 2 = (n : ℤ) := by
  have hrew : ∀ z ∈ Finset.range n,
      ((∑ k ∈ Finset.range n, obcDiffEntry n (n - 1) k * dualityEntry k z) +
        paritySign (n - 1) * obcDiffEntry n (n - 1) z) ^ 2 = (1 : ℤ) := by
    intro z hz
    rw [obc_defect_row n z hn (Finset.mem_range.mp hz), neg_sq, sq, paritySign_sq]
  rw [Finset.sum_congr rfl hrew, Finset.sum_const, Finset.card_range]; simp

private theorem pbc_closing_row_eval (n z : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.range n, pbcDiffEntry n (n - 1) k * dualityEntry k z) +
      paritySign (n - 1) * pbcDiffEntry n (n - 1) z =
      dualityEntry 0 z - dualityEntry (n - 1) z +
        paritySign (n - 1) * ((if z = 0 then (1 : ℤ) else 0) - (if n - 1 = z then 1 else 0)) := by
  have heq : (n - 1) + 1 = n := by omega
  have hrew : ∀ k ∈ Finset.range n,
      pbcDiffEntry n (n - 1) k * dualityEntry k z =
        (if k = 0 then dualityEntry 0 z else 0) +
        (if k = n - 1 then -dualityEntry (n - 1) z else 0) := by
    intro k _
    simp only [pbcDiffEntry, heq, lt_self_iff_false, ↓reduceIte]
    by_cases hk0 : k = 0
    · subst hk0; simp [show (0 : ℕ) ≠ n - 1 by omega, show n - 1 ≠ 0 by omega]
    · by_cases hkn : k = n - 1
      · subst hkn; simp [hk0]
      · simp [hk0, hkn, Ne.symm hkn]
  rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range n) 0, Finset.sum_ite_eq' (Finset.range n) (n - 1)]
  simp only [Finset.mem_range.mpr (by omega : 0 < n), Finset.mem_range.mpr (by omega : n - 1 < n),
    pbcDiffEntry, heq, lt_self_iff_false, ↓reduceIte]
  ring

/-- Full rank-1 naive PBC closing-row defect for even `n`: `-2 * (-1)^z`. -/
theorem pbc_defect_row_even (n z : ℕ) (hn : 2 ≤ n) (heven : n % 2 = 0) (hz : z < n) :
    (∑ k ∈ Finset.range n, pbcDiffEntry n (n - 1) k * dualityEntry k z) +
      paritySign (n - 1) * pbcDiffEntry n (n - 1) z = -(2 * paritySign z) := by
  rw [pbc_closing_row_eval n z hn]
  unfold dualityEntry skewSignEntry paritySign; split_ifs <;> omega

/-- Odd-wire naive PBC closing-row defect: `-2 (-1)^z (1 - δ_{z,0})`. -/
theorem pbc_defect_row_odd (n z : ℕ) (hn : 3 ≤ n) (hodd : n % 2 = 1) (hz : z < n) :
    (∑ k ∈ Finset.range n, pbcDiffEntry n (n - 1) k * dualityEntry k z) +
      paritySign (n - 1) * pbcDiffEntry n (n - 1) z =
      if z = 0 then 0 else -(2 * paritySign z) := by
  rw [pbc_closing_row_eval n z (by omega)]
  unfold dualityEntry skewSignEntry paritySign; split_ifs <;> omega

theorem pbc_boundary_defect_nonzero (N : ℕ) (hN : 3 ≤ N) :
    (dualityEntry 0 1 - dualityEntry (N - 1) 1) +
      paritySign (N - 1) * ((if (1 : ℕ) = 0 then (1 : ℤ) else 0) -
        (if N - 1 = 1 then (1 : ℤ) else 0)) = 2 := by
  have h1 : (1 : ℕ) < N - 1 := by omega
  have h2 : N - 1 ≠ 1 := by omega
  simp [dualityEntry, skewSignEntry, paritySign, h1, h2]

/-- Squared Frobenius norm of the even-wire naive PBC closing-row defect equals `4n`. -/
theorem pbc_defect_row_even_frobenius_sq (n : ℕ) (hn : 2 ≤ n) (heven : n % 2 = 0) :
    ∑ z ∈ Finset.range n,
      ((∑ k ∈ Finset.range n, pbcDiffEntry n (n - 1) k * dualityEntry k z) +
        paritySign (n - 1) * pbcDiffEntry n (n - 1) z) ^ 2 = 4 * (n : ℤ) := by
  have hrew : ∀ z ∈ Finset.range n,
      ((∑ k ∈ Finset.range n, pbcDiffEntry n (n - 1) k * dualityEntry k z) +
        paritySign (n - 1) * pbcDiffEntry n (n - 1) z) ^ 2 = (4 : ℤ) := by
    intro z hz
    rw [pbc_defect_row_even n z hn heven (Finset.mem_range.mp hz)]
    have hsq := paritySign_sq z
    nlinarith
  rw [Finset.sum_congr rfl hrew, Finset.sum_const, Finset.card_range]; simp; ring

/-! ### 3. Duality Transpose Charge Conservation, Involution, Locality & `D A D^T = -A` -/

/-- Exact U(1) charge conservation on ANY finite even wire array `N = 2m`:
`∑_z (D^T q)_z = ∑_k q_k`. -/
theorem dualityTranspose_charge_conservation (m : ℕ) (q : ℕ → ℤ) :
    ∑ z ∈ Finset.range (2 * m), dualityTransposeApply (2 * m) q z =
      ∑ k ∈ Finset.range (2 * m), q k := by
  simp only [dualityTransposeApply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.mul_sum, duality_row_sum_even m k (Finset.mem_range.mp hk), mul_one]

/-- Exact even-wire involution `(D^T)^2 = I_{2m}` on operator exponent vectors. -/
theorem dualityTranspose_involution (m : ℕ) (q : ℕ → ℤ) (z : ℕ) (hz : z < 2 * m) :
    dualityTransposeApply (2 * m) (dualityTransposeApply (2 * m) q) z = q z := by
  simp only [dualityTransposeApply]
  have hpull :
      ∑ k ∈ Finset.range (2 * m), (∑ j ∈ Finset.range (2 * m), q j * dualityEntry j k) * dualityEntry k z =
      ∑ k ∈ Finset.range (2 * m), ∑ j ∈ Finset.range (2 * m), q j * (dualityEntry j k * dualityEntry k z) := by
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => mul_assoc _ _ _)
  rw [hpull, Finset.sum_comm]
  have hrew : ∀ j ∈ Finset.range (2 * m),
      ∑ k ∈ Finset.range (2 * m), q j * (dualityEntry j k * dualityEntry k z) =
        if j = z then q z else 0 := by
    intro j hj
    rw [← Finset.mul_sum, dualitySq_even m j z (Finset.mem_range.mp hj) hz]
    split_ifs with h <;> simp [h]
  rw [Finset.sum_congr rfl hrew, Finset.sum_ite_eq' (Finset.range (2 * m)) z]
  simp [Finset.mem_range.mpr hz]

/-- Exact locality theorem: any neutral dual operator supported in `[a, b]` maps under `D^T`
to a strictly local electron operator also supported in `[a, b]`. -/
theorem dualityTranspose_locality (n a b z : ℕ) (q : ℕ → ℤ)
    (hsupp : ∀ k, k < n → (k < a ∨ b < k) → q k = 0)
    (hneutral : ∑ k ∈ Finset.range n, q k = 0)
    (hout : z < a ∨ b < z) :
    dualityTransposeApply n q z = 0 := by
  simp only [dualityTransposeApply]
  rcases hout with hlt | hgt
  · have hrew : ∀ k ∈ Finset.range n, q k * dualityEntry k z = q k * paritySign z := by
      intro k hk
      by_cases hka : k < a
      · rw [hsupp k (Finset.mem_range.mp hk) (Or.inl hka), zero_mul, zero_mul]
      · simp [dualityEntry, skewSignEntry, show k ≠ z by omega, show z < k by omega]
    rw [Finset.sum_congr rfl hrew, ← Finset.sum_mul, hneutral, zero_mul]
  · have hrew : ∀ k ∈ Finset.range n, q k * dualityEntry k z = q k * (-paritySign z) := by
      intro k hk
      by_cases hkb : b < k
      · rw [hsupp k (Finset.mem_range.mp hk) (Or.inr hkb), zero_mul, zero_mul]
      · simp [dualityEntry, skewSignEntry, show k ≠ z by omega, show ¬ (z < k) by omega]
    rw [Finset.sum_congr rfl hrew, ← Finset.sum_mul, hneutral, zero_mul]

/-- Exact finite-`N_y = 2m` matrix identity `(D A D^T)_{y,z} = -A_{y,z}` for ALL `m, y, z < 2m`. -/
theorem duality_skewSign_flip_even (m y z : ℕ) (hy : y < 2 * m) (_hz : z < 2 * m) :
    ∑ j ∈ Finset.range (2 * m), ∑ k ∈ Finset.range (2 * m),
      dualityEntry y j * skewSignEntry j k * dualityEntry z k = -skewSignEntry y z := by
  have hrew : ∀ j ∈ Finset.range (2 * m),
      ∑ k ∈ Finset.range (2 * m), dualityEntry y j * skewSignEntry j k * dualityEntry z k =
      ∑ k ∈ Finset.range (2 * m), (dualityEntry y j * dualityEntry j k) * (paritySign k * dualityEntry z k) := by
    intro j _; apply Finset.sum_congr rfl; intro k _
    rw [← dualityEntry_mul_parity_eq_skewSign j k]; ring
  rw [Finset.sum_congr rfl hrew, Finset.sum_comm]
  have hinner : ∀ k ∈ Finset.range (2 * m),
      ∑ j ∈ Finset.range (2 * m), (dualityEntry y j * dualityEntry j k) * (paritySign k * dualityEntry z k) =
        if k = y then paritySign y * dualityEntry z y else 0 := by
    intro k hk
    rw [← Finset.sum_mul, dualitySq_even m y k hy (Finset.mem_range.mp hk)]
    by_cases hky : k = y
    · subst hky; simp
    · simp [hky, Ne.symm hky]
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq' (Finset.range (2 * m)) y]
  simp only [Finset.mem_range.mpr hy, ↓reduceIte]
  rw [dualityEntry_eq_skewSign_mul_parity z y, skewSignEntry_skew y z]
  have hsq := paritySign_sq y
  linear_combination -(skewSignEntry y z) * hsq

end Bosonize.CoupledWire
