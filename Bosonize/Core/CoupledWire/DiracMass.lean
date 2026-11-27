module

public import Bosonize.Core.CoupledWire.DualityMatrix
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Coupled-Wire Inter-Wire Dirac Mass Matrix & Chiral Edge Zero Modes

Formalizes the finite-`N_y` open-boundary alternating inter-wire pairing matrix
`M = wireMassEntry n t1 t2` coupling adjacent chiral wires (`even` right-movers, `odd` left-movers)
on pinned Mathlib4 `Finset.sum`:
- symmetry `M^T = M`, chiral anticommutation `P M + M P = 0`, and `(k P + M)^2 = k^2 I + M^T M`;
- uniform (`t1 = t2 = 1`) and general dimerized odd-wire (`N_y = 2m + 1`) chiral zero modes;
- exact even-wire (`N_y = 2m`) singular-value-squared matrix `M^T M`, topological (`t1 = 0`)
  `2×2` bulk dimers + 2D boundary kernel `span{e_0, e_{2m-1}}`, trivial (`t2 = 0`) bulk gap,
  exact finite-size kernel triviality `ker(M) = {0}` for all `t1 ≠ 0`, and the exact boundary
  residual `(M v)_y = δ_{y, 2m-1} (-(-t1)^m)`.
-/

@[expose] public section

namespace Bosonize.CoupledWire

open scoped BigOperators

/-- Open-boundary inter-wire Dirac mass matrix `M_{y,z}` on `n` wires with alternating bonds
`t1` on `(2j, 2j+1)` and `t2` on `(2j+1, 2j+2)`. -/
def wireMassEntry (n : ℕ) (t1 t2 : ℤ) (y z : ℕ) : ℤ :=
  if y < n ∧ z < n then
    if y + 1 = z then (if y % 2 = 0 then t1 else t2)
    else if z + 1 = y then (if z % 2 = 0 then t1 else t2)
    else 0
  else 0

/-- Closed-form entry of `M^T M` on `n` wires (exact for all even `n = 2m`, `m ≥ 1`). -/
def wireMassSqEntry (n : ℕ) (t1 t2 : ℤ) (y z : ℕ) : ℤ :=
  if y < n ∧ z < n then
    if y = z then (if y = 0 ∨ y + 1 = n then t1 * t1 else t1 * t1 + t2 * t2)
    else if y + 2 = z ∨ z + 2 = y then t1 * t2
    else 0
  else 0

/-- Alternating chiral zero-mode vector on odd-wire uniform OBC (`t1 = t2 = 1`),
supported strictly on even wires (`z = 0, 2, ..., 2m`). -/
def oddWireLeftZeroMode (z : ℕ) : ℤ :=
  if z % 2 = 0 then paritySign (z / 2) else 0

/-- General dimerized chiral zero-mode on odd wire counts `N_y = 2m + 1` for arbitrary `t1, t2 : ℤ`. -/
def dimerizedOddWireZeroMode (t1 t2 : ℤ) (m z : ℕ) : ℤ :=
  if z % 2 = 0 then (-t1) ^ (z / 2) * t2 ^ (m - z / 2) else 0

/-- Protected left boundary chiral wire (`y = 0`, right-mover `P = +1`). -/
def evenWireTopoLeftEdge (z : ℕ) : ℤ :=
  if z = 0 then 1 else 0

/-- Protected right boundary chiral wire (`y = n - 1`, left-mover `P = -1` for even `n ≥ 2`). -/
def evenWireTopoRightEdge (n z : ℕ) : ℤ :=
  if z + 1 = n then 1 else 0

/-- Exact finite-`N_y = 2m` left-boundary exponentially decaying chiral ansatz
`v_{2j} = (-t1)^j t2^{m - 1 - j}`, `v_{2j+1} = 0` (`m ≥ 1`). -/
def evenWireEdgeAnsatz (t1 t2 : ℤ) (m z : ℕ) : ℤ :=
  if z % 2 = 0 then (-t1) ^ (z / 2) * t2 ^ (m - 1 - z / 2) else 0

/-! ### 1. Symmetry, Chiral Anticommutation & Dirac Hamiltonian Square -/

theorem wireMassEntry_symm (n : ℕ) (t1 t2 : ℤ) (y z : ℕ) :
    wireMassEntry n t1 t2 y z = wireMassEntry n t1 t2 z y := by
  unfold wireMassEntry; split_ifs <;> omega

theorem wireMassEntry_chiral_anticomm (n : ℕ) (t1 t2 : ℤ) (y z : ℕ) :
    paritySign y * wireMassEntry n t1 t2 y z + wireMassEntry n t1 t2 y z * paritySign z = 0 := by
  unfold wireMassEntry
  split_ifs with h1 h2 _ h3 _
  · subst h2; rw [paritySign_succ]; ring
  · subst h2; rw [paritySign_succ]; ring
  · subst h3; rw [paritySign_succ]; ring
  · subst h3; rw [paritySign_succ]; ring
  · ring
  · ring

/-- Exact row evaluation of `M v` for any `y < n`. -/
theorem wireMass_row_eval (n : ℕ) (t1 t2 : ℤ) (v : ℕ → ℤ) (y : ℕ) (hy : y < n) :
    ∑ z ∈ Finset.range n, wireMassEntry n t1 t2 y z * v z =
      (if y + 1 < n then (if y % 2 = 0 then t1 else t2) * v (y + 1) else 0) +
      (if 0 < y then (if (y - 1) % 2 = 0 then t1 else t2) * v (y - 1) else 0) := by
  have hrew : ∀ z ∈ Finset.range n,
      wireMassEntry n t1 t2 y z * v z =
        (if z = y + 1 then (if y % 2 = 0 then t1 else t2) * v (y + 1) else 0) +
        (if z = y - 1 then (if 0 < y then (if (y - 1) % 2 = 0 then t1 else t2) * v (y - 1) else 0) else 0) := by
    intro z hz
    have hz' : z < n := Finset.mem_range.mp hz
    unfold wireMassEntry
    by_cases h1 : y + 1 = z
    · subst h1; simp [hy, hz', show y + 1 ≠ y - 1 by omega]
    · by_cases h2 : z + 1 = y
      · have hz_eq : z = y - 1 := by omega
        subst hz_eq
        simp [hy, hz', show y - 1 ≠ y + 1 by omega, show (y - 1) + 1 = y by omega,
          show 0 < y by omega, show ¬ (y + 1 = y - 1) by omega]
      · simp [hy, hz', h1, h2, show z ≠ y + 1 by omega]
        split_ifs <;> omega
  rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range n) (y + 1), Finset.sum_ite_eq' (Finset.range n) (y - 1)]
  by_cases hy0 : 0 < y
  · simp [Finset.mem_range, hy0, show y - 1 < n by omega]
  · simp [Finset.mem_range, hy0]

/-- Exact Dirac Hamiltonian square `(k P + M)^2 = k^2 I + M^T M` on `n` wires. -/
theorem wireDirac_sq_eq (n : ℕ) (k t1 t2 : ℤ) (y z : ℕ) (hy : y < n) (hz : z < n) :
    ∑ w ∈ Finset.range n,
      (k * (if y = w then paritySign y else 0) + wireMassEntry n t1 t2 y w) *
      (k * (if w = z then paritySign w else 0) + wireMassEntry n t1 t2 w z) =
      (if y = z then k * k else 0) +
        ∑ w ∈ Finset.range n, wireMassEntry n t1 t2 w y * wireMassEntry n t1 t2 w z := by
  have hrew : ∀ w ∈ Finset.range n,
      (k * (if y = w then paritySign y else 0) + wireMassEntry n t1 t2 y w) *
      (k * (if w = z then paritySign w else 0) + wireMassEntry n t1 t2 w z) =
        k * k * (if w = y then (if y = z then 1 else 0) else 0) +
        k * ((if w = y then paritySign y * wireMassEntry n t1 t2 y z else 0) +
             (if w = z then wireMassEntry n t1 t2 y z * paritySign z else 0)) +
        wireMassEntry n t1 t2 w y * wireMassEntry n t1 t2 w z := by
    intro w _
    rw [wireMassEntry_symm n t1 t2 w y]
    by_cases hwy : w = y
    · subst hwy
      by_cases hwz : w = z
      · subst hwz; simp; have hsq := paritySign_sq w; linear_combination (k * k) * hsq
      · simp [hwz]; ring
    · by_cases hwz : w = z
      · subst hwz; simp [hwy, Ne.symm hwy]; ring
      · simp [hwy, Ne.symm hwy, hwz]
  rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range n) y, Finset.sum_ite_eq' (Finset.range n) y,
    Finset.sum_ite_eq' (Finset.range n) z]
  simp only [Finset.mem_range.mpr hy, Finset.mem_range.mpr hz, ↓reduceIte,
    wireMassEntry_chiral_anticomm n t1 t2 y z, mul_zero, add_zero]
  split_ifs <;> ring

/-! ### 2. Odd-Wire Chiral Edge Zero Modes (`N_y = 2m + 1`) -/

theorem oddWireLeftZeroMode_even (k : ℕ) : oddWireLeftZeroMode (2 * k) = paritySign k := by
  simp [oddWireLeftZeroMode]

theorem oddWireLeftZeroMode_chiral (z : ℕ) :
    paritySign z * oddWireLeftZeroMode z = oddWireLeftZeroMode z := by
  unfold oddWireLeftZeroMode paritySign; split_ifs <;> simp

theorem oddWireLeftZeroMode_normSq (m : ℕ) :
    ∑ z ∈ Finset.range (2 * m + 1), oddWireLeftZeroMode z * oddWireLeftZeroMode z = (m + 1 : ℤ) := by
  induction m with
  | zero => simp [oddWireLeftZeroMode, paritySign]
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have hodd : (2 * m + 1) % 2 ≠ 0 := by omega
    have heven : (2 * m + 2) % 2 = 0 := by omega
    simp only [oddWireLeftZeroMode, hodd, heven, ↓reduceIte, paritySign_sq]
    push_cast; ring

/-- For every odd wire count `2m + 1` and arbitrary `t1, t2 : ℤ`, `dimerizedOddWireZeroMode`
lies strictly in `ker(wireMass)`. -/
theorem dimerizedOddWireZeroMode_in_kernel (t1 t2 : ℤ) (m y : ℕ) (hy : y < 2 * m + 1) :
    ∑ z ∈ Finset.range (2 * m + 1),
      wireMassEntry (2 * m + 1) t1 t2 y z * dimerizedOddWireZeroMode t1 t2 m z = 0 := by
  rw [wireMass_row_eval (2 * m + 1) t1 t2 _ y hy]
  by_cases hy_even : y % 2 = 0
  · have h1 : (y + 1) % 2 ≠ 0 := by omega
    by_cases hy0 : 0 < y
    · have h2 : (y - 1) % 2 ≠ 0 := by omega
      simp [dimerizedOddWireZeroMode, h1, h2]
    · simp [dimerizedOddWireZeroMode, h1, hy0]
  · have hy_pos : 0 < y := by omega
    have hyu : y + 1 < 2 * m + 1 := by omega
    have he1 : (y + 1) % 2 = 0 := by omega
    have he2 : (y - 1) % 2 = 0 := by omega
    have hk : (y + 1) / 2 = (y - 1) / 2 + 1 := by omega
    have hm : m - (y - 1) / 2 = (m - ((y - 1) / 2 + 1)) + 1 := by omega
    simp only [hyu, hy_pos, hy_even, he2, ↓reduceIte, dimerizedOddWireZeroMode, he1, hk, hm, pow_succ]
    ring

theorem oddWireLeftZeroMode_in_kernel (m y : ℕ) (hy : y < 2 * m + 1) :
    ∑ z ∈ Finset.range (2 * m + 1),
      wireMassEntry (2 * m + 1) 1 1 y z * oddWireLeftZeroMode z = 0 := by
  have hpow : ∀ k : ℕ, (-1 : ℤ) ^ k = paritySign k := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, ih, paritySign_succ]; ring
  have heq : ∀ z ∈ Finset.range (2 * m + 1),
      oddWireLeftZeroMode z = dimerizedOddWireZeroMode 1 1 m z := by
    intro z _
    unfold oddWireLeftZeroMode dimerizedOddWireZeroMode
    split_ifs <;> simp [hpow]
  rw [Finset.sum_congr rfl (fun z hz => by rw [heq z hz])]
  exact dimerizedOddWireZeroMode_in_kernel 1 1 m y hy

theorem dimerizedOddWireZeroMode_nonzero (t1 t2 : ℤ) (m : ℕ) (ht : t1 ≠ 0 ∨ t2 ≠ 0) :
    ∃ z, z < 2 * m + 1 ∧ dimerizedOddWireZeroMode t1 t2 m z ≠ 0 := by
  rcases ht with h1 | h2
  · refine ⟨2 * m, by omega, ?_⟩
    simp [dimerizedOddWireZeroMode, pow_ne_zero m (neg_ne_zero.mpr h1)]
  · refine ⟨0, by omega, ?_⟩
    simp [dimerizedOddWireZeroMode, pow_ne_zero m h2]

/-! ### 3. Even-Wire `M^T M` Block Structure, Topological/Trivial Limits & Kernel Triviality -/

/-- Exact singular-value-squared matrix `(M^T M)_{y,z}` for ALL even wire counts `N_y = 2m` (`m ≥ 1`). -/
theorem wireMassSq_even (t1 t2 : ℤ) (m y z : ℕ) (hm : 1 ≤ m) (hy : y < 2 * m) (hz : z < 2 * m) :
    ∑ k ∈ Finset.range (2 * m),
      wireMassEntry (2 * m) t1 t2 k y * wireMassEntry (2 * m) t1 t2 k z =
      wireMassSqEntry (2 * m) t1 t2 y z := by
  have hsym : ∀ k ∈ Finset.range (2 * m),
      wireMassEntry (2 * m) t1 t2 k y * wireMassEntry (2 * m) t1 t2 k z =
        wireMassEntry (2 * m) t1 t2 y k * wireMassEntry (2 * m) t1 t2 k z := fun k _ => by
    rw [wireMassEntry_symm]
  rw [Finset.sum_congr rfl hsym, wireMass_row_eval (2 * m) t1 t2 (fun k => wireMassEntry (2 * m) t1 t2 k z) y hy]
  unfold wireMassEntry wireMassSqEntry
  by_cases hyz : y = z
  · subst hyz
    by_cases hy0 : y = 0
    · subst hy0; simp [show 1 < 2 * m by omega]
    · by_cases hyn : y + 1 = 2 * m
      · have he : (y - 1) % 2 = 0 := by omega
        simp [hy, hy0, hyn, show 0 < y by omega, show y - 1 < 2 * m by omega,
          show (y - 1) + 1 = y by omega, he]
      · have hyu : y + 1 < 2 * m := by omega
        have hyp : 0 < y := by omega
        simp only [hy, hy0, hyn, hyu, hyp, or_self, and_self, ↓reduceIte,
          show y - 1 < 2 * m by omega, show (y - 1) + 1 = y by omega,
          show ¬ ((y + 1) + 1 = y) by omega]
        by_cases hye : y % 2 = 0
        · have hy1 : (y - 1) % 2 ≠ 0 := by omega
          simp [hye, hy1]
        · have hy1 : (y - 1) % 2 = 0 := by omega
          simp [hye, hy1]; ring
  · by_cases h1 : y + 2 = z
    · subst h1
      have hyu : y + 1 < 2 * m := by omega
      simp only [hy, hz, hyu, show y ≠ y + 2 by omega, true_or, and_self, ↓reduceIte,
        show (y + 1) + 1 = y + 2 by omega]
      split_ifs <;> first | omega | ring
    · by_cases h2 : z + 2 = y
      · subst h2
        have hyp : 0 < z + 2 := by omega
        simp only [hy, hz, hyp, show z + 2 ≠ z by omega, or_true, and_self, ↓reduceIte,
          show z + 2 - 1 < 2 * m by omega, show z + 1 = z + 2 - 1 by omega,
          show ¬ ((z + 2 - 1) + 1 = z) by omega]
        split_ifs <;> first | omega | ring
      · simp only [hy, hz, hyz, h1, h2, or_self, and_self, ↓reduceIte]
        split_ifs <;> omega

theorem wireMassSq_even_topo (t2 : ℤ) (m y z : ℕ) (hm : 1 ≤ m) (hy : y < 2 * m) (hz : z < 2 * m) :
    ∑ k ∈ Finset.range (2 * m),
      wireMassEntry (2 * m) 0 t2 k y * wireMassEntry (2 * m) 0 t2 k z =
      if y = z then (if y = 0 ∨ y + 1 = 2 * m then 0 else t2 * t2) else 0 := by
  rw [wireMassSq_even 0 t2 m y z hm hy hz]
  simp [wireMassSqEntry, hy, hz]

theorem wireMass_topo_dimer_action (t2 : ℤ) (m j z : ℕ) (hj : j + 1 < m) (hz : z < 2 * m) :
    wireMassEntry (2 * m) 0 t2 (2 * j + 1) z = (if z = 2 * j + 2 then t2 else 0) ∧
    wireMassEntry (2 * m) 0 t2 (2 * j + 2) z = (if z = 2 * j + 1 then t2 else 0) := by
  constructor <;> (unfold wireMassEntry; split_ifs <;> omega)

theorem wireMassSq_even_trivial (t1 : ℤ) (m y z : ℕ) (hm : 1 ≤ m) (hy : y < 2 * m) (hz : z < 2 * m) :
    ∑ k ∈ Finset.range (2 * m),
      wireMassEntry (2 * m) t1 0 k y * wireMassEntry (2 * m) t1 0 k z =
      if y = z then t1 * t1 else 0 := by
  rw [wireMassSq_even t1 0 m y z hm hy hz]
  simp only [wireMassSqEntry, hy, hz, and_self, ↓reduceIte]
  split_ifs <;> simp

theorem evenWireTopoLeftEdge_in_kernel (t2 : ℤ) (m y : ℕ) (hy : y < 2 * m) :
    ∑ z ∈ Finset.range (2 * m), wireMassEntry (2 * m) 0 t2 y z * evenWireTopoLeftEdge z = 0 := by
  rw [wireMass_row_eval (2 * m) 0 t2 _ y hy]
  unfold evenWireTopoLeftEdge
  by_cases hy1 : y = 1
  · subst hy1; simp
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, mul_zero]
    split_ifs <;> omega

theorem evenWireTopoRightEdge_in_kernel (t2 : ℤ) (m y : ℕ) (hy : y < 2 * m) :
    ∑ z ∈ Finset.range (2 * m),
      wireMassEntry (2 * m) 0 t2 y z * evenWireTopoRightEdge (2 * m) z = 0 := by
  rw [wireMass_row_eval (2 * m) 0 t2 _ y hy]
  unfold evenWireTopoRightEdge; split_ifs <;> omega

theorem evenWireTopoEdge_chiralities (m : ℕ) (hm : 1 ≤ m) :
    paritySign 0 = 1 ∧ paritySign (2 * m - 1) = -1 := by
  refine ⟨rfl, ?_⟩
  unfold paritySign; split_ifs <;> omega

/-- Exact topological-phase kernel characterization on `N_y = 2m`:
when `t1 = 0, t2 ≠ 0`, `v ∈ ker(M)` iff all interior wires `0 < y < 2m - 1` vanish. -/
theorem wireMass_topo_kernel_iff (t2 : ℤ) (ht2 : t2 ≠ 0) (m : ℕ) (_hm : 1 ≤ m) (v : ℕ → ℤ) :
    (∀ y, y < 2 * m → ∑ z ∈ Finset.range (2 * m), wireMassEntry (2 * m) 0 t2 y z * v z = 0) ↔
      (∀ y, 0 < y → y + 1 < 2 * m → v y = 0) := by
  have row_eq : ∀ y, 0 < y → y + 1 < 2 * m →
      ∑ z ∈ Finset.range (2 * m), wireMassEntry (2 * m) 0 t2 y z * v z =
        if y % 2 = 1 then t2 * v (y + 1) else t2 * v (y - 1) := by
    intro y hy0 hy1
    rw [wireMass_row_eval (2 * m) 0 t2 v y (by omega)]
    split_ifs <;> omega
  constructor
  · intro hker y hy0 hy1
    by_cases hy_odd : y % 2 = 1
    · have hnext := hker (y + 1) (by omega)
      rw [row_eq (y + 1) (by omega) (by omega)] at hnext
      have hne : (y + 1) % 2 ≠ 1 := by omega
      simp only [hne, ↓reduceIte, Nat.add_sub_cancel] at hnext
      exact (mul_eq_zero.mp hnext).resolve_left ht2
    · have hprev := hker (y - 1) (by omega)
      rw [row_eq (y - 1) (by omega) (by omega)] at hprev
      have ho : (y - 1) % 2 = 1 := by omega
      have hadd : y - 1 + 1 = y := by omega
      simp only [ho, ↓reduceIte, hadd] at hprev
      exact (mul_eq_zero.mp hprev).resolve_left ht2
  · intro hinter y hy
    by_cases hy0 : y = 0
    · subst hy0; rw [wireMass_row_eval (2 * m) 0 t2 v 0 hy]; simp
    · by_cases hyn : y + 1 = 2 * m
      · rw [wireMass_row_eval (2 * m) 0 t2 v y hy]
        have he : (y - 1) % 2 = 0 := by omega
        simp [hyn, he]
      · rw [row_eq y (by omega) (by omega)]
        split_ifs
        · rw [hinter (y + 1) (by omega) (by omega), mul_zero]
        · rw [hinter (y - 1) (by omega) (by omega), mul_zero]

/-- Exact finite-size kernel triviality on `N_y = 2m` for ANY `t1 ≠ 0` and ANY `t2 : ℤ`. -/
theorem wireMass_even_kernel_eq_zero (t1 t2 : ℤ) (ht1 : t1 ≠ 0) (m : ℕ) (v : ℕ → ℤ)
    (hker : ∀ y, y < 2 * m →
      ∑ z ∈ Finset.range (2 * m), wireMassEntry (2 * m) t1 t2 y z * v z = 0) :
    ∀ z, z < 2 * m → v z = 0 := by
  have hodd_zero : ∀ j, 2 * j + 1 < 2 * m → v (2 * j + 1) = 0 := by
    intro j
    induction j with
    | zero =>
      intro hj
      have h0 := hker 0 (by omega)
      rw [wireMass_row_eval (2 * m) t1 t2 v 0 (by omega)] at h0
      simp [hj] at h0
      exact h0.resolve_left ht1
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hev := hker (2 * j + 2) (by omega)
      rw [wireMass_row_eval (2 * m) t1 t2 v (2 * j + 2) (by omega)] at hev
      have hadd : 2 * j + 2 + 1 = 2 * (j + 1) + 1 := by omega
      have hsub : 2 * j + 2 - 1 = 2 * j + 1 := by omega
      simp [hj, hadd, hsub, hprev, show (2 * j + 2) % 2 = 0 by omega,
        show 0 < 2 * j + 2 by omega] at hev
      exact hev.resolve_left ht1
  have heven_rev : ∀ k, k < m → v (2 * (m - 1 - k)) = 0 := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hlast := hker (2 * m - 1) (by omega)
      rw [wireMass_row_eval (2 * m) t1 t2 v (2 * m - 1) (by omega)] at hlast
      have hsub : 2 * m - 1 - 1 = 2 * (m - 1 - 0) := by omega
      simp [show ¬ ((2 * m - 1) + 1 < 2 * m) by omega, show 0 < 2 * m - 1 by omega,
        hsub] at hlast
      exact hlast.resolve_left ht1
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hrow := hker (2 * (m - 1 - k) - 1) (by omega)
      rw [wireMass_row_eval (2 * m) t1 t2 v (2 * (m - 1 - k) - 1) (by omega)] at hrow
      have hadd : 2 * (m - 1 - k) - 1 + 1 = 2 * (m - 1 - k) := by omega
      have hsub : 2 * (m - 1 - k) - 1 - 1 = 2 * (m - 1 - (k + 1)) := by omega
      simp [show 2 * (m - 1 - k) < 2 * m by omega, show 0 < 2 * (m - 1 - k) - 1 by omega,
        hadd, hsub, hprev, show (2 * (m - 1 - (k + 1))) % 2 = 0 by omega] at hrow
      exact hrow.resolve_left ht1
  intro z hz
  by_cases hz_even : z % 2 = 0
  · have hidx : 2 * (m - 1 - (m - 1 - z / 2)) = z := by omega
    simpa [hidx] using heven_rev (m - 1 - z / 2) (by omega)
  · have hidx : 2 * (z / 2) + 1 = z := by omega
    simpa [hidx] using hodd_zero (z / 2) (by omega)

theorem wireMass_trivial_kernel_eq_zero (t1 : ℤ) (ht1 : t1 ≠ 0) (m : ℕ) (v : ℕ → ℤ)
    (hker : ∀ y, y < 2 * m →
      ∑ z ∈ Finset.range (2 * m), wireMassEntry (2 * m) t1 0 y z * v z = 0) :
    ∀ z, z < 2 * m → v z = 0 :=
  wireMass_even_kernel_eq_zero t1 0 ht1 m v hker

/-- Exact finite-size boundary residual of `evenWireEdgeAnsatz` on `N_y = 2m` (`m ≥ 1`):
`M v` vanishes on every row `y < 2m - 1` and equals `-((-t1)^m)` solely on row `y = 2m - 1`. -/
theorem evenWireEdgeAnsatz_residual (t1 t2 : ℤ) (m y : ℕ) (hm : 1 ≤ m) (hy : y < 2 * m) :
    ∑ z ∈ Finset.range (2 * m),
      wireMassEntry (2 * m) t1 t2 y z * evenWireEdgeAnsatz t1 t2 m z =
      if y + 1 = 2 * m then -((-t1) ^ m) else 0 := by
  rw [wireMass_row_eval (2 * m) t1 t2 _ y hy]
  by_cases hy_even : y % 2 = 0
  · have hne : y + 1 ≠ 2 * m := by omega
    have h1 : (y + 1) % 2 ≠ 0 := by omega
    by_cases hy0 : 0 < y
    · have h2 : (y - 1) % 2 ≠ 0 := by omega
      simp [hne, evenWireEdgeAnsatz, h1, h2]
    · simp [hne, evenWireEdgeAnsatz, h1, hy0]
  · have hy_pos : 0 < y := by omega
    by_cases hlast : y + 1 = 2 * m
    · have he0 : (y - 1) % 2 = 0 := by omega
      have hd : (y - 1) / 2 = m - 1 := by omega
      have hpow : (-t1) ^ m = (-t1) ^ (m - 1) * (-t1) := by
        rw [← pow_succ, show m - 1 + 1 = m by omega]
      simp only [hlast, lt_self_iff_false, hy_pos, he0, ↓reduceIte, zero_add,
        evenWireEdgeAnsatz, hd, Nat.sub_self, pow_zero, mul_one, hpow]
      ring
    · have hyu : y + 1 < 2 * m := by omega
      have he1 : (y + 1) % 2 = 0 := by omega
      have he2 : (y - 1) % 2 = 0 := by omega
      have hk : (y + 1) / 2 = (y - 1) / 2 + 1 := by omega
      have hm1 : m - 1 - (y - 1) / 2 = (m - 1 - ((y - 1) / 2 + 1)) + 1 := by omega
      simp only [hlast, hyu, hy_pos, hy_even, he2, ↓reduceIte, evenWireEdgeAnsatz, he1, hk, hm1,
        pow_succ]
      ring

end Bosonize.CoupledWire
