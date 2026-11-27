module

public import Bosonize.Core.CoupledWire.BlochDiracAndGauge
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Staggered CS Anomaly Cancellation, `(2+1)D` Mutual-CS Gauge Invariance, `π`-Mode Schur Renormalization & Dirac-CFL Conductivity

Formalizes Mross–Alicea–Motrunich (`arXiv:1510.08455`, Secs. IV–VI & Apps. B, C, E, G) on pinned Mathlib4:
- staggered Chern–Simons level `2 ν(y) = twoNu0 + (-1)^y`, uniqueness, TI surface vs. half-filled
  2DEG strips, and interior/OBC/PBC anomaly cancellation;
- discrete `(2+1)D` curls, field strengths `(f01, f02, f12)`, Bianchi identity, periodic
  central-difference skew-adjointness, and exact `(T, X, N)` mutual-CS lattice gauge invariance;
- cleared-denominator MAM App. E `π`-mode `2×2` Schur complement (`Matrix.det`), Gaussian square
  completion, velocity bounds `v ≤ v_tilde < 2v`, and Luttinger `K ↔ 1/K` duality;
- universal `[CommRing R]` isotropic Hall matrix `hallMat`, Ioffe–Larkin `ρ_total = ρ_f + ρ_CS`
  and Son/MAM Dirac-CFL mutual-CS conductivity inversion, PH-symmetric `σ_xy = 1/2`, and PH sum rule.
-/

@[expose] public section

namespace Bosonize.CoupledWire

open scoped BigOperators
open Matrix

/-! ### 1. Staggered Chern–Simons Level Recurrence & Anomaly Cancellation -/

/-- Integer-scaled staggered Chern–Simons level `2 ν(y) = twoNu0 + (-1)^y`. -/
def twoNu (twoNu0 : ℤ) (y : ℕ) : ℤ :=
  twoNu0 + paritySign y

/-- Doubled OBC staggered Chern–Simons anomaly coefficient on wire `y < n` (`n ≥ 2`). -/
def staggeredCSVarOBC (n : ℕ) (twoNu0 : ℤ) (y : ℕ) : ℤ :=
  if y = 0 then twoNu twoNu0 0
  else if y + 1 = n then -twoNu twoNu0 (n - 2)
  else twoNu twoNu0 y - twoNu twoNu0 (y - 1)

theorem twoNu_recurrence (twoNu0 : ℤ) (y : ℕ) :
    twoNu twoNu0 (y + 1) - twoNu twoNu0 y = 2 * paritySign (y + 1) := by
  simp only [twoNu, paritySign_succ]; omega

theorem twoNu_recurrence_pred (twoNu0 : ℤ) (y : ℕ) (hy : 1 ≤ y) :
    twoNu twoNu0 y - twoNu twoNu0 (y - 1) = 2 * paritySign y := by
  have h := twoNu_recurrence twoNu0 (y - 1)
  rwa [show y - 1 + 1 = y by omega] at h

theorem twoNu_unique (f : ℕ → ℤ)
    (hrec : ∀ y : ℕ, f (y + 1) - f y = 2 * paritySign (y + 1)) (y : ℕ) :
    f y = twoNu (f 0 - 1) y := by
  induction y with
  | zero => simp [twoNu, paritySign]
  | succ k ih =>
    have hstep := hrec k
    have hnu := twoNu_recurrence (f 0 - 1) k
    omega

theorem twoNu_ti_surface_sq (y : ℕ) : twoNu 0 y * twoNu 0 y = 1 := by
  simp [twoNu, paritySign_sq]

theorem twoNu_2deg_half_filling (k : ℕ) :
    twoNu 1 (2 * k) = 2 ∧ twoNu 1 (2 * k + 1) = 0 := by
  simp [twoNu, paritySign]

theorem staggeredCS_interior_anomaly_cancel (twoNu0 : ℤ) (y : ℕ) (hy : 1 ≤ y) :
    (twoNu twoNu0 y - twoNu twoNu0 (y - 1)) + (-2 * paritySign y) = 0 := by
  rw [twoNu_recurrence_pred twoNu0 y hy]; omega

theorem staggeredCS_obc_interior_zero (n : ℕ) (twoNu0 : ℤ) (y : ℕ)
    (hy0 : 0 < y) (hyn : y + 1 < n) :
    staggeredCSVarOBC n twoNu0 y + (-2 * paritySign y) = 0 := by
  simp only [staggeredCSVarOBC, show y ≠ 0 by omega, show y + 1 ≠ n by omega, ↓reduceIte]
  exact staggeredCS_interior_anomaly_cancel twoNu0 y hy0

theorem staggeredCS_obc_boundary_values (n : ℕ) (hn : 2 ≤ n) (twoNu0 : ℤ) :
    (staggeredCSVarOBC n twoNu0 0 + (-2 * paritySign 0) = twoNu0 - 1) ∧
    (staggeredCSVarOBC n twoNu0 (n - 1) + (-2 * paritySign (n - 1)) =
      -twoNu0 - paritySign (n - 1)) := by
  have hpred : paritySign (n - 2) = -paritySign (n - 1) := by
    have h := paritySign_succ (n - 2)
    rw [show n - 2 + 1 = n - 1 by omega] at h; omega
  constructor
  · simp [staggeredCSVarOBC, twoNu, paritySign]; omega
  · simp only [staggeredCSVarOBC, show n - 1 ≠ 0 by omega, show n - 1 + 1 = n by omega,
      ↓reduceIte, twoNu, hpred]; omega

theorem staggeredCS_pbc_anomaly_cancel (m : ℕ) (hm : 1 ≤ m) (twoNu0 : ℤ) (y : ℕ) (hy : y < 2 * m) :
    (twoNu twoNu0 y - twoNu twoNu0 ((y + 2 * m - 1) % (2 * m))) + (-2 * paritySign y) = 0 := by
  by_cases hy0 : y = 0
  · subst hy0
    have hmod : (0 + 2 * m - 1) % (2 * m) = 2 * m - 1 := by
      rw [zero_add]; exact Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    simp [twoNu, paritySign, show (2 * m - 1) % 2 ≠ 0 by omega]
  · have hmod : (y + 2 * m - 1) % (2 * m) = y - 1 := by
      rw [show y + 2 * m - 1 = (y - 1) + 2 * m by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    exact staggeredCS_interior_anomaly_cancel twoNu0 y (by omega)

/-! ### 2. Discrete `(2+1)D` Curl, Bianchi Identity & Periodic Mutual-CS Gauge Invariance -/

def dt (f : ℕ → ℕ → ℕ → ℤ) (t x y : ℕ) : ℤ := f (t + 1) x y - f t x y
def dx (f : ℕ → ℕ → ℕ → ℤ) (t x y : ℕ) : ℤ := f t (x + 1) y - f t x y
def dy (f : ℕ → ℕ → ℕ → ℤ) (t x y : ℕ) : ℤ := f t x (y + 1) - f t x y
def dtWire (f : ℕ → ℕ → ℤ) (t y : ℕ) : ℤ := f (t + 1) y - f t y
def deltaLinkOp (n : ℕ) (f : ℕ → ℤ) (y : ℕ) : ℤ := ∑ z ∈ Finset.range n, diffLinkEntry y z * f z
def shiftLinkOp (n : ℕ) (f : ℕ → ℤ) (y : ℕ) : ℤ := ∑ z ∈ Finset.range n, shiftLinkEntry y z * f z
def wireLinkCurl (n : ℕ) (a0 a1 : ℕ → ℕ → ℤ) (t y : ℕ) : ℤ := dtWire a1 t y - deltaLinkOp n (a0 t) y
def f01 (a0 a1 : ℕ → ℕ → ℕ → ℤ) (t x y : ℕ) : ℤ := dt a1 t x y - dx a0 t x y
def f02 (a0 a2 : ℕ → ℕ → ℕ → ℤ) (t x y : ℕ) : ℤ := dt a2 t x y - dy a0 t x y
def f12 (a1 a2 : ℕ → ℕ → ℕ → ℤ) (t x y : ℕ) : ℤ := dx a2 t x y - dy a1 t x y

theorem dt_dx_comm (f : ℕ → ℕ → ℕ → ℤ) (t x y : ℕ) : dt (dx f) t x y = dx (dt f) t x y := by
  simp only [dt, dx]; omega

theorem dt_dy_comm (f : ℕ → ℕ → ℕ → ℤ) (t x y : ℕ) : dt (dy f) t x y = dy (dt f) t x y := by
  simp only [dt, dy]; omega

theorem dx_dy_comm (f : ℕ → ℕ → ℕ → ℤ) (t x y : ℕ) : dx (dy f) t x y = dy (dx f) t x y := by
  simp only [dx, dy]; omega

theorem deltaLinkOp_dt_commute (n : ℕ) (chi : ℕ → ℕ → ℤ) (t y : ℕ) :
    deltaLinkOp n (dtWire chi t) y - dtWire (fun t' y' => deltaLinkOp n (chi t') y') t y = 0 := by
  simp only [deltaLinkOp, dtWire, mul_sub, Finset.sum_sub_distrib]; omega

theorem shiftLinkOp_dt_commute (n : ℕ) (chi : ℕ → ℕ → ℤ) (t y : ℕ) :
    shiftLinkOp n (dtWire chi t) y - dtWire (fun t' y' => shiftLinkOp n (chi t') y') t y = 0 := by
  simp only [shiftLinkOp, dtWire, mul_sub, Finset.sum_sub_distrib]; omega

theorem wireLinkCurl_gauge_inv (n : ℕ) (a0 a1 chi : ℕ → ℕ → ℤ) (t y : ℕ) :
    wireLinkCurl n
        (fun t' y' => a0 t' y' + dtWire chi t' y')
        (fun t' y' => a1 t' y' + deltaLinkOp n (chi t') y') t y =
      wireLinkCurl n a0 a1 t y := by
  simp only [wireLinkCurl, dtWire, deltaLinkOp, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  omega

theorem f01_gauge_inv (a0 a1 chi : ℕ → ℕ → ℕ → ℤ) (t x y : ℕ) :
    f01 (fun t' x' y' => a0 t' x' y' + dt chi t' x' y')
        (fun t' x' y' => a1 t' x' y' + dx chi t' x' y') t x y = f01 a0 a1 t x y := by
  simp only [f01, dt, dx]; omega

theorem f02_gauge_inv (a0 a2 chi : ℕ → ℕ → ℕ → ℤ) (t x y : ℕ) :
    f02 (fun t' x' y' => a0 t' x' y' + dt chi t' x' y')
        (fun t' x' y' => a2 t' x' y' + dy chi t' x' y') t x y = f02 a0 a2 t x y := by
  simp only [f02, dt, dy]; omega

theorem f12_gauge_inv (a1 a2 chi : ℕ → ℕ → ℕ → ℤ) (t x y : ℕ) :
    f12 (fun t' x' y' => a1 t' x' y' + dx chi t' x' y')
        (fun t' x' y' => a2 t' x' y' + dy chi t' x' y') t x y = f12 a1 a2 t x y := by
  simp only [f12, dx, dy]; omega

theorem discrete_bianchi_identity (a0 a1 a2 : ℕ → ℕ → ℕ → ℤ) (t x y : ℕ) :
    dt (f12 a1 a2) t x y - dx (f02 a0 a2) t x y + dy (f01 a0 a1) t x y = 0 := by
  simp only [dt, dx, dy, f01, f02, f12]; omega

theorem wire_delta_shift_telescope (n : ℕ) (A0 g : ℕ → ℤ) :
    ∑ y ∈ Finset.range n,
      ((A0 (y + 1) - A0 y) * (g (y + 1) + g y) + (g (y + 1) - g y) * (A0 (y + 1) + A0 y)) =
      2 * (A0 n * g n - A0 0 * g 0) := by
  have hrew : ∀ y ∈ Finset.range n,
      (A0 (y + 1) - A0 y) * (g (y + 1) + g y) + (g (y + 1) - g y) * (A0 (y + 1) + A0 y) =
        2 * (A0 (y + 1) * g (y + 1) - A0 y * g y) := fun y _ => by ring
  rw [Finset.sum_congr rfl hrew, ← Finset.mul_sum, Finset.sum_range_sub (fun y => A0 y * g y) n]

theorem sum_range_shift_mod (n : ℕ) (hn : 1 ≤ n) (f : ℕ → ℤ) :
    ∑ k ∈ Finset.range n, f ((k + 1) % n) = ∑ k ∈ Finset.range n, f k := by
  cases n with
  | zero => omega
  | succ m =>
    rw [Finset.sum_range_succ, Nat.mod_self]
    have hcongr : ∑ k ∈ Finset.range m, f ((k + 1) % (m + 1)) = ∑ k ∈ Finset.range m, f (k + 1) :=
      Finset.sum_congr rfl (fun k hk => by rw [Nat.mod_eq_of_lt (by have := Finset.mem_range.mp hk; omega)])
    rw [hcongr, ← Finset.sum_range_succ']

theorem sum_range_shift_pred_mod (n : ℕ) (hn : 1 ≤ n) (f : ℕ → ℤ) :
    ∑ k ∈ Finset.range n, f ((k + n - 1) % n) = ∑ k ∈ Finset.range n, f k := by
  rw [← sum_range_shift_mod n hn (fun k => f ((k + n - 1) % n))]
  apply Finset.sum_congr rfl; intro k hk
  have hk' : k < n := Finset.mem_range.mp hk
  have heq : (((k + 1) % n) + n - 1) % n = k := by
    by_cases hlast : k + 1 = n
    · rw [hlast, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega : n - 1 < n)]; omega
    · rw [Nat.mod_eq_of_lt (by omega : k + 1 < n), show k + 1 + n - 1 = k + n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hk']
  rw [heq]

/-- Periodic central difference along an axis of period `N ≥ 1`. -/
def centralDiff1D (N : ℕ) (f : ℕ → ℤ) (k : ℕ) : ℤ :=
  f ((k + 1) % N) - f ((k + N - 1) % N)

theorem centralDiff1D_skew (N : ℕ) (hn : 1 ≤ N) (u v : ℕ → ℤ) :
    ∑ k ∈ Finset.range N, (centralDiff1D N u k * v k + u k * centralDiff1D N v k) = 0 := by
  have hcyc : ∀ k < N, (((k + N - 1) % N) + 1) % N = k := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      rw [zero_add, Nat.mod_eq_of_lt (by omega : N - 1 < N), show N - 1 + 1 = N by omega, Nat.mod_self]
    · rw [show k + N - 1 = (k - 1) + N by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega : k - 1 < N), show k - 1 + 1 = k by omega, Nat.mod_eq_of_lt hk]
  have h1 : ∑ k ∈ Finset.range N, u ((k + 1) % N) * v k =
      ∑ k ∈ Finset.range N, u k * v ((k + N - 1) % N) := by
    rw [← sum_range_shift_pred_mod N hn (fun k => u ((k + 1) % N) * v k)]
    exact Finset.sum_congr rfl (fun k hk => by rw [hcyc k (Finset.mem_range.mp hk)])
  have h2 : ∑ k ∈ Finset.range N, u k * v ((k + 1) % N) =
      ∑ k ∈ Finset.range N, u ((k + N - 1) % N) * v k := by
    rw [← sum_range_shift_pred_mod N hn (fun k => u k * v ((k + 1) % N))]
    exact Finset.sum_congr rfl (fun k hk => by rw [hcyc k (Finset.mem_range.mp hk)])
  simp only [centralDiff1D, sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2]
  omega

def dtC (T : ℕ) (f : ℕ → ℕ → ℕ → ℤ) (t x y : ℕ) : ℤ :=
  f ((t + 1) % T) x y - f ((t + T - 1) % T) x y
def dxC (X : ℕ) (f : ℕ → ℕ → ℕ → ℤ) (t x y : ℕ) : ℤ :=
  f t ((x + 1) % X) y - f t ((x + X - 1) % X) y
def dyP (N : ℕ) (f : ℕ → ℕ → ℕ → ℤ) (t x y : ℕ) : ℤ :=
  f t x ((y + 1) % N) - f t x y
def syP (N : ℕ) (f : ℕ → ℕ → ℕ → ℤ) (t x y : ℕ) : ℤ :=
  f t x ((y + 1) % N) + f t x y

/-- MAM App. B/C polarized mutual Chern–Simons lattice integrand on periodic `(T, X, N)`. -/
def mutualCSIntegrand (T X N : ℕ)
    (a0 a1 a2 A0 A1 A2 : ℕ → ℕ → ℕ → ℤ) (t x y : ℕ) : ℤ :=
  (dyP N a0 t x y - dtC T a2 t x y) * syP N A1 t x y +
  (dyP N A0 t x y - dtC T A2 t x y) * syP N a1 t x y +
  dxC X a2 t x y * syP N A0 t x y +
  dxC X A2 t x y * syP N a0 t x y

/-- Total discrete `(T, X, N)` periodic mutual Chern–Simons functional. -/
def mutualCSAction (T X N : ℕ) (a0 a1 a2 A0 A1 A2 : ℕ → ℕ → ℕ → ℤ) : ℤ :=
  ∑ t ∈ Finset.range T, ∑ x ∈ Finset.range X, ∑ y ∈ Finset.range N,
    mutualCSIntegrand T X N a0 a1 a2 A0 A1 A2 t x y

private theorem sum_centralDiff_tx_ibp (T X : ℕ) (hT : 1 ≤ T) (hX : 1 ≤ X) (A f : ℕ → ℕ → ℤ) :
    ∑ t ∈ Finset.range T, ∑ x ∈ Finset.range X,
      (centralDiff1D X (fun x' => A t x') x * centralDiff1D T (fun t' => f t' x) t -
       centralDiff1D T (fun t' => A t' x) t * centralDiff1D X (fun x' => f t x') x) = 0 := by
  simp_rw [Finset.sum_sub_distrib]
  have h1 : ∑ t ∈ Finset.range T, ∑ x ∈ Finset.range X,
      centralDiff1D X (fun x' => A t x') x * centralDiff1D T (fun t' => f t' x) t =
      -∑ t ∈ Finset.range T, ∑ x ∈ Finset.range X,
        A t x * centralDiff1D X (fun x' => centralDiff1D T (fun t' => f t' x') t) x := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro t _
    have hs := centralDiff1D_skew X hX (fun x' => A t x') (fun x' => centralDiff1D T (fun t' => f t' x') t)
    rw [Finset.sum_add_distrib] at hs; omega
  have h2 : ∑ t ∈ Finset.range T, ∑ x ∈ Finset.range X,
      centralDiff1D T (fun t' => A t' x) t * centralDiff1D X (fun x' => f t x') x =
      -∑ t ∈ Finset.range T, ∑ x ∈ Finset.range X,
        A t x * centralDiff1D T (fun t' => centralDiff1D X (fun x' => f t' x') x) t := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    have hcol : ∀ x ∈ Finset.range X,
        ∑ t ∈ Finset.range T, centralDiff1D T (fun t' => A t' x) t * centralDiff1D X (fun x' => f t x') x =
        -∑ t ∈ Finset.range T, A t x * centralDiff1D T (fun t' => centralDiff1D X (fun x' => f t' x') x) t := by
      intro x _
      have hs := centralDiff1D_skew T hT (fun t' => A t' x) (fun t' => centralDiff1D X (fun x' => f t' x') x)
      rw [Finset.sum_add_distrib] at hs; omega
    rw [Finset.sum_congr rfl hcol, Finset.sum_neg_distrib, Finset.sum_comm, ← Finset.sum_neg_distrib]
  have hcomm : ∀ t x,
      centralDiff1D X (fun x' => centralDiff1D T (fun t' => f t' x') t) x =
      centralDiff1D T (fun t' => centralDiff1D X (fun x' => f t' x') x) t := by
    intro t x; simp only [centralDiff1D]; omega
  rw [h1, h2]; simp_rw [hcomm]; omega

/-- Exact periodic `(T, X, N)` lattice gauge invariance of the MAM mutual Chern–Simons action. -/
theorem mutualCSAction_gauge_inv (T X N : ℕ) (hT : 1 ≤ T) (hX : 1 ≤ X) (hN : 1 ≤ N)
    (a0 a1 a2 A0 A1 A2 chi : ℕ → ℕ → ℕ → ℤ) :
    mutualCSAction T X N
      (fun t x y => a0 t x y + dtC T chi t x y)
      (fun t x y => a1 t x y + dxC X chi t x y)
      (fun t x y => a2 t x y + dyP N chi t x y) A0 A1 A2 =
    mutualCSAction T X N a0 a1 a2 A0 A1 A2 := by
  suffices hdiff :
      mutualCSAction T X N
        (fun t x y => a0 t x y + dtC T chi t x y)
        (fun t x y => a1 t x y + dxC X chi t x y)
        (fun t x y => a2 t x y + dyP N chi t x y) A0 A1 A2 -
      mutualCSAction T X N a0 a1 a2 A0 A1 A2 = 0 by omega
  simp only [mutualCSAction, ← Finset.sum_sub_distrib]
  have hpt : ∀ t x y,
      mutualCSIntegrand T X N
        (fun t' x' y' => a0 t' x' y' + dtC T chi t' x' y')
        (fun t' x' y' => a1 t' x' y' + dxC X chi t' x' y')
        (fun t' x' y' => a2 t' x' y' + dyP N chi t' x' y') A0 A1 A2 t x y -
      mutualCSIntegrand T X N a0 a1 a2 A0 A1 A2 t x y =
      2 * (A0 t x ((y + 1) % N) * dxC X chi t x ((y + 1) % N) - A0 t x y * dxC X chi t x y) +
      (centralDiff1D X (fun x' => A2 t x' y) x * centralDiff1D T (fun t' => syP N chi t' x y) t -
       centralDiff1D T (fun t' => A2 t' x y) t * centralDiff1D X (fun x' => syP N chi t x' y) x) := by
    intro t x y; simp only [mutualCSIntegrand, dyP, syP, dtC, dxC, centralDiff1D]; ring
  simp_rw [hpt, Finset.sum_add_distrib]
  have hy_zero : ∑ t ∈ Finset.range T, ∑ x ∈ Finset.range X, ∑ y ∈ Finset.range N,
      2 * (A0 t x ((y + 1) % N) * dxC X chi t x ((y + 1) % N) - A0 t x y * dxC X chi t x y) = 0 := by
    apply Finset.sum_eq_zero; intro t _; apply Finset.sum_eq_zero; intro x _
    rw [← Finset.mul_sum, Finset.sum_sub_distrib,
      sum_range_shift_mod N hN (fun y => A0 t x y * dxC X chi t x y), sub_self, mul_zero]
  have htx_zero : ∑ t ∈ Finset.range T, ∑ x ∈ Finset.range X, ∑ y ∈ Finset.range N,
      (centralDiff1D X (fun x' => A2 t x' y) x * centralDiff1D T (fun t' => syP N chi t' x y) t -
       centralDiff1D T (fun t' => A2 t' x y) t * centralDiff1D X (fun x' => syP N chi t x' y) x) = 0 := by
    simp_rw [Finset.sum_comm (s := Finset.range X) (t := Finset.range N)]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero; intro y _
    exact sum_centralDiff_tx_ibp T X hT hX (fun t x => A2 t x y) (fun t x => syP N chi t x y)
  rw [hy_zero, htx_zero, add_zero]

/-! ### 3. MAM App. E `π`-Mode Velocity Renormalization & `2×2` Schur Complement -/

/-- `2×2` Schur complement matrix `[[u + v, -u], [-u, u + v]]` over `[CommRing R]`. -/
def piModeSchurMat {R : Type*} [CommRing R] (u v : R) : Matrix (Fin 2) (Fin 2) R :=
  !![u + v, -u; -u, u + v]

theorem piModeSchurMat_det {R : Type*} [CommRing R] (u v : R) :
    (piModeSchurMat u v).det = v * (2 * u + v) := by
  rw [piModeSchurMat, Matrix.det_fin_two_of]; ring

theorem piMode_complete_square_exact {R : Type*} [CommRing R] (v u a0 a1 J : R) :
    (u + v) * (a0 * a0 + 2 * v * J * a0) +
      v * (u + v) * (-(u + v) * a1 * a1 + 2 * u * J * a1 - u * J * J) =
    (u + v) * (a0 + v * J) ^ 2 - v * ((u + v) * a1 - u * J) ^ 2 -
      v ^ 2 * (2 * u + v) * J ^ 2 := by
  ring

theorem piMode_velocity_renorm_diff {R : Type*} [CommRing R] (v u v_tilde : R)
    (hvt : (u + v) * v_tilde = v * (2 * u + v)) :
    (u + v) * (v_tilde - v) = u * v ∧ (u + v) * (2 * v - v_tilde) = v * v :=
  ⟨by linear_combination hvt, by linear_combination -hvt⟩

theorem piMode_velocity_bounds (v u v_tilde : ℤ) (hv : 0 < v) (hu : 0 ≤ u)
    (hvt : (u + v) * v_tilde = v * (2 * u + v)) :
    v ≤ v_tilde ∧ v_tilde < 2 * v ∧ (v_tilde = v ↔ u = 0) := by
  obtain ⟨hdiff, hupper⟩ := piMode_velocity_renorm_diff v u v_tilde hvt
  have huv : 0 < u + v := by omega
  have hle : v ≤ v_tilde := by nlinarith
  have hlt2 : v_tilde < 2 * v := by nlinarith
  refine ⟨hle, hlt2, ?_⟩
  constructor
  · intro heq; rw [heq, sub_self, mul_zero] at hdiff
    exact (mul_eq_zero.mp hdiff.symm).resolve_right (by omega)
  · rintro rfl; simp only [zero_mul] at hdiff
    have hsub := (mul_eq_zero.mp hdiff).resolve_left (by omega)
    omega

theorem luttinger_velocity_duality {R : Type*} [CommRing R] (p q v vLL : R)
    (hvll : (p ^ 2 + q ^ 2) * vLL = 2 * p * q * v) :
    (q ^ 2 + p ^ 2) * vLL = 2 * q * p * v ∧
    (p ^ 2 + q ^ 2) * (v - vLL) = (p - q) ^ 2 * v := by
  constructor
  · linear_combination hvll
  · linear_combination -hvll

/-! ### 4. Ioffe–Larkin & Son/MAM Dirac-CFL `ν = 1/2` Conductivity Matrix Algebra -/

/-- Isotropic 2D Hall conductivity/resistivity matrix `[[d, h], [-h, d]]` over `[CommRing R]`. -/
def hallMat {R : Type*} [CommRing R] (d h : R) : Matrix (Fin 2) (Fin 2) R :=
  !![d, h; -h, d]

/-- HLR Ioffe–Larkin total resistivity `ρ_total = ρ_f + ρ_CS` at `ν = 1/2`. -/
def ioffeLarkinRhoTotal {R : Type*} [CommRing R] (rxx rxy : R) : Matrix (Fin 2) (Fin 2) R :=
  hallMat rxx (-rxy) + hallMat 0 (-2)

/-- Son/MAM Dirac-CFL cleared-denominator EM conductivity `4 D_f σ_EM`. -/
def diracCflFourDfSigmaEM {R : Type*} [CommRing R] (sxx sxy : R) : Matrix (Fin 2) (Fin 2) R :=
  hallMat sxx (2 * (sxx ^ 2 + sxy ^ 2) - sxy)

/-- Background half-filling Hall conductivity `2 σ_bg = [[0, 1], [-1, 0]]`. -/
def twoSigmaBgHalf (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  hallMat 0 1

theorem hallMat_mul {R : Type*} [CommRing R] (d1 h1 d2 h2 : R) :
    hallMat d1 h1 * hallMat d2 h2 = hallMat (d1 * d2 - h1 * h2) (d1 * h2 + h1 * d2) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hallMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem hallMat_add {R : Type*} [CommRing R] (d1 h1 d2 h2 : R) :
    hallMat d1 h1 + hallMat d2 h2 = hallMat (d1 + d2) (h1 + h2) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hallMat]; ring

theorem hallMat_neg {R : Type*} [CommRing R] (d h : R) :
    -hallMat d h = hallMat (-d) (-h) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hallMat]

theorem hallMat_smul {R : Type*} [CommRing R] (c d h : R) :
    c • hallMat d h = hallMat (c * d) (c * h) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hallMat]

theorem hallMat_adj_mul {R : Type*} [CommRing R] (d h : R) :
    hallMat d h * hallMat d (-h) = (d ^ 2 + h ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hallMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem hallMat_det {R : Type*} [CommRing R] (d h : R) :
    (hallMat d h).det = d ^ 2 + h ^ 2 := by
  rw [hallMat, Matrix.det_fin_two_of]; ring

theorem ioffeLarkinRhoTotal_eq {R : Type*} [CommRing R] (rxx rxy : R) :
    ioffeLarkinRhoTotal rxx rxy = hallMat rxx (-(rxy + 2)) := by
  rw [ioffeLarkinRhoTotal, hallMat_add]; congr 1 <;> ring

theorem ioffeLarkin_rho_inv {R : Type*} [CommRing R] (rxx rxy : R) :
    ioffeLarkinRhoTotal rxx rxy * hallMat rxx (rxy + 2) =
      (rxx ^ 2 + (rxy + 2) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [ioffeLarkinRhoTotal_eq, hallMat_mul]
  ext i j; fin_cases i <;> fin_cases j <;> simp [hallMat] <;> ring

theorem ioffeLarkin_sigma_of_sigma_f {R : Type*} [CommRing R] (sxx sxy : R) :
    let Df := sxx ^ 2 + sxy ^ 2
    let den := 4 * sxx ^ 2 + (1 + 2 * sxy) ^ 2
    (hallMat sxx (-sxy) + Df • hallMat (0 : R) (-2)) * hallMat sxx (sxy + 2 * Df) =
      (Df * den) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  simp only
  rw [hallMat_smul, hallMat_add, hallMat_mul]
  ext i j; fin_cases i <;> fin_cases j <;> simp [hallMat] <;> ring

theorem diracCfl_mutualCS_inversion {R : Type*} [CommRing R] (sxx sxy : R) :
    (diracCflFourDfSigmaEM sxx sxy - (2 * (sxx ^ 2 + sxy ^ 2)) • twoSigmaBgHalf R) *
        hallMat sxx sxy =
      (sxx ^ 2 + sxy ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  simp only [diracCflFourDfSigmaEM, twoSigmaBgHalf, sub_eq_add_neg]
  rw [hallMat_smul, hallMat_neg, hallMat_add, hallMat_mul]
  ext i j; fin_cases i <;> fin_cases j <;> simp [hallMat] <;> ring

theorem diracCfl_ph_sym_hall_half {R : Type*} [CommRing R] (sxx : R) :
    diracCflFourDfSigmaEM sxx (0 : R) 0 1 = 2 * sxx ^ 2 ∧
    2 * diracCflFourDfSigmaEM sxx (0 : R) 0 1 = 4 * (sxx ^ 2 + (0 : R) ^ 2) := by
  refine ⟨by simp [diracCflFourDfSigmaEM, hallMat], ?_⟩
  simp only [diracCflFourDfSigmaEM, hallMat, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem diracCfl_particle_hole_sum_rule {R : Type*} [CommRing R] (sxx sxy sxy_ph : R)
    (hph : sxy + sxy_ph = 0) :
    diracCflFourDfSigmaEM sxx sxy 0 1 + diracCflFourDfSigmaEM sxx sxy_ph 0 1 =
      4 * (sxx ^ 2 + sxy ^ 2) := by
  have hsxy : sxy_ph = -sxy := eq_neg_of_add_eq_zero_right hph
  subst hsxy
  simp only [diracCflFourDfSigmaEM, hallMat, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem diracCfl_em_to_fermion_inv {R : Type*} [CommRing R] (sxx4 sxy4 : R) :
    hallMat sxx4 (sxy4 - 2) * hallMat sxx4 (-(sxy4 - 2)) =
      (sxx4 ^ 2 + (sxy4 - 2) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) :=
  hallMat_adj_mul sxx4 (sxy4 - 2)

end Bosonize.CoupledWire
