module

public import Bosonize.Core.CoupledWire.DiracMass
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Finite Coupled-Wire SSH / Dirac Edge Zero-Mode Kinematics (`HC-QMB-09b`)

Formalizes the finite-`N` open- and closed-boundary alternating SSH / coupled-wire Dirac
mass Hamiltonian `sshWireMatrix a b N` over `ℤ` on pinned Mathlib4 `Finset.sum`:
- symmetry, chiral conjugation `P H P = -H`, and exact odd-wire (`2m + 1`) chiral zero mode;
- left/right even-wire (`2m`) chiral edge ansatze, interior vanishing, exact far-boundary
  residual `-((-a)^m)`, exact `ker(H_OBC)` iff `a = 0`, and kernel triviality for `a ≠ 0`;
- exact OBC edge hybridization `a (-a)^(m-1) b^(m-1)`, PBC closing-bond coupling
  `c b^(2m-2)`, total PBC-closed splitting, chiral diagonal orthogonality, norm equality,
  boundary lower bound, and exponential/power-law hybridization suppression when `|a| < |b|`.
-/

@[expose] public section

namespace Bosonize.CoupledWire

open scoped BigOperators

/-- Finite coupled-wire alternating SSH dimerization Hamiltonian matrix `H_{y,z}` on `N` wires. -/
def sshWireMatrix (a b : ℤ) (N y z : ℕ) : ℤ :=
  wireMassEntry N a b y z

/-- Left-localized chiral edge vector on `N = 2m` (`m ≥ 1`), supported on even wires `2k`. -/
def leftEdgeVec (a b : ℤ) (m y : ℕ) : ℤ :=
  evenWireEdgeAnsatz a b m y

/-- Unpaired chiral edge zero-mode on odd wire count `N = 2m + 1`. -/
def oddLeftEdgeVec (a b : ℤ) (m y : ℕ) : ℤ :=
  dimerizedOddWireZeroMode a b m y

/-- Right-localized chiral edge vector on `N = 2m` (`m ≥ 1`), supported on odd wires `2k + 1`. -/
def rightEdgeVec (a b : ℤ) (m y : ℕ) : ℤ :=
  if y % 2 = 1 then (-a) ^ (m - 1 - y / 2) * b ^ (y / 2) else 0

/-- Closing boundary bond `(0, N - 1)` of coupling `c : ℤ` on `N ≥ 2` wires. -/
def sshCloseBondMatrix (c : ℤ) (N y z : ℕ) : ℤ :=
  if 2 ≤ N ∧ y < N ∧ z < N ∧ ((y = 0 ∧ z = N - 1) ∨ (y = N - 1 ∧ z = 0)) then c else 0

/-- Full periodic-boundary-closed SSH matrix `H_close = H_OBC + H_closeBond`. -/
def sshCloseMatrix (a b c : ℤ) (N y z : ℕ) : ℤ :=
  sshWireMatrix a b N y z + sshCloseBondMatrix c N y z

/-! ### 1. Symmetry, Chirality & Sublattice Orthogonality -/

theorem sshWireMatrix_symm (a b : ℤ) (N y z : ℕ) :
    sshWireMatrix a b N y z = sshWireMatrix a b N z y :=
  wireMassEntry_symm N a b y z

theorem sshWire_chiral_anticomm_add (a b : ℤ) (N y z : ℕ) :
    paritySign y * sshWireMatrix a b N y z + sshWireMatrix a b N y z * paritySign z = 0 :=
  wireMassEntry_chiral_anticomm N a b y z

theorem sshWire_chiral_anticomm (a b : ℤ) (N y z : ℕ) :
    paritySign y * sshWireMatrix a b N y z * paritySign z = -sshWireMatrix a b N y z := by
  have h := sshWire_chiral_anticomm_add a b N y z
  have hsq := paritySign_sq z
  linear_combination paritySign z * h - sshWireMatrix a b N y z * hsq

theorem oddLeftEdgeVec_eq_leftEdgeVec_succ (a b : ℤ) (m y : ℕ) :
    oddLeftEdgeVec a b m y = leftEdgeVec a b (m + 1) y := by
  simp [oddLeftEdgeVec, leftEdgeVec, dimerizedOddWireZeroMode, evenWireEdgeAnsatz]

theorem leftEdgeVec_chiral (a b : ℤ) (m y : ℕ) :
    paritySign y * leftEdgeVec a b m y = leftEdgeVec a b m y := by
  unfold leftEdgeVec evenWireEdgeAnsatz paritySign; split_ifs <;> simp

theorem oddLeftEdgeVec_chiral (a b : ℤ) (m y : ℕ) :
    paritySign y * oddLeftEdgeVec a b m y = oddLeftEdgeVec a b m y := by
  rw [oddLeftEdgeVec_eq_leftEdgeVec_succ]; exact leftEdgeVec_chiral a b (m + 1) y

theorem rightEdgeVec_chiral (a b : ℤ) (m y : ℕ) :
    paritySign y * rightEdgeVec a b m y = -rightEdgeVec a b m y := by
  unfold rightEdgeVec paritySign; split_ifs <;> omega

theorem leftEdgeVec_rightEdgeVec_orth (a b : ℤ) (m y : ℕ) :
    leftEdgeVec a b m y * rightEdgeVec a b m y = 0 := by
  unfold leftEdgeVec evenWireEdgeAnsatz rightEdgeVec; split_ifs <;> omega

/-! ### 2. Left/Right Even-Wire Residuals, Dimer Zero Modes & Odd-Wire Zero Mode -/

theorem sshWire_even_leftEdge_residual (a b : ℤ) (m y : ℕ) (hm : 1 ≤ m) (hy : y < 2 * m) :
    ∑ z ∈ Finset.range (2 * m), sshWireMatrix a b (2 * m) y z * leftEdgeVec a b m z =
      if y + 1 = 2 * m then -((-a) ^ m) else 0 :=
  evenWireEdgeAnsatz_residual a b m y hm hy

theorem sshWire_even_leftEdge_interior_zero (a b : ℤ) (m y : ℕ) (hm : 1 ≤ m) (hy : y + 1 < 2 * m) :
    ∑ z ∈ Finset.range (2 * m), sshWireMatrix a b (2 * m) y z * leftEdgeVec a b m z = 0 := by
  rw [sshWire_even_leftEdge_residual a b m y hm (by omega)]
  simp [show y + 1 ≠ 2 * m by omega]

theorem sshWire_even_leftEdge_zero (b : ℤ) (m y : ℕ) (hm : 1 ≤ m) (hy : y < 2 * m) :
    ∑ z ∈ Finset.range (2 * m), sshWireMatrix 0 b (2 * m) y z * leftEdgeVec 0 b m z = 0 := by
  rw [sshWire_even_leftEdge_residual 0 b m y hm hy]
  split_ifs <;> simp [zero_pow (by omega : m ≠ 0)]

theorem sshWire_even_leftEdge_zero_iff (a b : ℤ) (m : ℕ) (hm : 1 ≤ m) :
    (∀ y, y < 2 * m →
      ∑ z ∈ Finset.range (2 * m), sshWireMatrix a b (2 * m) y z * leftEdgeVec a b m z = 0) ↔
      a = 0 := by
  constructor
  · intro hker
    have hlast := hker (2 * m - 1) (by omega)
    rw [sshWire_even_leftEdge_residual a b m (2 * m - 1) hm (by omega)] at hlast
    simp only [show (2 * m - 1) + 1 = 2 * m by omega, ↓reduceIte] at hlast
    have hpow : (-a) ^ m = 0 := by omega
    have hneg : -a = 0 := (pow_eq_zero_iff (by omega : m ≠ 0)).mp hpow
    omega
  · rintro rfl y hy; exact sshWire_even_leftEdge_zero b m y hm hy

/-- Exact finite-wire residual of `rightEdgeVec` on `N = 2m` (`m ≥ 1`):
vanishes on `0 < y < 2m` and equals `-((-a)^m)` solely on row `y = 0`. -/
theorem sshWire_even_rightEdge_residual (a b : ℤ) (m y : ℕ) (hm : 1 ≤ m) (hy : y < 2 * m) :
    ∑ z ∈ Finset.range (2 * m), sshWireMatrix a b (2 * m) y z * rightEdgeVec a b m z =
      if y = 0 then -((-a) ^ m) else 0 := by
  simp only [sshWireMatrix]
  rw [wireMass_row_eval (2 * m) a b _ y hy]
  by_cases hy_odd : y % 2 = 1
  · have hy0 : y ≠ 0 := by omega
    have h1 : (y + 1) % 2 ≠ 1 := by omega
    have h2 : (y - 1) % 2 ≠ 1 := by omega
    simp [hy0, rightEdgeVec, h1, h2]
  · by_cases hy0 : y = 0
    · subst hy0
      have hpow : (-a) ^ m = (-a) ^ (m - 1) * (-a) := by
        rw [← pow_succ, show m - 1 + 1 = m by omega]
      simp only [show 1 < 2 * m by omega, show ¬ (0 < 0) by omega, Nat.zero_mod, ↓reduceIte,
        add_zero, rightEdgeVec, show (1 : ℕ) % 2 = 1 by decide, show (1 : ℕ) / 2 = 0 by decide,
        Nat.sub_zero, pow_zero, mul_one, hpow]
      ring
    · have hy_pos : 0 < y := by omega
      have hyu : y + 1 < 2 * m := by omega
      have ho1 : (y + 1) % 2 = 1 := by omega
      have ho2 : (y - 1) % 2 = 1 := by omega
      have hk : (y + 1) / 2 = (y - 1) / 2 + 1 := by omega
      have hm1 : m - 1 - (y - 1) / 2 = (m - 1 - ((y - 1) / 2 + 1)) + 1 := by omega
      simp only [hy0, hyu, hy_pos, show y % 2 = 0 by omega,
        ↓reduceIte, rightEdgeVec, ho1, ho2, one_ne_zero, hk, hm1, pow_succ]
      ring

theorem sshWire_even_rightEdge_interior_zero (a b : ℤ) (m y : ℕ) (hm : 1 ≤ m)
    (hy0 : 0 < y) (hy : y < 2 * m) :
    ∑ z ∈ Finset.range (2 * m), sshWireMatrix a b (2 * m) y z * rightEdgeVec a b m z = 0 := by
  rw [sshWire_even_rightEdge_residual a b m y hm hy]
  simp [show y ≠ 0 by omega]

theorem sshWire_even_rightEdge_zero (b : ℤ) (m y : ℕ) (hm : 1 ≤ m) (hy : y < 2 * m) :
    ∑ z ∈ Finset.range (2 * m), sshWireMatrix 0 b (2 * m) y z * rightEdgeVec 0 b m z = 0 := by
  rw [sshWire_even_rightEdge_residual 0 b m y hm hy]
  split_ifs <;> simp [zero_pow (by omega : m ≠ 0)]

theorem sshWire_even_rightEdge_zero_iff (a b : ℤ) (m : ℕ) (hm : 1 ≤ m) :
    (∀ y, y < 2 * m →
      ∑ z ∈ Finset.range (2 * m), sshWireMatrix a b (2 * m) y z * rightEdgeVec a b m z = 0) ↔
      a = 0 := by
  constructor
  · intro hker
    have h0 := hker 0 (by omega)
    rw [sshWire_even_rightEdge_residual a b m 0 hm (by omega)] at h0
    simp only [↓reduceIte] at h0
    have hpow : (-a) ^ m = 0 := by omega
    have hneg : -a = 0 := (pow_eq_zero_iff (by omega : m ≠ 0)).mp hpow
    omega
  · rintro rfl y hy; exact sshWire_even_rightEdge_zero b m y hm hy

theorem sshWire_even_kernel_trivial (a b : ℤ) (ha : a ≠ 0) (m : ℕ) (v : ℕ → ℤ)
    (hker : ∀ y, y < 2 * m →
      ∑ z ∈ Finset.range (2 * m), sshWireMatrix a b (2 * m) y z * v z = 0) :
    ∀ z, z < 2 * m → v z = 0 :=
  wireMass_even_kernel_eq_zero a b ha m v hker

theorem sshWire_odd_leftEdge_zero (a b : ℤ) (m y : ℕ) (hy : y < 2 * m + 1) :
    ∑ z ∈ Finset.range (2 * m + 1), sshWireMatrix a b (2 * m + 1) y z * oddLeftEdgeVec a b m z = 0 :=
  dimerizedOddWireZeroMode_in_kernel a b m y hy

theorem sshWire_odd_leftEdge_nonzero (a b : ℤ) (m : ℕ) (ht : a ≠ 0 ∨ b ≠ 0) :
    ∃ y, y < 2 * m + 1 ∧ oddLeftEdgeVec a b m y ≠ 0 :=
  dimerizedOddWireZeroMode_nonzero a b m ht

/-! ### 3. Closing-Bond Coupling, Hybridization Splitting & Decay Bound -/

theorem sshCloseBondMatrix_symm (c : ℤ) (N y z : ℕ) :
    sshCloseBondMatrix c N y z = sshCloseBondMatrix c N z y := by
  unfold sshCloseBondMatrix; split_ifs <;> omega

theorem sshCloseMatrix_symm (a b c : ℤ) (N y z : ℕ) :
    sshCloseMatrix a b c N y z = sshCloseMatrix a b c N z y := by
  simp only [sshCloseMatrix, sshWireMatrix_symm, sshCloseBondMatrix_symm]

theorem sshCloseMatrix_even_chiral_anticomm (a b c : ℤ) (m y z : ℕ) :
    paritySign y * sshCloseMatrix a b c (2 * m) y z * paritySign z =
      -sshCloseMatrix a b c (2 * m) y z := by
  simp only [sshCloseMatrix, mul_add, add_mul, sshWire_chiral_anticomm]
  have hbond : paritySign y * sshCloseBondMatrix c (2 * m) y z * paritySign z =
      -sshCloseBondMatrix c (2 * m) y z := by
    unfold sshCloseBondMatrix
    split_ifs with h
    · rcases h with ⟨hN, _, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
      · have hodd : (2 * m - 1) % 2 ≠ 0 := by omega
        simp [paritySign, hodd]
    · ring
  rw [hbond]; ring

/-- Exact OBC edge-to-edge hybridization `<rightEdgeVec, H_OBC leftEdgeVec> = a (-a)^(m-1) b^(m-1)`. -/
theorem sshWire_even_edge_hybridization (a b : ℤ) (m : ℕ) (hm : 1 ≤ m) :
    ∑ y ∈ Finset.range (2 * m), ∑ z ∈ Finset.range (2 * m),
      rightEdgeVec a b m y * sshWireMatrix a b (2 * m) y z * leftEdgeVec a b m z =
      a * (-a) ^ (m - 1) * b ^ (m - 1) := by
  have hrow : ∀ y ∈ Finset.range (2 * m),
      ∑ z ∈ Finset.range (2 * m),
        rightEdgeVec a b m y * sshWireMatrix a b (2 * m) y z * leftEdgeVec a b m z =
        if y = 2 * m - 1 then rightEdgeVec a b m (2 * m - 1) * (-((-a) ^ m)) else 0 := by
    intro y hy
    rw [Finset.sum_congr rfl (fun z _ => mul_assoc _ _ _), ← Finset.mul_sum,
      sshWire_even_leftEdge_residual a b m y hm (Finset.mem_range.mp hy)]
    by_cases hlast : y = 2 * m - 1
    · subst hlast; simp [show (2 * m - 1) + 1 = 2 * m by omega]
    · simp [hlast, show y + 1 ≠ 2 * m by omega]
  rw [Finset.sum_congr rfl hrow, Finset.sum_ite_eq' (Finset.range (2 * m)) (2 * m - 1)]
  simp only [Finset.mem_range.mpr (by omega : 2 * m - 1 < 2 * m), ↓reduceIte]
  have hpow : (-a) ^ m = (-a) ^ (m - 1) * (-a) := by
    rw [← pow_succ, show m - 1 + 1 = m by omega]
  simp only [rightEdgeVec, show (2 * m - 1) % 2 = 1 by omega, show (2 * m - 1) / 2 = m - 1 by omega,
    Nat.sub_self, pow_zero, one_mul, ↓reduceIte, hpow]
  ring

/-- Exact PBC closing-bond matrix element `<rightEdgeVec, H_closeBond leftEdgeVec> = c b^(2m-2)`. -/
theorem sshCloseBond_even_edge_coupling (a b c : ℤ) (m : ℕ) (hm : 1 ≤ m) :
    ∑ y ∈ Finset.range (2 * m), ∑ z ∈ Finset.range (2 * m),
      rightEdgeVec a b m y * sshCloseBondMatrix c (2 * m) y z * leftEdgeVec a b m z =
      c * b ^ (m - 1) * b ^ (m - 1) := by
  have hrow : ∀ y ∈ Finset.range (2 * m),
      ∑ z ∈ Finset.range (2 * m),
        rightEdgeVec a b m y * sshCloseBondMatrix c (2 * m) y z * leftEdgeVec a b m z =
        if y = 2 * m - 1 then rightEdgeVec a b m (2 * m - 1) * c * leftEdgeVec a b m 0 else 0 := by
    intro y hy
    have hy' : y < 2 * m := Finset.mem_range.mp hy
    by_cases hlast : y = 2 * m - 1
    · subst hlast
      have hrew : ∀ z ∈ Finset.range (2 * m),
          rightEdgeVec a b m (2 * m - 1) * sshCloseBondMatrix c (2 * m) (2 * m - 1) z *
              leftEdgeVec a b m z =
            if z = 0 then rightEdgeVec a b m (2 * m - 1) * c * leftEdgeVec a b m 0 else 0 := by
        intro z hz
        by_cases hz0 : z = 0
        · subst hz0; simp [sshCloseBondMatrix, show 2 ≤ 2 * m by omega, hy', Finset.mem_range.mp hz]
        · unfold sshCloseBondMatrix; split_ifs <;> omega
      rw [Finset.sum_congr rfl hrew, Finset.sum_ite_eq' (Finset.range (2 * m)) 0]
      simp [Finset.mem_range.mpr (by omega : 0 < 2 * m)]
    · have hzero : ∀ z ∈ Finset.range (2 * m),
          rightEdgeVec a b m y * sshCloseBondMatrix c (2 * m) y z * leftEdgeVec a b m z = 0 := by
        intro z _
        unfold sshCloseBondMatrix leftEdgeVec evenWireEdgeAnsatz rightEdgeVec
        split_ifs <;> omega
      rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
      simp [hlast]
  rw [Finset.sum_congr rfl hrow, Finset.sum_ite_eq' (Finset.range (2 * m)) (2 * m - 1)]
  simp only [Finset.mem_range.mpr (by omega : 2 * m - 1 < 2 * m), ↓reduceIte]
  simp only [rightEdgeVec, show (2 * m - 1) % 2 = 1 by omega, show (2 * m - 1) / 2 = m - 1 by omega,
    Nat.sub_self, pow_zero, one_mul, ↓reduceIte, leftEdgeVec, evenWireEdgeAnsatz,
    Nat.zero_mod, Nat.zero_div, Nat.sub_zero]
  ring

/-- Total PBC-closed edge splitting `<rightEdgeVec, H_close leftEdgeVec>`. -/
theorem sshClose_even_edge_splitting (a b c : ℤ) (m : ℕ) (hm : 1 ≤ m) :
    ∑ y ∈ Finset.range (2 * m), ∑ z ∈ Finset.range (2 * m),
      rightEdgeVec a b m y * sshCloseMatrix a b c (2 * m) y z * leftEdgeVec a b m z =
      c * b ^ (m - 1) * b ^ (m - 1) + a * (-a) ^ (m - 1) * b ^ (m - 1) := by
  have hsplit : ∀ y ∈ Finset.range (2 * m),
      ∑ z ∈ Finset.range (2 * m),
        rightEdgeVec a b m y * sshCloseMatrix a b c (2 * m) y z * leftEdgeVec a b m z =
      (∑ z ∈ Finset.range (2 * m),
        rightEdgeVec a b m y * sshWireMatrix a b (2 * m) y z * leftEdgeVec a b m z) +
      (∑ z ∈ Finset.range (2 * m),
        rightEdgeVec a b m y * sshCloseBondMatrix c (2 * m) y z * leftEdgeVec a b m z) := by
    intro y _
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun z _ => by simp only [sshCloseMatrix]; ring)
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    sshWire_even_edge_hybridization a b m hm, sshCloseBond_even_edge_coupling a b c m hm]
  ring

/-- Exact chiral orthogonality of diagonal edge expectation values under `H_close`. -/
theorem sshClose_even_diag_zero (a b c : ℤ) (m : ℕ) :
    (∑ y ∈ Finset.range (2 * m), ∑ z ∈ Finset.range (2 * m),
      leftEdgeVec a b m y * sshCloseMatrix a b c (2 * m) y z * leftEdgeVec a b m z = 0) ∧
    (∑ y ∈ Finset.range (2 * m), ∑ z ∈ Finset.range (2 * m),
      rightEdgeVec a b m y * sshCloseMatrix a b c (2 * m) y z * rightEdgeVec a b m z = 0) := by
  constructor
  · apply Finset.sum_eq_zero; intro y _
    apply Finset.sum_eq_zero; intro z _
    by_cases hy0 : y % 2 = 0 <;> by_cases hz0 : z % 2 = 0
    · have hant := sshCloseMatrix_even_chiral_anticomm a b c m y z
      simp only [paritySign, hy0, hz0, ↓reduceIte, one_mul, mul_one] at hant
      have h0 : sshCloseMatrix a b c (2 * m) y z = 0 := by omega
      simp [h0]
    · simp [leftEdgeVec, evenWireEdgeAnsatz, hz0]
    · simp [leftEdgeVec, evenWireEdgeAnsatz, hy0]
    · simp [leftEdgeVec, evenWireEdgeAnsatz, hy0]
  · apply Finset.sum_eq_zero; intro y _
    apply Finset.sum_eq_zero; intro z _
    by_cases hy1 : y % 2 = 1 <;> by_cases hz1 : z % 2 = 1
    · have hant := sshCloseMatrix_even_chiral_anticomm a b c m y z
      simp only [paritySign, show y % 2 ≠ 0 by omega, show z % 2 ≠ 0 by omega, ↓reduceIte] at hant
      have h0 : sshCloseMatrix a b c (2 * m) y z = 0 := by omega
      simp [h0]
    · simp [rightEdgeVec, hz1]
    · simp [rightEdgeVec, hy1]
    · simp [rightEdgeVec, hy1]

/-- Exact equality of squared Euclidean norms of `leftEdgeVec` and `rightEdgeVec` on `N = 2m`. -/
theorem leftEdgeVec_normSq_eq_rightEdgeVec_normSq (a b : ℤ) (m : ℕ) :
    ∑ z ∈ Finset.range (2 * m), leftEdgeVec a b m z * leftEdgeVec a b m z =
      ∑ z ∈ Finset.range (2 * m), rightEdgeVec a b m z * rightEdgeVec a b m z := by
  have hleft : ∀ n,
      ∑ z ∈ Finset.range (2 * n), leftEdgeVec a b m z * leftEdgeVec a b m z =
        ∑ k ∈ Finset.range n, ((-a) ^ k * b ^ (m - 1 - k)) * ((-a) ^ k * b ^ (m - 1 - k)) := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
        ih, Finset.sum_range_succ]
      simp [leftEdgeVec, evenWireEdgeAnsatz]
  have hright : ∀ n,
      ∑ z ∈ Finset.range (2 * n), rightEdgeVec a b m z * rightEdgeVec a b m z =
        ∑ k ∈ Finset.range n, ((-a) ^ (m - 1 - k) * b ^ k) * ((-a) ^ (m - 1 - k) * b ^ k) := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
        ih, Finset.sum_range_succ]
      simp [rightEdgeVec, show (2 * n + 1) % 2 = 1 by omega,
        show (2 * n + 1) / 2 = n by omega]
  rw [hleft m, hright m, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl; intro k hk
  have hk' : k < m := Finset.mem_range.mp hk
  have hkk : m - 1 - (m - 1 - k) = k := by omega
  rw [hkk]

/-- The `z = 0` boundary weight `b^(2m-2)` lower-bounds `‖leftEdgeVec‖²` (`m ≥ 1`). -/
theorem leftEdgeVec_normSq_ge_boundary (a b : ℤ) (m : ℕ) (hm : 1 ≤ m) :
    b ^ (2 * m - 2) ≤ ∑ z ∈ Finset.range (2 * m), leftEdgeVec a b m z * leftEdgeVec a b m z := by
  have h0 : leftEdgeVec a b m 0 * leftEdgeVec a b m 0 = b ^ (2 * m - 2) := by
    simp only [leftEdgeVec, evenWireEdgeAnsatz, Nat.zero_mod, Nat.zero_div, pow_zero,
      Nat.sub_zero, one_mul, ↓reduceIte, ← pow_add]
    congr 1; omega
  rw [← h0]
  exact Finset.single_le_sum (fun z _ => mul_self_nonneg _) (Finset.mem_range.mpr (by omega))

/-- Exponential/power-law hybridization suppression in the topological phase `|a| < |b|` (`m ≥ 2`). -/
theorem sshWire_even_hybridization_decay_bound (a b : ℤ) (m : ℕ)
    (hm : 2 ≤ m) (ha : a ≠ 0) (hab : a.natAbs < b.natAbs) :
    (a * (-a) ^ (m - 1) * b ^ (m - 1)).natAbs < a.natAbs * (b ^ (2 * m - 2)).natAbs := by
  have ha_pos : 0 < a.natAbs := Int.natAbs_pos.mpr ha
  have hpow : a.natAbs ^ (m - 1) < b.natAbs ^ (m - 1) :=
    Nat.pow_lt_pow_left hab (by omega)
  have hb_pow_pos : 0 < b.natAbs ^ (m - 1) := Nat.pow_pos (by omega)
  have hlhs : (a * (-a) ^ (m - 1) * b ^ (m - 1)).natAbs =
      a.natAbs * (a.natAbs ^ (m - 1) * b.natAbs ^ (m - 1)) := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_pow, mul_assoc]
  have hrhs : (b ^ (2 * m - 2)).natAbs = b.natAbs ^ (m - 1) * b.natAbs ^ (m - 1) := by
    rw [Int.natAbs_pow, ← Nat.pow_add]; congr 1; omega
  rw [hlhs, hrhs]
  exact Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_right hpow hb_pow_pos) ha_pos

end Bosonize.CoupledWire
