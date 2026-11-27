module

public import Bosonize.Core.CoupledWire.BlochDiracAndGauge
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# 6-Wire 3-Cone Bloch Hamiltonian, Universal Block Determinant & Fu–Kane ↔ `T`-Pfaffian Duality

Formalizes Mross–Alicea–Motrunich (`arXiv:1510.08455`, Sec. V & App. 4) on pinned Mathlib4:
- 3-sublattice partition `sublatticeMod3` and 6-wire chirality pairing;
- universal characteristic-free block determinant `det_fromBlocks_scalar_diag` over ALL
  `[Fintype m] [DecidableEq m] [CommRing R]` (superseding fixed-`4×4` Laplace expansion);
- 6-wire 3-cone Bloch Hamiltonian `Matrix.fromBlocks`, exact `4×4` & `2×2` determinants and
  characteristic polynomials, cone 0–1 mass gapping (`det ≥ m^4 > 0`), and unique cone-2 node;
- exact finite-`N` Fu–Kane ↔ `T`-Pfaffian `D^T` duality for `fkPairOp` (preserving the exact `3y+2`
  exponent `-4` correction to MAM App. 4 Eq. (63)), `fkProximityOp`, `fkCone2HopOp`, and charge/parity.
-/

@[expose] public section

namespace Bosonize.CoupledWire

open scoped BigOperators
open Matrix Polynomial

/-! ### 1. 3-Sublattice Partition & Universal Scalar-Diagonal Block Determinant -/

/-- 3-sublattice (3-Dirac-cone) wire residue `y mod 3 : Fin 3`. -/
def sublatticeMod3 (y : ℕ) : Fin 3 :=
  ⟨y % 3, Nat.mod_lt y (by decide)⟩

theorem sublatticeMod3_add_three (y : ℕ) : sublatticeMod3 (y + 3) = sublatticeMod3 y := by
  simp only [sublatticeMod3, Fin.mk.injEq]; omega

theorem sublatticeMod3_three_mul_add (k r : ℕ) (hr : r < 3) :
    sublatticeMod3 (3 * k + r) = ⟨r, hr⟩ := by
  simp only [sublatticeMod3, Fin.mk.injEq]; omega

theorem threeCone_intraCell_opposite_chirality (q r : ℕ) :
    paritySign (6 * q + r) + paritySign (6 * q + r + 3) = 0 ∧
    paritySign (6 * q + r) * paritySign (6 * q + r + 3) = -1 := by
  rw [paritySign_add_three]
  have hsq := paritySign_sq (6 * q + r)
  exact ⟨by ring, by linear_combination -hsq⟩

theorem threeCone_mass_opposite_chirality (y : ℕ) :
    paritySign (3 * y) * paritySign (3 * y + 1) = -1 ∧
    sublatticeMod3 (3 * y) = ⟨0, by decide⟩ ∧
    sublatticeMod3 (3 * y + 1) = ⟨1, by decide⟩ ∧
    sublatticeMod3 (3 * y + 2) = ⟨2, by decide⟩ :=
  ⟨paritySign_mul_succ (3 * y), sublatticeMod3_three_mul_add y 0 (by decide),
   sublatticeMod3_three_mul_add y 1 (by decide), sublatticeMod3_three_mul_add y 2 (by decide)⟩

/-- Universal block-determinant identity for scalar diagonal blocks over ANY finite type `m`
and ANY commutative ring `R`: `det [[a I, B], [C, d I]] = det ((a d) I - B C)`. -/
theorem det_fromBlocks_scalar_diag {m : Type*} [Fintype m] [DecidableEq m]
    {R : Type*} [CommRing R] (a d : R) (B C : Matrix m m R) :
    (Matrix.fromBlocks (a • (1 : Matrix m m R)) B C (d • (1 : Matrix m m R))).det =
      ((a * d) • (1 : Matrix m m R) - B * C).det := by
  let Bp : Matrix m m (Polynomial R) := B.map Polynomial.C
  let Cp : Matrix m m (Polynomial R) := C.map Polynomial.C
  have hmul :
      Matrix.fromBlocks ((Polynomial.X : Polynomial R) • (1 : Matrix m m (Polynomial R))) (-Bp) 0 1 *
      Matrix.fromBlocks ((Polynomial.C a) • (1 : Matrix m m (Polynomial R))) Bp Cp
        ((Polynomial.X : Polynomial R) • (1 : Matrix m m (Polynomial R))) =
      Matrix.fromBlocks ((Polynomial.C a * Polynomial.X) • (1 : Matrix m m (Polynomial R)) - Bp * Cp)
        0 Cp ((Polynomial.X : Polynomial R) • (1 : Matrix m m (Polynomial R))) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_one,
        mul_comm Polynomial.X (Polynomial.C a), Matrix.neg_mul, sub_eq_add_neg]
    · rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
        smul_neg, add_neg_cancel]
    · simp
    · simp
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, mul_one, Matrix.det_smul, Matrix.det_one, mul_one,
    mul_comm (Polynomial.X ^ Fintype.card m)] at hdet
  have hpoly :
      (Matrix.fromBlocks ((Polynomial.C a) • (1 : Matrix m m (Polynomial R))) Bp Cp
        ((Polynomial.X : Polynomial R) • (1 : Matrix m m (Polynomial R)))).det =
      ((Polynomial.C a * Polynomial.X) • (1 : Matrix m m (Polynomial R)) - Bp * Cp).det :=
    (Polynomial.Monic.isRegular (Polynomial.monic_X_pow (Fintype.card m))).right hdet
  have heval := congrArg (Polynomial.evalRingHom d) hpoly
  rw [RingHom.map_det, RingHom.map_det] at heval
  simp only [RingHom.mapMatrix_apply] at heval
  have hmapL :
      (Matrix.fromBlocks ((Polynomial.C a) • (1 : Matrix m m (Polynomial R))) Bp Cp
        ((Polynomial.X : Polynomial R) • (1 : Matrix m m (Polynomial R)))).map (Polynomial.evalRingHom d) =
      Matrix.fromBlocks (a • (1 : Matrix m m R)) B C (d • (1 : Matrix m m R)) := by
    ext i j; cases i <;> cases j <;> simp [Bp, Cp, Matrix.one_apply] <;> split_ifs <;> simp
  have hmapR :
      (((Polynomial.C a * Polynomial.X) • (1 : Matrix m m (Polynomial R)) - Bp * Cp)).map
        (Polynomial.evalRingHom d) =
      (a * d) • (1 : Matrix m m R) - B * C := by
    ext i j
    simp [Bp, Cp, Matrix.mul_apply, Matrix.one_apply, Polynomial.eval_finsetSum]
    split_ifs <;> simp
  rwa [hmapL, hmapR] at heval

/-! ### 2. 6-Wire 3-Cone Bloch Hamiltonian, Mass Gapping & Surviving Cone-2 Dirac Node -/

/-- Homogeneous single-cone staggered hopping off-diagonal entry `w ((r - c) + i s)`. -/
def coneHopOffDiag (w r c s : ℤ) : GaussianInt :=
  ⟨w * (r - c), w * s⟩

/-- Chiral off-diagonal `2×2` mass-and-hopping block `B` for cones 0 and 1. -/
def threeCone01BlockB (w0 w1 m r c s : ℤ) : Matrix (Fin 2) (Fin 2) GaussianInt :=
  !![coneHopOffDiag w0 r c s, ⟨m, 0⟩; ⟨-m, 0⟩, star (coneHopOffDiag w1 r c s)]

/-- `4×4` Bloch Hamiltonian `H_{01}` for cones 0 and 1 as `Matrix.fromBlocks`. -/
def threeCone01Ham (v kx w0 w1 m r c s : ℤ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) GaussianInt :=
  let B := threeCone01BlockB w0 w1 m r c s
  Matrix.fromBlocks
    ((⟨v * kx, 0⟩ : GaussianInt) • (1 : Matrix (Fin 2) (Fin 2) GaussianInt)) B
    Bᴴ ((⟨-(v * kx), 0⟩ : GaussianInt) • (1 : Matrix (Fin 2) (Fin 2) GaussianInt))

/-- `2×2` Bloch Hamiltonian `H_2` and full `6×6` 3-cone determinant `det(H_{01}) * det(H_2)`. -/
def threeCone2Ham (v kx w2 r c s : ℤ) : Matrix (Fin 2) (Fin 2) GaussianInt :=
  blochWireMatrixHomog v kx w2 (-w2) r c s
def threeConeDet6 (v kx w0 w1 w2 m r c s : ℤ) : GaussianInt :=
  (threeCone01Ham v kx w0 w1 m r c s).det * (threeCone2Ham v kx w2 r c s).det

theorem threeCone01Ham_hermitian (v kx w0 w1 m r c s : ℤ) :
    (threeCone01Ham v kx w0 w1 m r c s)ᴴ = threeCone01Ham v kx w0 w1 m r c s := by
  simp only [threeCone01Ham, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Matrix.conjTranspose_conjTranspose]
  have h1 : star ({ re := v * kx, im := 0 } : GaussianInt) = { re := v * kx, im := 0 } := by ext <;> simp
  have h2 : star ({ re := -(v * kx), im := 0 } : GaussianInt) = { re := -(v * kx), im := 0 } := by ext <;> simp
  rw [h1, h2]

theorem threeCone01Ham_sq_equal (v kx w m r c s : ℤ) :
    threeCone01Ham v kx w w m r c s * threeCone01Ham v kx w w m r c s =
      (((v * kx) ^ 2 + w ^ 2 * ((r - c) ^ 2 + s ^ 2) + m ^ 2 : ℤ) : GaussianInt) •
        (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) GaussianInt) := by
  let c0 : GaussianInt := (((v * kx) ^ 2 + w ^ 2 * ((r - c) ^ 2 + s ^ 2) + m ^ 2 : ℤ) : GaussianInt)
  have hrhs : c0 • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) GaussianInt) =
      Matrix.fromBlocks (c0 • (1 : Matrix (Fin 2) (Fin 2) GaussianInt)) 0 0
        (c0 • (1 : Matrix (Fin 2) (Fin 2) GaussianInt)) := by
    ext i j <;> cases i <;> cases j <;> simp [Matrix.one_apply]
  simp only [threeCone01Ham, Matrix.fromBlocks_multiply]
  change _ = c0 • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) GaussianInt)
  rw [hrhs]
  congr 1
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [c0, threeCone01BlockB, coneHopOffDiag, Matrix.vecMul, dotProduct,
        Matrix.conjTranspose_apply, Fin.sum_univ_two, -Int.cast_add, -Int.cast_mul,
        -Int.cast_pow, -Int.cast_sub] <;> ring
  · rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, ← add_smul]
    have hz : ({ re := v * kx, im := 0 } : GaussianInt) + { re := -(v * kx), im := 0 } = 0 := by
      ext <;> simp
    rw [hz, zero_smul]
  · rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, ← add_smul]
    have hz : ({ re := v * kx, im := 0 } : GaussianInt) + { re := -(v * kx), im := 0 } = 0 := by
      ext <;> simp
    rw [hz, zero_smul]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [c0, threeCone01BlockB, coneHopOffDiag, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fin.sum_univ_two, -Int.cast_add, -Int.cast_mul,
        -Int.cast_pow, -Int.cast_sub] <;> ring

/-- Exact closed-form `4×4` determinant of `H_{01}` via `det_fromBlocks_scalar_diag`. -/
theorem threeCone01Ham_det_general (v kx w0 w1 m r c s : ℤ) :
    let k := v * kx
    let D := (r - c) ^ 2 + s ^ 2
    (threeCone01Ham v kx w0 w1 m r c s).det =
      ((k ^ 4 + k ^ 2 * ((w0 ^ 2 + w1 ^ 2) * D + 2 * m ^ 2) + (w0 * w1 * D + m ^ 2) ^ 2 : ℤ) :
        GaussianInt) := by
  simp only [threeCone01Ham]
  rw [det_fromBlocks_scalar_diag, Matrix.det_fin_two]
  ext <;>
    simp [threeCone01BlockB, coneHopOffDiag, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, -Int.cast_add, -Int.cast_mul, -Int.cast_pow, -Int.cast_sub] <;> ring

theorem threeCone01Ham_det_equal (v kx w m r c s : ℤ) :
    (threeCone01Ham v kx w w m r c s).det =
      ((((v * kx) ^ 2 + w ^ 2 * ((r - c) ^ 2 + s ^ 2) + m ^ 2) ^ 2 : ℤ) : GaussianInt) := by
  rw [threeCone01Ham_det_general]
  ext <;> simp [-Int.cast_add, -Int.cast_mul, -Int.cast_pow, -Int.cast_sub]
  ring

theorem threeCone2Ham_det (v kx w2 r c s : ℤ) :
    (threeCone2Ham v kx w2 r c s).det =
      ((-((v * kx) ^ 2 + w2 ^ 2 * ((r - c) ^ 2 + s ^ 2)) : ℤ) : GaussianInt) := by
  rw [threeCone2Ham, blochWireMatrixHomog, Matrix.det_fin_two_of]
  ext <;> simp [-Int.cast_add, -Int.cast_mul, -Int.cast_pow, -Int.cast_sub, -Int.cast_neg] <;> ring

theorem threeCone01Ham_charpoly_equal (lam v kx w m r c s : ℤ) :
    (((lam : GaussianInt) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) GaussianInt)) -
        threeCone01Ham v kx w w m r c s).det =
      (((lam ^ 2 - ((v * kx) ^ 2 + w ^ 2 * ((r - c) ^ 2 + s ^ 2) + m ^ 2)) ^ 2 : ℤ) : GaussianInt) := by
  have hsub :
      ((lam : GaussianInt) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) GaussianInt)) -
          threeCone01Ham v kx w w m r c s =
      Matrix.fromBlocks
        ((⟨lam - v * kx, 0⟩ : GaussianInt) • (1 : Matrix (Fin 2) (Fin 2) GaussianInt))
        (-threeCone01BlockB w w m r c s) (-(threeCone01BlockB w w m r c s)ᴴ)
        ((⟨lam + v * kx, 0⟩ : GaussianInt) • (1 : Matrix (Fin 2) (Fin 2) GaussianInt)) := by
    ext i j <;> cases i <;> cases j <;> simp [threeCone01Ham, Matrix.one_apply] <;>
      split_ifs <;> simp
  rw [hsub, det_fromBlocks_scalar_diag, Matrix.det_fin_two]
  ext <;>
    simp [threeCone01BlockB, coneHopOffDiag, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, -Int.cast_add, -Int.cast_mul, -Int.cast_pow, -Int.cast_sub] <;> ring

theorem threeCone2Ham_charpoly (lam v kx w2 r c s : ℤ) :
    (((lam : GaussianInt) • (1 : Matrix (Fin 2) (Fin 2) GaussianInt)) -
        threeCone2Ham v kx w2 r c s).det =
      ((lam ^ 2 - ((v * kx) ^ 2 + w2 ^ 2 * ((r - c) ^ 2 + s ^ 2)) : ℤ) : GaussianInt) := by
  rw [Matrix.det_fin_two]
  ext <;>
    simp [threeCone2Ham, blochWireMatrixHomog, -Int.cast_add, -Int.cast_mul, -Int.cast_pow,
      -Int.cast_sub] <;> ring

theorem threeCone_mass_gapping_and_zero_mode (v kx w0 w1 w2 m r c s : ℤ)
    (hm : m ≠ 0) (hw01 : 0 ≤ w0 * w1) :
    (0 < (threeCone01Ham v kx w0 w1 m r c s).det.re) ∧
    (m ^ 4 ≤ (threeCone01Ham v kx w0 w1 m r c s).det.re) ∧
    (threeConeDet6 v 0 w0 w1 w2 m r r 0 = 0) ∧
    ((threeCone01Ham v 0 w0 w1 m r r 0).det = ((m ^ 4 : ℤ) : GaussianInt)) := by
  have hD : 0 ≤ (r - c) ^ 2 + s ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hm2 : 0 < m ^ 2 := sq_pos_of_ne_zero hm
  have hm4 : 0 < m ^ 4 := by
    have : m ^ 4 = (m ^ 2) ^ 2 := by ring
    rw [this]; exact sq_pos_of_ne_zero (ne_of_gt hm2)
  have hre : (threeCone01Ham v kx w0 w1 m r c s).det.re =
      (v * kx) ^ 4 + (v * kx) ^ 2 * ((w0 ^ 2 + w1 ^ 2) * ((r - c) ^ 2 + s ^ 2) + 2 * m ^ 2) +
        (w0 * w1 * ((r - c) ^ 2 + s ^ 2) + m ^ 2) ^ 2 := by
    rw [threeCone01Ham_det_general]; rfl
  have hk4 : 0 ≤ (v * kx) ^ 4 := by
    have : (v * kx) ^ 4 = ((v * kx) ^ 2) ^ 2 := by ring
    rw [this]; exact sq_nonneg _
  have hmid : 0 ≤ (v * kx) ^ 2 * ((w0 ^ 2 + w1 ^ 2) * ((r - c) ^ 2 + s ^ 2) + 2 * m ^ 2) :=
    mul_nonneg (sq_nonneg _) (by nlinarith [sq_nonneg w0, sq_nonneg w1])
  have hterm : m ^ 4 ≤ (w0 * w1 * ((r - c) ^ 2 + s ^ 2) + m ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (w0 * w1 * ((r - c) ^ 2 + s ^ 2)), mul_nonneg hw01 hD]
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · simp [threeConeDet6, threeCone2Ham_det]
  · rw [threeCone01Ham_det_general]
    ext <;> simp [-Int.cast_add, -Int.cast_mul, -Int.cast_pow, -Int.cast_sub]
    ring

theorem threeCone2_unique_dirac_node (v kx w2 r c s : ℤ)
    (hv : v ≠ 0) (hw2 : w2 ≠ 0) (_hr : r ≠ 0) (_hcircle : c ^ 2 + s ^ 2 = r ^ 2) :
    (threeCone2Ham v kx w2 r c s).det = 0 ↔ (kx = 0 ∧ c = r ∧ s = 0) := by
  rw [threeCone2Ham_det]
  constructor
  · intro h0
    have hre : (v * kx) ^ 2 + (w2 * (r - c)) ^ 2 + (w2 * s) ^ 2 = 0 := by
      have h := congrArg Zsqrtd.re h0
      simp [-Int.cast_add, -Int.cast_mul, -Int.cast_pow, -Int.cast_sub, -Int.cast_neg] at h
      linarith
    have hx : (v * kx) ^ 2 = 0 := by nlinarith [sq_nonneg (v * kx), sq_nonneg (w2 * (r - c)), sq_nonneg (w2 * s)]
    have hy : (w2 * (r - c)) ^ 2 = 0 := by nlinarith [sq_nonneg (v * kx), sq_nonneg (w2 * (r - c)), sq_nonneg (w2 * s)]
    have hz : (w2 * s) ^ 2 = 0 := by nlinarith [sq_nonneg (v * kx), sq_nonneg (w2 * (r - c)), sq_nonneg (w2 * s)]
    exact ⟨(mul_eq_zero.mp (sq_eq_zero_iff.mp hx)).resolve_left hv,
      by have := (mul_eq_zero.mp (sq_eq_zero_iff.mp hy)).resolve_left hw2; linarith,
      (mul_eq_zero.mp (sq_eq_zero_iff.mp hz)).resolve_left hw2⟩
  · rintro ⟨rfl, rfl, rfl⟩; simp

/-! ### 3. Fu–Kane ↔ `T`-Pfaffian `D^T` Operator Duality (MAM App. 4 Eqs. (63)–(65)) -/

def fkPairOp (y k : ℕ) : ℤ :=
  if k = 3 * y then -1 else if k = 3 * y + 1 then -1
  else if k = 3 * y + 3 then 1 else if k = 3 * y + 4 then 1 else 0

def fkProximityOp (y k : ℕ) : ℤ :=
  if k = 3 * y + 2 then -1 else if k = 3 * y + 3 then 1
  else if k = 3 * y + 4 then 1 else if k = 3 * y + 5 then -1 else 0

def fkCone2HopOp (y k : ℕ) : ℤ :=
  if k = 3 * y + 2 then -1 else if k = 3 * y + 5 then 1 else 0

/-- Electronic `T`-Pfaffian pairing operator (correcting MAM App. 4 Eq. (63): `3y+2` exponent `-4`). -/
def tPfaffianPairTarget (y z : ℕ) : ℤ :=
  paritySign y * (if z = 3 * y then 1 else if z = 3 * y + 1 then -3
    else if z = 3 * y + 2 then 4 else if z = 3 * y + 3 then -3
    else if z = 3 * y + 4 then 1 else 0)

/-- Electronic `T`-Pfaffian dressed cone-2 hopping operator (MAM App. 4 Eq. (65)). -/
def tPfaffianCone2HopTarget (y z : ℕ) : ℤ :=
  paritySign y * (if z = 3 * y + 2 then 1 else if z = 3 * y + 3 then -2
    else if z = 3 * y + 4 then 2 else if z = 3 * y + 5 then -1 else 0)

private theorem sum_range_four_pts (n i0 i1 i2 i3 : ℕ) (c0 c1 c2 c3 : ℤ) (g : ℕ → ℤ)
    (hi0 : i0 < n) (hi1 : i1 < n) (hi2 : i2 < n) (hi3 : i3 < n)
    (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h03 : i0 ≠ i3)
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3) :
    ∑ k ∈ Finset.range n,
      (if k = i0 then c0 else if k = i1 then c1 else if k = i2 then c2 else if k = i3 then c3 else 0) * g k =
      c0 * g i0 + c1 * g i1 + c2 * g i2 + c3 * g i3 := by
  have hrew : ∀ k ∈ Finset.range n,
      (if k = i0 then c0 else if k = i1 then c1 else if k = i2 then c2 else if k = i3 then c3 else 0) * g k =
        (if k = i0 then c0 * g i0 else 0) + (if k = i1 then c1 * g i1 else 0) +
        (if k = i2 then c2 * g i2 else 0) + (if k = i3 then c3 * g i3 else 0) := by
    intro k _
    by_cases h0 : k = i0
    · subst h0; simp [h01, h02, h03]
    · by_cases h1 : k = i1
      · subst h1; simp [h0, h12, h13]
      · by_cases h2 : k = i2
        · subst h2; simp [h0, h1, h23]
        · by_cases h3 : k = i3
          · subst h3; simp [h0, h1, h2]
          · simp [h0, h1, h2, h3]
  rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_ite_eq' _ i0, Finset.sum_ite_eq' _ i1,
    Finset.sum_ite_eq' _ i2, Finset.sum_ite_eq' _ i3]
  simp [Finset.mem_range.mpr hi0, Finset.mem_range.mpr hi1,
    Finset.mem_range.mpr hi2, Finset.mem_range.mpr hi3]

private theorem sum_range_two_pts (n i0 i1 : ℕ) (c0 c1 : ℤ) (g : ℕ → ℤ)
    (hi0 : i0 < n) (hi1 : i1 < n) (h01 : i0 ≠ i1) :
    ∑ k ∈ Finset.range n, (if k = i0 then c0 else if k = i1 then c1 else 0) * g k =
      c0 * g i0 + c1 * g i1 := by
  have hrew : ∀ k ∈ Finset.range n,
      (if k = i0 then c0 else if k = i1 then c1 else 0) * g k =
        (if k = i0 then c0 * g i0 else 0) + (if k = i1 then c1 * g i1 else 0) := by
    intro k _
    by_cases h0 : k = i0
    · subst h0; simp [h01]
    · by_cases h1 : k = i1
      · subst h1; simp [h0]
      · simp [h0, h1]
  rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib,
    Finset.sum_ite_eq' _ i0, Finset.sum_ite_eq' _ i1]
  simp [Finset.mem_range.mpr hi0, Finset.mem_range.mpr hi1]

private theorem skewSign_eval_lt {a b : ℕ} (h : a < b) : skewSignEntry a b = -1 := by
  unfold skewSignEntry; simp [show a ≠ b by omega, show ¬ (b < a) by omega]

private theorem skewSign_eval_gt {a b : ℕ} (h : b < a) : skewSignEntry a b = 1 := by
  unfold skewSignEntry; simp [show a ≠ b by omega, h]

theorem fkPairOp_duality_exact (n y z : ℕ) (hn : 3 * y + 4 < n) :
    dualityTransposeApply n (fkPairOp y) z = tPfaffianPairTarget y z := by
  simp only [dualityTransposeApply, fkPairOp]
  rw [sum_range_four_pts n (3 * y) (3 * y + 1) (3 * y + 3) (3 * y + 4) (-1) (-1) 1 1
    (fun k => dualityEntry k z) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have hfac : -1 * dualityEntry (3 * y) z + -1 * dualityEntry (3 * y + 1) z +
      1 * dualityEntry (3 * y + 3) z + 1 * dualityEntry (3 * y + 4) z =
      (-skewSignEntry (3 * y) z - skewSignEntry (3 * y + 1) z +
        skewSignEntry (3 * y + 3) z + skewSignEntry (3 * y + 4) z) * paritySign z := by
    simp only [dualityEntry]; ring
  rw [hfac]; unfold tPfaffianPairTarget
  have hcases : z < 3 * y ∨ z = 3 * y ∨ z = 3 * y + 1 ∨ z = 3 * y + 2 ∨
      z = 3 * y + 3 ∨ z = 3 * y + 4 ∨ 3 * y + 4 < z := by omega
  rcases hcases with h | rfl | rfl | rfl | rfl | rfl | h
  · rw [skewSign_eval_gt h, skewSign_eval_gt (by omega), skewSign_eval_gt (by omega),
      skewSign_eval_gt (by omega)]
    simp [show z ≠ 3 * y by omega, show z ≠ 3 * y + 1 by omega, show z ≠ 3 * y + 2 by omega,
      show z ≠ 3 * y + 3 by omega, show z ≠ 3 * y + 4 by omega]
  · rw [skewSignEntry_diag, skewSign_eval_gt (by omega), skewSign_eval_gt (by omega),
      skewSign_eval_gt (by omega)]
    simp [paritySign]; split_ifs <;> omega
  · rw [skewSign_eval_lt (by omega), skewSignEntry_diag, skewSign_eval_gt (by omega),
      skewSign_eval_gt (by omega)]
    simp [paritySign]; split_ifs <;> omega
  · rw [skewSign_eval_lt (by omega), skewSign_eval_lt (by omega), skewSign_eval_gt (by omega),
      skewSign_eval_gt (by omega)]
    simp [paritySign]; split_ifs <;> omega
  · rw [skewSign_eval_lt (by omega), skewSign_eval_lt (by omega), skewSignEntry_diag,
      skewSign_eval_gt (by omega)]
    simp [paritySign]; split_ifs <;> omega
  · rw [skewSign_eval_lt (by omega), skewSign_eval_lt (by omega), skewSign_eval_lt (by omega),
      skewSignEntry_diag]
    simp [paritySign]; split_ifs <;> omega
  · rw [skewSign_eval_lt (by omega), skewSign_eval_lt (by omega), skewSign_eval_lt (by omega),
      skewSign_eval_lt h]
    simp [show z ≠ 3 * y by omega, show z ≠ 3 * y + 1 by omega, show z ≠ 3 * y + 2 by omega,
      show z ≠ 3 * y + 3 by omega, show z ≠ 3 * y + 4 by omega]

theorem fkProximityOp_duality_exact (n y z : ℕ) (hn : 3 * y + 5 < n) :
    dualityTransposeApply n (fkProximityOp y) z = -paritySign y * fkProximityOp y z := by
  simp only [dualityTransposeApply, fkProximityOp]
  rw [sum_range_four_pts n (3 * y + 2) (3 * y + 3) (3 * y + 4) (3 * y + 5) (-1) 1 1 (-1)
    (fun k => dualityEntry k z) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have hfac : -1 * dualityEntry (3 * y + 2) z + 1 * dualityEntry (3 * y + 3) z +
      1 * dualityEntry (3 * y + 4) z + -1 * dualityEntry (3 * y + 5) z =
      (-skewSignEntry (3 * y + 2) z + skewSignEntry (3 * y + 3) z +
        skewSignEntry (3 * y + 4) z - skewSignEntry (3 * y + 5) z) * paritySign z := by
    simp only [dualityEntry]; ring
  rw [hfac]
  have hcases : z < 3 * y + 2 ∨ z = 3 * y + 2 ∨ z = 3 * y + 3 ∨ z = 3 * y + 4 ∨
      z = 3 * y + 5 ∨ 3 * y + 5 < z := by omega
  rcases hcases with h | rfl | rfl | rfl | rfl | h
  · rw [skewSign_eval_gt h, skewSign_eval_gt (by omega), skewSign_eval_gt (by omega),
      skewSign_eval_gt (by omega)]
    simp [show z ≠ 3 * y + 2 by omega, show z ≠ 3 * y + 3 by omega, show z ≠ 3 * y + 4 by omega,
      show z ≠ 3 * y + 5 by omega]
  · rw [skewSignEntry_diag, skewSign_eval_gt (by omega), skewSign_eval_gt (by omega),
      skewSign_eval_gt (by omega)]
    simp [paritySign]; split_ifs <;> omega
  · rw [skewSign_eval_lt (by omega), skewSignEntry_diag, skewSign_eval_gt (by omega),
      skewSign_eval_gt (by omega)]
    simp [paritySign]; split_ifs <;> omega
  · rw [skewSign_eval_lt (by omega), skewSign_eval_lt (by omega), skewSignEntry_diag,
      skewSign_eval_gt (by omega)]
    simp [paritySign]; split_ifs <;> omega
  · rw [skewSign_eval_lt (by omega), skewSign_eval_lt (by omega), skewSign_eval_lt (by omega),
      skewSignEntry_diag]
    simp [paritySign]; split_ifs <;> omega
  · rw [skewSign_eval_lt (by omega), skewSign_eval_lt (by omega), skewSign_eval_lt (by omega),
      skewSign_eval_lt h]
    simp [show z ≠ 3 * y + 2 by omega, show z ≠ 3 * y + 3 by omega, show z ≠ 3 * y + 4 by omega,
      show z ≠ 3 * y + 5 by omega]

theorem fkCone2HopOp_duality_exact (n y z : ℕ) (hn : 3 * y + 5 < n) :
    dualityTransposeApply n (fkCone2HopOp y) z = tPfaffianCone2HopTarget y z := by
  simp only [dualityTransposeApply, fkCone2HopOp]
  rw [sum_range_two_pts n (3 * y + 2) (3 * y + 5) (-1) 1 (fun k => dualityEntry k z)
    (by omega) (by omega) (by omega)]
  unfold tPfaffianCone2HopTarget dualityEntry skewSignEntry paritySign
  split_ifs <;> omega

theorem tPfaffian_operators_charge_and_parity (m y : ℕ) (h : 3 * y + 5 < 2 * m) :
    (∑ k ∈ Finset.range (2 * m), fkPairOp y k = 0 ∧
     ∑ z ∈ Finset.range (2 * m), dualityTransposeApply (2 * m) (fkPairOp y) z = 0) ∧
    (∑ k ∈ Finset.range (2 * m), fkProximityOp y k = 0 ∧
     ∑ z ∈ Finset.range (2 * m), dualityTransposeApply (2 * m) (fkProximityOp y) z = 0) ∧
    (∑ k ∈ Finset.range (2 * m), fkCone2HopOp y k = 0 ∧
     ∑ z ∈ Finset.range (2 * m), dualityTransposeApply (2 * m) (fkCone2HopOp y) z = 0) := by
  have hpair : ∑ k ∈ Finset.range (2 * m), fkPairOp y k = 0 := by
    simpa [fkPairOp] using sum_range_four_pts (2 * m) (3 * y) (3 * y + 1) (3 * y + 3) (3 * y + 4)
      (-1) (-1) 1 1 (fun _ => (1 : ℤ)) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hprox : ∑ k ∈ Finset.range (2 * m), fkProximityOp y k = 0 := by
    simpa [fkProximityOp] using sum_range_four_pts (2 * m) (3 * y + 2) (3 * y + 3) (3 * y + 4) (3 * y + 5)
      (-1) 1 1 (-1) (fun _ => (1 : ℤ)) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hhop : ∑ k ∈ Finset.range (2 * m), fkCone2HopOp y k = 0 := by
    simpa [fkCone2HopOp] using sum_range_two_pts (2 * m) (3 * y + 2) (3 * y + 5) (-1) 1
      (fun _ => (1 : ℤ)) (by omega) (by omega) (by omega)
  exact ⟨⟨hpair, by rw [dualityTranspose_charge_conservation, hpair]⟩,
    ⟨hprox, by rw [dualityTranspose_charge_conservation, hprox]⟩,
    ⟨hhop, by rw [dualityTranspose_charge_conservation, hhop]⟩⟩

end Bosonize.CoupledWire
