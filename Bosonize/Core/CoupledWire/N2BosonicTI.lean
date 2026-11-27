module

public import Bosonize.Core.CoupledWire.BlochDiracAndGauge
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# `N = 2` QED₃ ↔ Bosonic TI (`K = σ^x`) & Klein-Factor Exchange Algebra (MAM Sec. VII & Apps. 10–11)

Formalizes the finite-`2m` Klein-factor commutator algebra, `K = σ^x` basis transformation,
and discrete symmetry group `{T, C, I, M, R}` of Mross–Alicea–Motrunich (`arXiv:1510.08455`):
- charge/neutral fermion-to-boson commutators in exact integer units of `i π / 2`;
- universal finite-`2m` closed form `[φ_{s,y}, φ_{s',y'}] = (s s' - 1) δ_{y,y'} (-1)^y sgnX - (2 + s + s') A_{y,y'}`;
- same-species bosonic self-statistics `∈ {-2, 0, +2} (i π)` (`≡ 0 mod 2 π i`), exact skew-symmetry
  preserving `sgn(y - y')` (correcting MAM App. 11's dropped sign), and even full-braid monodromy;
- universal `[CommRing R]` `W^T σ^z W = 2 σ^x` transformation and `K = σ^x` invariance under `T, C, I, M, R`;
- signed integer-lattice duality-kernel symmetry laws and exact `BosonOpState` / `BosonCellState` involutions.
-/

@[expose] public section

namespace Bosonize.CoupledWire

open scoped BigOperators
open Matrix

/-! ### 1. Exact Finite-`2m` Klein-Factor Commutator Algebra (in units of `i π / 2`) -/

/-- Species predicate `σ ∈ {+1, -1}` for `N = 2` QED₃ / bosonic TI duality. -/
def isSpecies (s : ℤ) : Prop := s = 1 ∨ s = -1

/-- Antisymmetric species Levi-Civita symbol `ε_{+-} = 1, ε_{-+} = -1`, `0` otherwise. -/
def speciesEps (s s' : ℤ) : ℤ :=
  if s = 1 ∧ s' = -1 then 1 else if s = -1 ∧ s' = 1 then -1 else 0

/-- Fundamental dual-fermion phase commutator `[tilde_φ_{s,y}(x), tilde_φ_{s',y'}(x')]` in `i π / 2`. -/
def commTildePhiHalfPi (sgnX : ℤ) (y y' : ℕ) (s s' : ℤ) : ℤ :=
  2 * ((if y = y' then paritySign y * ((if s = s' then sgnX else 0) + speciesEps s s') else 0) +
    skewSignEntry y y')

def commTildeC_HalfPi (sgnX : ℤ) (y y' : ℕ) : ℤ :=
  (if y = y' then paritySign y * sgnX else 0) + 2 * skewSignEntry y y'

def commTildeN_HalfPi (sgnX : ℤ) (y y' : ℕ) : ℤ :=
  if y = y' then paritySign y * sgnX else 0

def commTildeCN_HalfPi (y y' : ℕ) : ℤ :=
  if y = y' then -paritySign y else 0

def commTildeNC_HalfPi (y y' : ℕ) : ℤ :=
  if y = y' then paritySign y else 0

def commPhiC_HalfPi (m : ℕ) (sgnX : ℤ) (y y' : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * m), ∑ k ∈ Finset.range (2 * m),
    dualityEntry y j * commTildeC_HalfPi sgnX j k * dualityEntry y' k

def commPhiC_TildeN_HalfPi (m y y' : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (2 * m), dualityEntry y k * commTildeCN_HalfPi k y'

def commTildeN_PhiC_HalfPi (m y y' : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (2 * m), commTildeNC_HalfPi y k * dualityEntry y' k

def commVarphi_HalfPi (m : ℕ) (sgnX : ℤ) (y y' : ℕ) (s s' : ℤ) : ℤ :=
  commPhiC_HalfPi m sgnX y y' +
  s' * commPhiC_TildeN_HalfPi m y y' +
  s * commTildeN_PhiC_HalfPi m y y' +
  s * s' * commTildeN_HalfPi sgnX y y'

/-- Exact bilinear derivation of `tilde_φ_{c/n} = (tilde_φ_+ ± tilde_φ_-) / 2` commutators. -/
theorem commTildeCN_from_fermions (sgnX : ℤ) (y y' : ℕ) :
    (commTildePhiHalfPi sgnX y y' 1 1 + commTildePhiHalfPi sgnX y y' 1 (-1) +
     commTildePhiHalfPi sgnX y y' (-1) 1 + commTildePhiHalfPi sgnX y y' (-1) (-1) =
       4 * commTildeC_HalfPi sgnX y y') ∧
    (commTildePhiHalfPi sgnX y y' 1 1 - commTildePhiHalfPi sgnX y y' 1 (-1) -
     commTildePhiHalfPi sgnX y y' (-1) 1 + commTildePhiHalfPi sgnX y y' (-1) (-1) =
       4 * commTildeN_HalfPi sgnX y y') ∧
    (commTildePhiHalfPi sgnX y y' 1 1 - commTildePhiHalfPi sgnX y y' 1 (-1) +
     commTildePhiHalfPi sgnX y y' (-1) 1 - commTildePhiHalfPi sgnX y y' (-1) (-1) =
       4 * commTildeCN_HalfPi y y') ∧
    (commTildePhiHalfPi sgnX y y' 1 1 + commTildePhiHalfPi sgnX y y' 1 (-1) -
     commTildePhiHalfPi sgnX y y' (-1) 1 - commTildePhiHalfPi sgnX y y' (-1) (-1) =
       4 * commTildeNC_HalfPi y y') := by
  by_cases hy : y = y'
  · subst hy
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [commTildePhiHalfPi, commTildeC_HalfPi, commTildeN_HalfPi, commTildeCN_HalfPi,
        commTildeNC_HalfPi, speciesEps, skewSignEntry_diag, ↓reduceIte,
        show (1 : ℤ) ≠ -1 by decide, show (-1 : ℤ) ≠ 1 by decide, and_self, and_false, false_and] <;>
      ring
  · refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [commTildePhiHalfPi, commTildeC_HalfPi, commTildeN_HalfPi, commTildeCN_HalfPi,
        commTildeNC_HalfPi, hy, ↓reduceIte] <;> ring

theorem commPhiC_HalfPi_eq (m : ℕ) (sgnX : ℤ) (y y' : ℕ) (hy : y < 2 * m) (hy' : y' < 2 * m) :
    commPhiC_HalfPi m sgnX y y' =
      -(if y = y' then paritySign y * sgnX else 0) - 2 * skewSignEntry y y' := by
  simp only [commPhiC_HalfPi, commTildeC_HalfPi]
  have hsplit : ∀ j ∈ Finset.range (2 * m),
      ∑ k ∈ Finset.range (2 * m),
        dualityEntry y j * ((if j = k then paritySign j * sgnX else 0) + 2 * skewSignEntry j k) *
          dualityEntry y' k =
      (dualityEntry y j * paritySign j * dualityEntry y' j) * sgnX +
        2 * (∑ k ∈ Finset.range (2 * m), dualityEntry y j * skewSignEntry j k * dualityEntry y' k) := by
    intro j hj
    have hrew : ∀ k ∈ Finset.range (2 * m),
        dualityEntry y j * ((if j = k then paritySign j * sgnX else 0) + 2 * skewSignEntry j k) *
          dualityEntry y' k =
        (if k = j then (dualityEntry y j * paritySign j * dualityEntry y' j) * sgnX else 0) +
          2 * (dualityEntry y j * skewSignEntry j k * dualityEntry y' k) := by
      intro k _
      by_cases hkj : k = j
      · subst hkj; simp; ring
      · simp [hkj, Ne.symm hkj]; ring
    rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib, Finset.sum_ite_eq' _ j,
      ← Finset.mul_sum]
    simp [Finset.mem_range.mp hj]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.sum_mul,
    duality_chirality_flip_even m y y' hy hy', ← Finset.mul_sum,
    duality_skewSign_flip_even m y y' hy hy']
  by_cases hyy' : y = y'
  · subst hyy'; simp; ring
  · simp [hyy']

theorem commPhiC_TildeN_HalfPi_eq (m y y' : ℕ) (hy' : y' < 2 * m) :
    commPhiC_TildeN_HalfPi m y y' = -skewSignEntry y y' := by
  simp only [commPhiC_TildeN_HalfPi, commTildeCN_HalfPi]
  have hrew : ∀ k ∈ Finset.range (2 * m),
      dualityEntry y k * (if k = y' then -paritySign k else 0) =
        if k = y' then -(dualityEntry y y' * paritySign y') else 0 := by
    intro k _; by_cases hk : k = y'
    · subst hk; simp
    · simp [hk]
  rw [Finset.sum_congr rfl hrew, Finset.sum_ite_eq' _ y']
  simp [Finset.mem_range.mpr hy', dualityEntry_mul_parity_eq_skewSign y y']

theorem commTildeN_PhiC_HalfPi_eq (m y y' : ℕ) (hy : y < 2 * m) :
    commTildeN_PhiC_HalfPi m y y' = -skewSignEntry y y' := by
  simp only [commTildeN_PhiC_HalfPi, commTildeNC_HalfPi]
  have hrew : ∀ k ∈ Finset.range (2 * m),
      (if y = k then paritySign y else 0) * dualityEntry y' k =
        if k = y then dualityEntry y' y * paritySign y else 0 := by
    intro k _; by_cases hk : k = y
    · subst hk; simp [mul_comm]
    · simp [hk, Ne.symm hk]
  rw [Finset.sum_congr rfl hrew, Finset.sum_ite_eq' _ y]
  simp [Finset.mem_range.mpr hy, dualityEntry_mul_parity_eq_skewSign y' y, skewSignEntry_skew y y']

/-- Universal finite-`2m` closed form for `[φ_{s,y}, φ_{s',y'}]` in `i π / 2` units. -/
theorem commVarphi_HalfPi_eq (m : ℕ) (sgnX : ℤ) (y y' : ℕ) (s s' : ℤ)
    (hy : y < 2 * m) (hy' : y' < 2 * m) :
    commVarphi_HalfPi m sgnX y y' s s' =
      (s * s' - 1) * (if y = y' then paritySign y * sgnX else 0) -
        (2 + s + s') * skewSignEntry y y' := by
  simp only [commVarphi_HalfPi, commTildeN_HalfPi]
  rw [commPhiC_HalfPi_eq m sgnX y y' hy hy', commPhiC_TildeN_HalfPi_eq m y y' hy',
    commTildeN_PhiC_HalfPi_eq m y y' hy]
  ring

/-- Exact same-species bosonic self-statistics (`≡ 0 mod 2 i π`) on every even array `N = 2m`. -/
theorem commVarphi_same_species_bosonic (m : ℕ) (sgnX : ℤ) (y y' : ℕ) (s : ℤ)
    (hs : isSpecies s) (hy : y < 2 * m) (hy' : y' < 2 * m) :
    (commVarphi_HalfPi m sgnX y y' s s = 2 * (-(1 + s) * skewSignEntry y y')) ∧
    (y = y' → commVarphi_HalfPi m sgnX y y' s s = 0) ∧
    ((-(1 + s) * skewSignEntry y y') % 2 = 0) ∧
    (-(1 + s) * skewSignEntry y y' = -2 ∨ -(1 + s) * skewSignEntry y y' = 0 ∨
      -(1 + s) * skewSignEntry y y' = 2) := by
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> decide
  have heq : commVarphi_HalfPi m sgnX y y' s s = 2 * (-(1 + s) * skewSignEntry y y') := by
    rw [commVarphi_HalfPi_eq m sgnX y y' s s hy hy', hss]; ring
  refine ⟨heq, fun hyy' => by subst hyy'; rw [heq, skewSignEntry_diag]; simp, ?_, ?_⟩
  · rcases hs with rfl | rfl
    · unfold skewSignEntry; split_ifs <;> decide
    · simp
  · rcases hs with rfl | rfl
    · unfold skewSignEntry; split_ifs <;> simp
    · right; left; simp

/-- Exact opposite-species commutator preserving `sgn(y - y')` (correcting MAM App. 11). -/
theorem commVarphi_opposite_species_exact (m : ℕ) (sgnX : ℤ) (y y' : ℕ) (s : ℤ)
    (hs : isSpecies s) (hy : y < 2 * m) (hy' : y' < 2 * m) :
    (commVarphi_HalfPi m sgnX y y' s (-s) =
      2 * (-(if y = y' then paritySign y * sgnX else 0) - skewSignEntry y y')) ∧
    (y = y' → commVarphi_HalfPi m sgnX y y' s (-s) = 2 * (-paritySign y * sgnX)) ∧
    (y ≠ y' → commVarphi_HalfPi m sgnX y y' s (-s) = 2 * (-skewSignEntry y y')) := by
  have hss : s * (-s) = -1 := by rcases hs with rfl | rfl <;> decide
  have heq : commVarphi_HalfPi m sgnX y y' s (-s) =
      2 * (-(if y = y' then paritySign y * sgnX else 0) - skewSignEntry y y') := by
    rw [commVarphi_HalfPi_eq m sgnX y y' s (-s) hy hy', hss]; ring
  refine ⟨heq, ?_, ?_⟩
  · intro hyy'; subst hyy'; rw [heq, skewSignEntry_diag]; simp
  · intro hne; rw [heq]; simp [hne]

theorem commVarphi_skew (m : ℕ) (sgnX : ℤ) (y y' : ℕ) (s s' : ℤ)
    (hy : y < 2 * m) (hy' : y' < 2 * m) :
    commVarphi_HalfPi m (-sgnX) y' y s' s = -commVarphi_HalfPi m sgnX y y' s s' := by
  rw [commVarphi_HalfPi_eq m (-sgnX) y' y s' s hy' hy,
    commVarphi_HalfPi_eq m sgnX y y' s s' hy hy', skewSignEntry_skew y y']
  by_cases hyy' : y = y'
  · subst hyy'; simp only [↓reduceIte]; ring
  · simp only [hyy', Ne.symm hyy', ↓reduceIte]; ring

theorem commVarphi_opposite_monodromy_even (m y y' : ℕ) (sgnX s : ℤ)
    (hs : isSpecies s) (hy : y < 2 * m) (hy' : y' < 2 * m) :
    let commPi := fun sx a b => -(if a = b then paritySign a * sx else 0) - skewSignEntry a b
    (commVarphi_HalfPi m sgnX y y' s (-s) = 2 * commPi sgnX y y') ∧
    ((commPi 1 y y - commPi (-1) y y) = -2 * paritySign y) ∧
    ((commPi 1 y y - commPi (-1) y y) % 2 = 0) ∧
    (y ≠ y' → (commPi sgnX y y' - commPi sgnX y' y) = -2 * skewSignEntry y y') ∧
    ((commPi sgnX y y' - commPi sgnX y' y) % 2 = 0) ∧
    ((2 * commPi sgnX y y') % 2 = 0) := by
  have hopp := (commVarphi_opposite_species_exact m sgnX y y' s hs hy hy').1
  refine ⟨hopp, by simp [skewSignEntry_diag]; omega, by simp [skewSignEntry_diag]; omega, ?_, ?_, by omega⟩
  · intro hne; simp [hne, Ne.symm hne, skewSignEntry_skew y y']; omega
  · by_cases hyy' : y = y'
    · subst hyy'; simp
    · simp [hyy', Ne.symm hyy', skewSignEntry_skew y y']; omega

/-! ### 2. Universal `K = σ^x` Basis Transform & `N = 2` Discrete Symmetries (`T, C, I, M, R`) -/

/-- Basis transformation matrix `W = [[1, 1], [1, -1]]` over arbitrary `[CommRing R]`. -/
def bosonBasisTransform (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![1, 1; 1, -1]

/-- Universal `K = σ^x` transformation over arbitrary `[CommRing R]` (MAM Sec. VII Eq. (45)). -/
theorem boson_kMatrix_sigmaX_transform (R : Type*) [CommRing R] :
    (bosonBasisTransform R)ᵀ = bosonBasisTransform R ∧
    bosonBasisTransform R * bosonBasisTransform R = (2 : R) • (1 : Matrix (Fin 2) (Fin 2) R) ∧
    (bosonBasisTransform R)ᵀ * pauliZ R * bosonBasisTransform R = (2 : R) • pauliX R ∧
    (bosonBasisTransform R)ᵀ * (-pauliZ R) * bosonBasisTransform R = (-2 : R) • pauliX R ∧
    (pauliX R).det = -1 ∧
    pauliX R * pauliX R = 1 ∧
    (pauliX R 0 0 = 0 ∧ pauliX R 1 1 = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, pauliX_sq R, by simp [pauliX], by simp [pauliX]⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [bosonBasisTransform]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [bosonBasisTransform, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [bosonBasisTransform, pauliZ, pauliX, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [bosonBasisTransform, pauliZ, pauliX, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · rw [pauliX, Matrix.det_fin_two_of]; ring

/-- Universal `K = σ^x` invariance under all five symmetries `T, C, I, M, R` over `[CommRing R]`. -/
theorem n2_symmetries_preserve_kMatrix_sigmaX (R : Type*) [CommRing R] :
    (((-1 : R) * (-1)) • ((pauliX R)ᵀ * pauliX R * pauliX R) = pauliX R) ∧
    (((-1 : R) * (-1)) • ((-pauliX R)ᵀ * pauliX R * (-pauliX R)) = pauliX R) ∧
    (((1 : R) * (-1) * (-1)) • ((1 : Matrix (Fin 2) (Fin 2) R)ᵀ * pauliX R * 1) = pauliX R) ∧
    (((1 : R) * 1 * 1) • ((-pauliX R)ᵀ * pauliX R * (-pauliX R)) = pauliX R) ∧
    (((1 : R) * 1 * 1) • ((pauliX R)ᵀ * pauliX R * pauliX R) = pauliX R) := by
  have hT : (pauliX R)ᵀ = pauliX R := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX]
  have hsq := pauliX_sq R
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [hT, hsq]

/-- Signed integer-lattice wire parity `(-1)^y` for `y : ℤ`. -/
def paritySignInt (y : ℤ) : ℤ := if y % 2 = 0 then 1 else -1

/-- Signed integer-lattice duality kernel `D_{y,z}` for MAM App. 10 Table 1 derivations. -/
def dualityEntryInt (y z : ℤ) : ℤ :=
  if y = z then 0 else (if z < y then 1 else -1) * paritySignInt z

theorem dualityEntryInt_symmetries (y z : ℤ) :
    (dualityEntryInt (y + 1) (z + 1) = -dualityEntryInt y z) ∧
    (dualityEntryInt (-y + 1) (-z + 1) = dualityEntryInt y z) ∧
    (dualityEntryInt (-y) (-z) = -dualityEntryInt y z) := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold dualityEntryInt paritySignInt; split_ifs <;> omega)

/-- Dual-boson operator label `b_{species, y}(x)` (`dag = 1`) or `b^\dag` (`dag = -1`). -/
structure BosonOpState where
  species : ℤ
  dag : ℤ
  y : ℤ
  x : ℤ
  deriving DecidableEq, Repr

/-- 2-wire unit-cell projection `(species, dag, y mod 2, x)`. -/
structure BosonCellState where
  species : ℤ
  dag : ℤ
  sub : Bool
  x : ℤ
  deriving DecidableEq, Repr

def symT (st : BosonOpState) : BosonOpState := ⟨-st.species, -st.dag, st.y + 1, st.x⟩
def symC (st : BosonOpState) : BosonOpState := ⟨-st.species, st.dag, st.y + 1, st.x⟩
def symI (st : BosonOpState) : BosonOpState := ⟨st.species, st.dag, -st.y + 1, -st.x⟩
def symM (st : BosonOpState) : BosonOpState := ⟨-st.species, -st.dag, -st.y, st.x⟩
def symR (st : BosonOpState) : BosonOpState := ⟨-st.species, st.dag, st.y, st.x⟩

def cellT (st : BosonCellState) : BosonCellState := ⟨-st.species, -st.dag, !st.sub, st.x⟩
def cellC (st : BosonCellState) : BosonCellState := ⟨-st.species, st.dag, !st.sub, st.x⟩
def cellI (st : BosonCellState) : BosonCellState := ⟨st.species, st.dag, !st.sub, -st.x⟩
def cellM (st : BosonCellState) : BosonCellState := ⟨-st.species, -st.dag, st.sub, st.x⟩
def cellR (st : BosonCellState) : BosonCellState := ⟨-st.species, st.dag, st.sub, st.x⟩

theorem n2_symmetries_lattice_squares (st : BosonOpState) :
    symI (symI st) = st ∧ symM (symM st) = st ∧ symR (symR st) = st ∧
    symT (symT st) = { st with y := st.y + 2 } ∧ symC (symC st) = { st with y := st.y + 2 } := by
  cases st
  refine ⟨by simp [symI], by simp [symM], by simp [symR],
    by simp [symT]; omega, by simp [symC]; omega⟩

theorem n2_symmetries_cell_involutions (st : BosonCellState) :
    cellT (cellT st) = st ∧ cellC (cellC st) = st ∧ cellI (cellI st) = st ∧
    cellM (cellM st) = st ∧ cellR (cellR st) = st := by
  cases st
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [cellT, cellC, cellI, cellM, cellR]

theorem n2_symmetries_commutation (st : BosonOpState) :
    symR (symT st) = symT (symR st) ∧ symR (symC st) = symC (symR st) ∧
    symR (symI st) = symI (symR st) ∧ symR (symM st) = symM (symR st) ∧
    symT (symC st) = symC (symT st) := by
  cases st
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [symT, symC, symI, symM, symR]

end Bosonize.CoupledWire
