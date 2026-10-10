module

public import Bosonize.Core.Ch05Fermions
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# A04 finite density kinematics
Phase A: complete concrete data and unproved one-sorry targets.
Integer partial shifts do not wrap. Second quantization preserves Lie brackets,
not products. Partitions, scalar budget CCR and Sugawara remain later work.
-/
@[expose] public section
namespace Bosonize.A04
open scoped BigOperators Classical

/-- Matrices on the frozen signed integer band, retaining the positive Nyquist representative. -/
abbrev ShiftMatrix (L : ℕ) := Matrix (Ch01.Band L) (Ch01.Band L) ℂ

/-- Valid source/target pairs for transfer m; equality is in ℤ, never residue addition. -/
def validPairs (L : ℕ) (m : ℤ) : Finset (Ch01.Band L × Ch01.Band L) :=
  Finset.univ.filter (fun z => z.1.val = z.2.val + m)

/-- The partial one-particle shift has unit matrix coefficient precisely for an unwrapped transfer. -/
def shift (L : ℕ) (m : ℤ) : ShiftMatrix L :=
  fun p k => if p.val = k.val + m then 1 else 0

/-- The exact intermediate-band coefficient in T_m T_n. Its indicator is indispensable for mixed signs. -/
def compositionCoefficient (L : ℕ) (m n : ℤ) (p k : Ch01.Band L) : ℂ :=
  if p.val = k.val + (m+n) ∧ Ch01.inBandPredicate L (k.val+n) then 1 else 0

/-- Difference of the two possible intermediate indicators, retaining finite edge hopping contributions. -/
def edgeMatrix (L : ℕ) (m n : ℤ) : ShiftMatrix L :=
  fun p k => compositionCoefficient L m n p k - compositionCoefficient L n m p k

/-- Weighted CAR bilinears on an arbitrary ordered finite mode set, acting on the existing occupation Hilbert space. -/
noncomputable def dGamma {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) : Module.End ℂ (A02.FockSpace ι) :=
  ∑ p, ∑ k, A p k • Ch04.hopping p k

/-- Complex linear second quantization. The following Lie theorem does not imply multiplicativity or unitality. -/
noncomputable def dGammaLinear (ι : Type*) [Fintype ι] [LinearOrder ι] :
    Matrix ι ι ℂ →ₗ[ℂ] Module.End ℂ (A02.FockSpace ι) where
  toFun := dGamma
  map_add' A B := by
    classical
    simp only [dGamma, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a A := by
    classical
    simp only [dGamma, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
      RingHom.id_apply]

/-- Unpack the integer valid-pair predicate without changing carriers. -/
lemma mem_valid_pairs (L : ℕ) (m : ℤ) (p k : Ch01.Band L) :
    (p,k) ∈ validPairs L m ↔ p.val = k.val+m := by sorry

/-- Zero transfer is the one-particle identity, including the empty-band case. -/
lemma shift_zero (L : ℕ) :
    shift L 0 = 1 := by sorry

/-- Band diameter is at most L−1, so transfers at least L vanish. -/
lemma shift_vanish (L : ℕ) (m : ℤ) (hm : (L : ℤ) ≤ |m|) :
    shift L m = 0 := by sorry

/-- The vanishing statement also applies directly to finite filtered sums. -/
lemma valid_pairs_empty (L : ℕ) (m : ℤ) (hm : (L : ℤ) ≤ |m|) :
    validPairs L m = ∅ := by sorry

/-- Matrix adjoint exchanges source and target and reverses the integer transfer. -/
lemma shift_adjoint (L : ℕ) (m : ℤ) :
    (shift L m).conjTranspose = shift L (-m) := by sorry

/-- Exact matrix multiplication includes the intermediate-in-band indicator. -/
lemma shift_mul_entry (L : ℕ) (m n : ℤ) (p k : Ch01.Band L) :
    (shift L m * shift L n) p k = compositionCoefficient L m n p k := by sorry

/-- Monotone positive transport keeps the intermediate inside the interval whenever both endpoints are inside. -/
lemma shift_mul_nonnegative (L : ℕ) (m n : ℤ) (hm : 0 ≤ m) (hn : 0 ≤ n) :
    shift L m * shift L n = shift L (m+n) := by sorry

/-- Negative monotone transport has the same exact interval-composition law. -/
lemma shift_mul_nonpositive (L : ℕ) (m n : ℤ) (hm : m ≤ 0) (hn : n ≤ 0) :
    shift L m * shift L n = shift L (m+n) := by sorry

/-- All finite commutator contributions are explicit differences of intermediate-band indicators. -/
lemma shift_commutator_edge (L : ℕ) (m n : ℤ) :
    shift L m * shift L n - shift L n * shift L m = edgeMatrix L m n := by sorry

/-- A nonzero edge hopping has the expected transfer and exactly one admissible intermediate. -/
lemma edge_support (L : ℕ) (m n : ℤ) (p k : Ch01.Band L) (he : edgeMatrix L m n p k ≠ 0) :
    p.val = k.val+(m+n) ∧ (Ch01.inBandPredicate L (k.val+n) ↔ ¬ Ch01.inBandPredicate L (k.val+m)) := by sorry

/-- The lowering-raising commutator is diagonal, with the bottom-minus-top orientation. -/
lemma opposite_shift_entry (L : ℕ) (m : ℤ) (p k : Ch01.Band L) :
    edgeMatrix L (-m) m p k = if p = k then (if Ch01.inBandPredicate L (k.val+m) then (1:ℂ) else 0) - (if Ch01.inBandPredicate L (k.val-m) then (1:ℂ) else 0) else 0 := by sorry

/-- A concrete allowed pair witnesses non-vacuity of the partial shift. -/
lemma shift_nonzero (L : ℕ) (m : ℤ) (p k : Ch01.Band L) (hp : p.val = k.val+m) :
    shift L m ≠ 0 := by sorry

/-- For nonnegative lowering/raising magnitudes the mixed commutator is explicitly
bottom minus top. Both tests use the original signed interval endpoints. -/
lemma mixed_edge_even (h : ℕ) (m n : ℤ) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (p k : Ch01.Band (2*h)) :
    edgeMatrix (2*h) (-m) n p k =
      if p.val = k.val+n-m then
        (if k.val < -(h : ℤ)+1+m then (1 : ℂ) else 0) -
        (if (h : ℤ)-n < k.val then (1 : ℂ) else 0)
      else 0 := by sorry

/-- A nonzero mixed edge hopping has both source and target in the matching boundary
regions. The two-endpoint information is needed for subsequent Pauli blocking proofs. -/
lemma mixed_edge_support_even (h : ℕ) (m n : ℤ) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (p k : Ch01.Band (2*h)) (he : edgeMatrix (2*h) (-m) n p k ≠ 0) :
    p.val = k.val+n-m ∧
      ((k.val < -(h : ℤ)+1+m ∧ p.val < -(h : ℤ)+1+n) ∨
       ((h : ℤ)-n < k.val ∧ (h : ℤ)-m < p.val)) := by sorry

section SecondQuantization
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Zero coefficients yield the zero operator by linearity. -/
lemma dGamma_zero  :
    dGamma (0 : Matrix ι ι ℂ) = 0 := by sorry

/-- Second quantization preserves sums of one-particle coefficients. -/
lemma dGamma_add (A B : Matrix ι ι ℂ) :
    dGamma (A+B) = dGamma A+dGamma B := by sorry

/-- The coefficient dependence is complex linear. -/
lemma dGamma_smul (a : ℂ) (A : Matrix ι ι ℂ) :
    dGamma (a • A) = a • dGamma A := by sorry

/-- Subtraction is preserved, as needed when lifting edge matrices. -/
lemma dGamma_sub (A B : Matrix ι ι ℂ) :
    dGamma (A-B) = dGamma A-dGamma B := by sorry

/-- Adjoint conjugates coefficients and reverses each CAR bilinear. -/
lemma dGamma_adjoint (A : Matrix ι ι ℂ) :
    LinearMap.adjoint (dGamma A) = dGamma A.conjTranspose := by sorry

/-- The CAR bilinear identity makes second quantization a linear Lie map. -/
lemma dGamma_commutator (A B : Matrix ι ι ℂ) :
    A02.commutator (dGamma A) (dGamma B) = dGamma (A*B-B*A) := by sorry

/-- The identity matrix lifts to particle number, rather than the Fock identity. -/
lemma dGamma_identity  :
    dGamma (1 : Matrix ι ι ℂ) = Ch04.totalNumber := by sorry

/-- Diagonal matrices lift to occupation-weighted observables. -/
lemma dGamma_diagonal (a : ι → ℂ) :
    dGamma (Matrix.diagonal a) = ∑ k, a k • Ch04.number k := by sorry

end SecondQuantization
end Bosonize.A04
