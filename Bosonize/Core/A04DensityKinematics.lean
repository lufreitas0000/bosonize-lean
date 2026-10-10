module

public import Bosonize.Core.Ch05Fermions
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# A04 finite density kinematics
Proved finite density kinematics: exact partial shifts, edge terms and CAR Lie lift.
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
    (p,k) ∈ validPairs L m ↔ p.val = k.val+m := by
  simp [validPairs]

/-- Zero transfer is the one-particle identity, including the empty-band case. -/
lemma shift_zero (L : ℕ) :
    shift L 0 = 1 := by
  classical
  ext p k
  simp [shift, Matrix.one_apply, Subtype.ext_iff]

/-- Band diameter is at most L−1, so transfers at least L vanish. -/
lemma shift_vanish (L : ℕ) (m : ℤ) (hm : (L : ℤ) ≤ |m|) :
    shift L m = 0 := by
  classical
  ext p k
  have he : p.val ≠ k.val+m := by
    have hp := p.property
    have hk := k.property
    unfold Ch01.inBandPredicate at hp hk
    by_cases h : 0 ≤ m
    · rw [abs_of_nonneg h] at hm
      omega
    · rw [abs_of_neg (by omega)] at hm
      omega
  simp [shift, he]

/-- The vanishing statement also applies directly to finite filtered sums. -/
lemma valid_pairs_empty (L : ℕ) (m : ℤ) (hm : (L : ℤ) ≤ |m|) :
    validPairs L m = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have he := (mem_valid_pairs L m z.1 z.2).mp hz
  have hs := congrArg (fun A : ShiftMatrix L => A z.1 z.2) (shift_vanish L m hm)
  simp [shift, he] at hs


/-- Matrix adjoint exchanges source and target and reverses the integer transfer. -/
lemma shift_adjoint (L : ℕ) (m : ℤ) :
    (shift L m).conjTranspose = shift L (-m) := by
  classical
  ext p k
  have he : k.val = p.val+m ↔ p.val=k.val+(-m) := by omega
  simp [shift, Matrix.conjTranspose_apply, he]


/-- Exact matrix multiplication includes the intermediate-in-band indicator. -/
lemma shift_mul_entry (L : ℕ) (m n : ℤ) (p k : Ch01.Band L) :
    (shift L m * shift L n) p k = compositionCoefficient L m n p k := by
  unfold compositionCoefficient
  classical
  by_cases hb : Ch01.inBandPredicate L (k.val+n)
  · let q : Ch01.Band L := ⟨k.val+n, hb⟩
    have he (r : Ch01.Band L) : r.val = k.val+n ↔ r=q := by
      constructor
      · intro h; exact Subtype.ext h
      · intro h; subst r; rfl
    simp [shift, Matrix.mul_apply, he, hb, q, add_assoc, add_comm n m]
  · have he (r : Ch01.Band L) : r.val ≠ k.val+n := by
      intro h; exact hb (h ▸ r.property)
    simp [shift, Matrix.mul_apply, he, hb]

/-- Monotone positive transport keeps the intermediate inside the interval whenever both endpoints are inside. -/
lemma shift_mul_nonnegative (L : ℕ) (m n : ℤ) (hm : 0 ≤ m) (hn : 0 ≤ n) :
    shift L m * shift L n = shift L (m+n) := by
  classical
  ext p k
  rw [shift_mul_entry]
  unfold compositionCoefficient
  by_cases he : p.val = k.val+(m+n)
  · have hb : Ch01.inBandPredicate L (k.val+n) := by
      have hp := p.property
      have hk := k.property
      unfold Ch01.inBandPredicate at *
      omega
    simp [shift, he, hb]
  · simp [shift, he]

/-- Negative monotone transport has the same exact interval-composition law. -/
lemma shift_mul_nonpositive (L : ℕ) (m n : ℤ) (hm : m ≤ 0) (hn : n ≤ 0) :
    shift L m * shift L n = shift L (m+n) := by
  classical
  ext p k
  rw [shift_mul_entry]
  unfold compositionCoefficient
  by_cases he : p.val = k.val+(m+n)
  · have hb : Ch01.inBandPredicate L (k.val+n) := by
      have hp := p.property
      have hk := k.property
      unfold Ch01.inBandPredicate at *
      omega
    simp [shift, he, hb]
  · simp [shift, he]

/-- All finite commutator contributions are explicit differences of intermediate-band indicators. -/
lemma shift_commutator_edge (L : ℕ) (m n : ℤ) :
    shift L m * shift L n - shift L n * shift L m = edgeMatrix L m n := by
  ext p k
  simp only [Matrix.sub_apply, shift_mul_entry, edgeMatrix]


/-- A nonzero edge hopping has the expected transfer and exactly one admissible intermediate. -/
lemma edge_support (L : ℕ) (m n : ℤ) (p k : Ch01.Band L) (he : edgeMatrix L m n p k ≠ 0) :
    p.val = k.val+(m+n) ∧ (Ch01.inBandPredicate L (k.val+n) ↔ ¬ Ch01.inBandPredicate L (k.val+m)) := by
  unfold edgeMatrix compositionCoefficient at he
  by_cases hp : p.val=k.val+(m+n)
  · refine ⟨hp, ?_⟩
    by_cases hn : Ch01.inBandPredicate L (k.val+n) <;>
      by_cases hm : Ch01.inBandPredicate L (k.val+m) <;> simp_all [add_comm m n]
  · simp [hp, add_comm n m] at he


/-- The lowering-raising commutator is diagonal, with the bottom-minus-top orientation. -/
lemma opposite_shift_entry (L : ℕ) (m : ℤ) (p k : Ch01.Band L) :
    edgeMatrix L (-m) m p k = if p = k then (if Ch01.inBandPredicate L (k.val+m) then (1:ℂ) else 0) - (if Ch01.inBandPredicate L (k.val-m) then (1:ℂ) else 0) else 0 := by
  classical
  unfold edgeMatrix compositionCoefficient
  by_cases hp : p=k
  · subst p
    simp [sub_eq_add_neg]
  · have hval : p.val ≠ k.val := fun h => hp (Subtype.ext h)
    simp [hp, hval]


/-- A concrete allowed pair witnesses non-vacuity of the partial shift. -/
lemma shift_nonzero (L : ℕ) (m : ℤ) (p k : Ch01.Band L) (hp : p.val = k.val+m) :
    shift L m ≠ 0 := by
  intro hz
  have he := congrArg (fun A : ShiftMatrix L => A p k) hz
  simp [shift, hp] at he


/-- For nonnegative lowering/raising magnitudes the mixed commutator is explicitly
bottom minus top. Both tests use the original signed interval endpoints. -/
lemma mixed_edge_even (h : ℕ) (m n : ℤ) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (p k : Ch01.Band (2*h)) :
    edgeMatrix (2*h) (-m) n p k =
      if p.val = k.val+n-m then
        (if k.val < -(h : ℤ)+1+m then (1 : ℂ) else 0) -
        (if (h : ℤ)-n < k.val then (1 : ℂ) else 0)
      else 0 := by
  have hk := k.property
  unfold Ch01.inBandPredicate at hk
  have htop : Ch01.inBandPredicate (2*h) (k.val+n) ↔ k.val ≤ (h : ℤ)-n := by
    unfold Ch01.inBandPredicate
    push_cast at *
    omega
  have hbottom : Ch01.inBandPredicate (2*h) (k.val+(-m)) ↔ -(h : ℤ)+1+m ≤ k.val := by
    unfold Ch01.inBandPredicate
    push_cast at *
    omega
  have he1 : p.val = k.val+(-m+n) ↔ p.val=k.val+n-m := by omega
  have he2 : p.val = k.val+(n+(-m)) ↔ p.val=k.val+n-m := by omega
  simp only [edgeMatrix, compositionCoefficient, he1, he2, htop, hbottom]
  simp only [← not_lt]
  by_cases he : p.val=k.val+n-m <;>
    by_cases hb : k.val < -(h : ℤ)+1+m <;>
    by_cases ht : (h : ℤ)-n < k.val <;> simp_all <;> split_ifs <;> simp_all <;> omega


/-- A nonzero mixed edge hopping has both source and target in the matching boundary
regions. The two-endpoint information is needed for subsequent Pauli blocking proofs. -/
lemma mixed_edge_support_even (h : ℕ) (m n : ℤ) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (p k : Ch01.Band (2*h)) (he : edgeMatrix (2*h) (-m) n p k ≠ 0) :
    p.val = k.val+n-m ∧
      ((k.val < -(h : ℤ)+1+m ∧ p.val < -(h : ℤ)+1+n) ∨
       ((h : ℤ)-n < k.val ∧ (h : ℤ)-m < p.val)) := by
  rw [mixed_edge_even h m n hm hn p k] at he
  by_cases hp : p.val=k.val+n-m
  · refine ⟨hp, ?_⟩
    by_cases hb : k.val < -(h : ℤ)+1+m
    · left; constructor
      · exact hb
      · omega
    · have ht : (h : ℤ)-n < k.val := by
        by_contra hn
        simp [hp, hb, hn] at he
      right; constructor
      · exact ht
      · omega
  · simp [hp] at he


section SecondQuantization
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Zero coefficients yield the zero operator by linearity. -/
lemma dGamma_zero  :
    dGamma (0 : Matrix ι ι ℂ) = 0 := by
 simp [dGamma]

/-- Second quantization preserves sums of one-particle coefficients. -/
lemma dGamma_add (A B : Matrix ι ι ℂ) :
    dGamma (A+B) = dGamma A+dGamma B := by
 exact (dGammaLinear ι).map_add A B

/-- The coefficient dependence is complex linear. -/
lemma dGamma_smul (a : ℂ) (A : Matrix ι ι ℂ) :
    dGamma (a • A) = a • dGamma A := by
 exact (dGammaLinear ι).map_smul a A

/-- Subtraction is preserved, as needed when lifting edge matrices. -/
lemma dGamma_sub (A B : Matrix ι ι ℂ) :
    dGamma (A-B) = dGamma A-dGamma B := by
 exact (dGammaLinear ι).map_sub A B

/-- Adjoint conjugates coefficients and reverses each CAR bilinear. -/
lemma dGamma_adjoint (A : Matrix ι ι ℂ) :
    LinearMap.adjoint (dGamma A) = dGamma A.conjTranspose := by
 simp only [dGamma, map_sum, map_smulₛₗ, starRingEnd_apply, Ch04.hopping_adjoint,
   Matrix.conjTranspose_apply]
 rw [Finset.sum_comm]

/-- The CAR bilinear identity makes second quantization a linear Lie map. -/
lemma dGamma_commutator (A B : Matrix ι ι ℂ) :
    A02.commutator (dGamma A) (dGamma B) = dGamma (A*B-B*A) := by
 classical
 have hl (f : ι → Module.End ℂ (A02.FockSpace ι)) (X) :
   A02.commutator (∑ i, f i) X = ∑ i, A02.commutator (f i) X := by
   simp [A02.commutator, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
 have hr (f : ι → Module.End ℂ (A02.FockSpace ι)) (X) :
   A02.commutator X (∑ i, f i) = ∑ i, A02.commutator X (f i) := by
   simp [A02.commutator, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
 have hs (a b : ℂ) (X Y : Module.End ℂ (A02.FockSpace ι)) :
   A02.commutator (a • X) (b • Y) = (a*b) • A02.commutator X Y := by
   simp [A02.commutator, smul_smul, smul_sub, mul_comm]
 simp only [dGamma, hl, hr, hs, Ch04.bilinear_commutator, smul_sub, smul_smul]
 simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul,
   Finset.sum_sub_distrib]
 have hf (p k : ι) :
   (∑ q, ∑ l, if k=q then (A p k * B q l) • Ch04.hopping p l else 0) =
   ∑ l, (A p k * B k l) • Ch04.hopping p l := by
   rw [Finset.sum_comm]
   simp
 have hg (p k : ι) :
   (∑ q, ∑ l, if p=l then (A p k * B q l) • Ch04.hopping q k else 0) =
   ∑ q, (A p k * B q p) • Ch04.hopping q k := by
   simp
 simp only [hf, hg, Matrix.sub_apply, Matrix.mul_apply, sub_smul,
   Finset.sum_smul, Finset.sum_sub_distrib]
 apply congrArg₂ (fun X Y : Module.End ℂ (A02.FockSpace ι) => X-Y)
 · apply Finset.sum_congr rfl
   intro p _
   exact Finset.sum_comm
 · calc
     _ = ∑ p, ∑ q, ∑ k, (A p k * B q p) • Ch04.hopping q k := by
       apply Finset.sum_congr rfl
       intro p _
       exact Finset.sum_comm
     _ = ∑ q, ∑ p, ∑ k, (A p k * B q p) • Ch04.hopping q k := Finset.sum_comm
     _ = ∑ q, ∑ k, ∑ p, (A p k * B q p) • Ch04.hopping q k := by
       apply Finset.sum_congr rfl
       intro q _
       exact Finset.sum_comm
     _ = _ := by simp_rw [mul_comm]

/-- The identity matrix lifts to particle number, rather than the Fock identity. -/
lemma dGamma_identity  :
    dGamma (1 : Matrix ι ι ℂ) = Ch04.totalNumber := by
 simp [dGamma, Matrix.one_apply, Ch04.hopping_diagonal, Ch04.totalNumber]

/-- Diagonal matrices lift to occupation-weighted observables. -/
lemma dGamma_diagonal (a : ι → ℂ) :
    dGamma (Matrix.diagonal a) = ∑ k, a k • Ch04.number k := by
 simp [dGamma, Matrix.diagonal_apply, Ch04.hopping_diagonal]

end SecondQuantization
end Bosonize.A04
