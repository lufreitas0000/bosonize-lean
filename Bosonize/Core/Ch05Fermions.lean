module

public import Bosonize.Core.A01FourierCharacters
public import Bosonize.Core.Ch03Fourier
public import Bosonize.Core.Ch04CARFock

/-!
# Chapter 5: position and momentum fermions
Phase A: complete definitions and one-sorry review stubs.
The Fourier layer works for positive L; physical sea formulas specialize to L = 2*h, h > 0.
-/

@[expose] public section

namespace Bosonize.Ch05

open scoped BigOperators

abbrev FockSpace (L : ℕ) := A02.FockSpace (Ch01.Band L)
abbrev Operators (L : ℕ) := Module.End ℂ (FockSpace L)

noncomputable def momentumAnnihilation (L : ℕ) (k : Ch01.Band L) : Operators L :=
  Ch04.annihilation k

noncomputable def momentumCreation (L : ℕ) (k : Ch01.Band L) : Operators L :=
  Ch04.creation k

noncomputable def momentumNumber (L : ℕ) (k : Ch01.Band L) : Operators L :=
  momentumCreation L k * momentumAnnihilation L k

/-- Positive character kernel for annihilators, with the real unitary normalization. -/
noncomputable def positionAnnihilation (L : ℕ) [NeZero L]
    (x : Ch01.Lattice L) : Operators L :=
  (A01.normalization L : ℂ) • ∑ k : Ch01.Band L,
    A01.bandCharacter L (A01.canonicalRoot L) k x • momentumAnnihilation L k

/-- Ordinary integer negation in the character; no negative-band membership is assumed. -/
noncomputable def positionCreation (L : ℕ) [NeZero L]
    (x : Ch01.Lattice L) : Operators L :=
  (A01.normalization L : ℂ) • ∑ k : Ch01.Band L,
    A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ) • momentumCreation L k

noncomputable def positionNumber (L : ℕ) [NeZero L]
    (x : Ch01.Lattice L) : Operators L :=
  positionCreation L x * positionAnnihilation L x

noncomputable def totalNumber (L : ℕ) : Operators L :=
  ∑ k : Ch01.Band L, momentumNumber L k

/-- Integer spectrum, without clipping negative bare energies. -/
def occupationEnergy (L : ℕ) (S : A02.Occupation (Ch01.Band L)) : ℤ :=
  ∑ k ∈ S, k.val

noncomputable def bareHamiltonian (L : ℕ) : Operators L :=
  ∑ k : Ch01.Band L, (k.val : ℂ) • momentumNumber L k

/-- Fill all nonpositive labels in the actual positive-Nyquist band. -/
def seaConfiguration (L : ℕ) : A02.Occupation (Ch01.Band L) :=
  Finset.univ.filter (fun k => k.val ≤ 0)

def seaEnergy (L : ℕ) : ℤ := occupationEnergy L (seaConfiguration L)

noncomputable def seaKet (L : ℕ) : FockSpace L := A02.ket (seaConfiguration L)

noncomputable def shiftedHamiltonian (L : ℕ) : Operators L :=
  bareHamiltonian L - (seaEnergy L : ℂ) • (1 : Operators L)

noncomputable def parity (L : ℕ) : Operators L := Ch04.parity

section Fourier
variable (L : ℕ) [NeZero L]

lemma position_creation_eq_adjoint (x : Ch01.Lattice L) :
    positionCreation L x = LinearMap.adjoint (positionAnnihilation L x) := by
  simp only [positionCreation, positionAnnihilation, map_smulₛₗ, map_sum, starRingEnd_apply,
    A01.bandCharacter, A01.complex_character_conj L _ (A01.canonical_root_primitive L),
    A01.normalization_conj, momentumCreation, momentumAnnihilation, Ch04.creation_eq_adjoint]

lemma position_annihilation_eq_adjoint (x : Ch01.Lattice L) :
    positionAnnihilation L x = LinearMap.adjoint (positionCreation L x) := by
  rw [position_creation_eq_adjoint, LinearMap.adjoint_adjoint]

lemma position_annihilation_car (x y : Ch01.Lattice L) :
    A02.anticommutator (positionAnnihilation L x) (positionAnnihilation L y) = 0 := by
  have hsum (a b : Ch01.Band L → Operators L) (f g : Ch01.Band L → ℂ) :
      A02.anticommutator (∑ k, f k • a k) (∑ p, g p • b p) =
        ∑ k, ∑ p, (f k * g p) • A02.anticommutator (a k) (b p) := by
    simp only [A02.anticommutator, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
      mul_smul_comm, Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro p hp
    rw [mul_comm (g p) (f k)]
  have hc (k p : Ch01.Band L) : A02.anticommutator (momentumAnnihilation L k) (momentumAnnihilation L p) = 0 := by
    convert Ch04.annihilation_car k p using 1
    all_goals simp [momentumAnnihilation, FockSpace]
  simp only [positionAnnihilation, Finset.smul_sum, smul_smul]
  rw [hsum]
  simp only [hc, smul_zero, Finset.sum_const_zero]

lemma position_creation_car (x y : Ch01.Lattice L) :
    A02.anticommutator (positionCreation L x) (positionCreation L y) = 0 := by
  have hsum (a b : Ch01.Band L → Operators L) (f g : Ch01.Band L → ℂ) :
      A02.anticommutator (∑ k, f k • a k) (∑ p, g p • b p) =
        ∑ k, ∑ p, (f k * g p) • A02.anticommutator (a k) (b p) := by
    simp only [A02.anticommutator, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
      mul_smul_comm, Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro p hp
    rw [mul_comm (g p) (f k)]
  have hc (k p : Ch01.Band L) : A02.anticommutator (momentumCreation L k) (momentumCreation L p) = 0 := by
    convert Ch04.creation_car k p using 1
    all_goals simp [momentumCreation, FockSpace]
  simp only [positionCreation, Finset.smul_sum, smul_smul]
  rw [hsum]
  simp only [hc, smul_zero, Finset.sum_const_zero]

lemma position_mixed_car (x y : Ch01.Lattice L) :
    A02.anticommutator (positionAnnihilation L x) (positionCreation L y) =
      (if x = y then (1 : ℂ) else 0) • (1 : Operators L) := by
  have hsum (a b : Ch01.Band L → Operators L) (f g : Ch01.Band L → ℂ) :
      A02.anticommutator (∑ k, f k • a k) (∑ p, g p • b p) =
        ∑ k, ∑ p, (f k * g p) • A02.anticommutator (a k) (b p) := by
    simp only [A02.anticommutator, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
      mul_smul_comm, Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro p hp
    rw [mul_comm (g p) (f k)]
  have hc (k p : Ch01.Band L) :
      A02.anticommutator (momentumAnnihilation L k) (momentumCreation L p) =
        (if k = p then (1 : ℂ) else 0) • (1 : Operators L) := by
    convert Ch04.mixed_car k p using 1
    all_goals simp [momentumAnnihilation, momentumCreation, FockSpace]
  simp only [positionAnnihilation, positionCreation, Finset.smul_sum, smul_smul]
  rw [hsum]
  simp_rw [hc]
  simp only [ite_smul, smul_ite, zero_smul, smul_zero, one_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hchar (k : Ch01.Band L) :
      A01.bandCharacter L (A01.canonicalRoot L) k x *
        A01.integerCharacter (A01.canonicalRoot L) (-k.val) (y.val : ℤ) =
      A01.integerCharacter (A01.canonicalRoot L) k.val ((x.val : ℤ) - (y.val : ℤ)) := by
    unfold A01.bandCharacter A01.integerCharacter
    rw [← zpow_add₀ (A01.root_ne_zero L _ (A01.canonical_root_primitive L))]
    congr 1
    ring
  have hcoeff (k : Ch01.Band L) :
      ((A01.normalization L : ℂ) * A01.bandCharacter L (A01.canonicalRoot L) k x) *
        ((A01.normalization L : ℂ) * A01.integerCharacter (A01.canonicalRoot L) (-k.val) (y.val : ℤ)) =
      (A01.normalization L : ℂ)^2 *
        A01.integerCharacter (A01.canonicalRoot L) k.val ((x.val : ℤ) - (y.val : ℤ)) := by
    rw [← hchar]
    ring
  simp_rw [hcoeff]
  rw [← Finset.sum_smul, ← Finset.mul_sum,
    A01.dual_character_orthogonality L _ (A01.canonical_root_primitive L)]
  by_cases hxy : x = y
  · simp only [hxy, ite_true]
    rw [mul_comm, A01.normalization_square_complex, one_smul]
  · simp [hxy]


lemma position_car_exists : ∃ R : A02.CAR (Ch01.Lattice L) (FockSpace L),
    R.annihilation = positionAnnihilation L ∧ R.creation = positionCreation L := by
  exact ⟨{ annihilation := positionAnnihilation L
           creation := positionCreation L
           annihilation_car := position_annihilation_car L
           creation_car := position_creation_car L
           mixed_car := position_mixed_car L
           adjoint_compat := position_creation_eq_adjoint L }, rfl, rfl⟩

lemma inverse_annihilation (k : Ch01.Band L) :
    momentumAnnihilation L k = (A01.normalization L : ℂ) •
      ∑ x : Ch01.Lattice L,
        A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ) •
          positionAnnihilation L x := by
  classical
  have he (p : Ch01.Band L) (x : Ch01.Lattice L) :
      A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ) *
        A01.bandCharacter L (A01.canonicalRoot L) p x =
      A01.integerCharacter (A01.canonicalRoot L) (p.val - k.val) (x.val : ℤ) := by
    simp only [A01.integerCharacter, A01.bandCharacter]
    rw [← zpow_add₀ (A01.root_ne_zero L _ (A01.canonical_root_primitive L))]
    congr 1
    ring
  symm
  simp only [positionAnnihilation]
  simp_rw [smul_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hs (p : Ch01.Band L) :
      (∑ x : Ch01.Lattice L,
        ((A01.normalization L : ℂ) * (A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ) *
          (A01.normalization L : ℂ) * A01.bandCharacter L (A01.canonicalRoot L) p x)) •
          momentumAnnihilation L p) =
      ((A01.normalization L : ℂ) * ((A01.normalization L : ℂ) * (if p = k then (L : ℂ) else 0))) • momentumAnnihilation L p := by
    rw [← Finset.sum_smul]
    congr 1
    have hx (x : Ch01.Lattice L) :
        (A01.normalization L : ℂ) * (A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ) *
          (A01.normalization L : ℂ) * A01.bandCharacter L (A01.canonicalRoot L) p x) =
        ((A01.normalization L : ℂ) * (A01.normalization L : ℂ)) * A01.integerCharacter (A01.canonicalRoot L)
          (p.val - k.val) (x.val : ℤ) := by
      rw [← he p x]
      ring
    simp_rw [hx]
    rw [← Finset.mul_sum, A01.character_orthogonality L _ (A01.canonical_root_primitive L)]
    ring
  simp_rw [hs]
  simp only [mul_ite, mul_zero, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hn : (A01.normalization L : ℂ) * ((A01.normalization L : ℂ) * (L : ℂ)) = 1 := by
    calc
      _ = (L : ℂ) * (A01.normalization L : ℂ) ^ 2 := by ring
      _ = 1 := A01.normalization_square_complex L
  rw [hn, one_smul]

lemma inverse_creation (k : Ch01.Band L) :
    momentumCreation L k = (A01.normalization L : ℂ) •
      ∑ x : Ch01.Lattice L,
        A01.bandCharacter L (A01.canonicalRoot L) k x • positionCreation L x := by
  have ha := congrArg LinearMap.adjoint (inverse_annihilation L k)
  have hconj (x : Ch01.Lattice L) :
      star (A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ)) =
        A01.bandCharacter L (A01.canonicalRoot L) k x := by
    rw [A01.complex_character_conj L _ (A01.canonical_root_primitive L)]
    simp [A01.bandCharacter]
  simpa only [momentumAnnihilation, Ch04.creation_eq_adjoint, map_smulₛₗ,
    map_sum, starRingEnd_apply, A01.normalization_conj, hconj,
    ← position_creation_eq_adjoint, momentumCreation] using ha

lemma total_number_position :
    (∑ x : Ch01.Lattice L, positionNumber L x) = totalNumber L := by
  classical
  unfold totalNumber momentumNumber
  simp_rw [inverse_annihilation L]
  simp only [mul_smul_comm, Finset.mul_sum, ← smul_mul_assoc]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp only [positionNumber, positionCreation, smul_mul_assoc, Finset.sum_mul]
  rw [Finset.smul_sum]

lemma position_number_idempotent (x : Ch01.Lattice L) :
    positionNumber L x * positionNumber L x = positionNumber L x := by
  obtain ⟨R, ha, hc⟩ := position_car_exists L
  simpa [A02.AlgebraicCAR.number, ha, hc, positionNumber] using
    A02.car_number_idempotent R.toAlgebraicCAR x

lemma position_number_adjoint (x : Ch01.Lattice L) :
    LinearMap.adjoint (positionNumber L x) = positionNumber L x := by
  change LinearMap.adjoint ((positionCreation L x).comp (positionAnnihilation L x)) = _
  rw [LinearMap.adjoint_comp, ← position_creation_eq_adjoint, ← position_annihilation_eq_adjoint]
  rfl

lemma position_number_commute (x y : Ch01.Lattice L) :
    positionNumber L x * positionNumber L y = positionNumber L y * positionNumber L x := by
  obtain ⟨R, ha, hc⟩ := position_car_exists L
  simpa [A02.AlgebraicCAR.number, ha, hc, positionNumber] using
    A02.car_number_commute R.toAlgebraicCAR x y

lemma position_annihilation_vacuum (x : Ch01.Lattice L) :
    positionAnnihilation L x (A02.ket ∅) = 0 := by
  have hv (k : Ch01.Band L) : momentumAnnihilation L k (A02.ket ∅) = 0 := by
    convert Ch04.annihilation_vacuum k using 1
    all_goals simp [momentumAnnihilation, FockSpace, A02.ket, A02.occupationBasis, A02.occupationONB]
  simp only [positionAnnihilation, LinearMap.smul_apply, LinearMap.sum_apply, hv, smul_zero, Finset.sum_const_zero]

lemma position_creation_vacuum_ne_zero (x : Ch01.Lattice L) :
    positionCreation L x (A02.ket ∅) ≠ 0 := by
  intro h
  have H := congrArg (fun A : Operators L => A (A02.ket ∅)) (position_mixed_car L x x)
  have Hz : A02.ket (∅ : A02.Occupation (Ch01.Band L)) = 0 := by
    simpa [A02.anticommutator, Module.End.mul_apply, h, position_annihilation_vacuum] using H.symm
  exact A02.ket_ne_zero ∅ Hz

lemma parity_position_creation (x : Ch01.Lattice L) :
    parity L * positionCreation L x = -(positionCreation L x * parity L) := by
  simp only [positionCreation, parity, momentumCreation, mul_smul_comm, smul_mul_assoc,
    Finset.mul_sum, Finset.sum_mul, Ch04.parity_creation, smul_neg, Finset.sum_neg_distrib]

lemma parity_position_annihilation (x : Ch01.Lattice L) :
    parity L * positionAnnihilation L x = -(positionAnnihilation L x * parity L) := by
  simp only [positionAnnihilation, parity, momentumAnnihilation, mul_smul_comm, smul_mul_assoc,
    Finset.mul_sum, Finset.sum_mul, Ch04.parity_annihilation, smul_neg, Finset.sum_neg_distrib]

lemma total_number_position_creation_commutator (x : Ch01.Lattice L) :
    A02.commutator (totalNumber L) (positionCreation L x) = positionCreation L x := by
  have hc (k : Ch01.Band L) : A02.commutator (totalNumber L) (momentumCreation L k) = momentumCreation L k := by
    convert Ch04.total_number_creation_commutator k using 1
    all_goals simp [totalNumber, momentumNumber, momentumCreation, momentumAnnihilation, Ch04.totalNumber, Ch04.number, FockSpace]
  simp only [positionCreation, A02.commutator, mul_smul_comm, smul_mul_assoc,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← smul_sub]
  change (A01.normalization L : ℂ) • (∑ k : Ch01.Band L, _ • A02.commutator (totalNumber L) (momentumCreation L k)) = _
  simp_rw [hc]

lemma total_number_position_annihilation_commutator (x : Ch01.Lattice L) :
    A02.commutator (totalNumber L) (positionAnnihilation L x) = -positionAnnihilation L x := by
  have hc (k : Ch01.Band L) : A02.commutator (totalNumber L) (momentumAnnihilation L k) = -momentumAnnihilation L k := by
    convert Ch04.total_number_annihilation_commutator k using 1
    all_goals simp [totalNumber, momentumNumber, momentumCreation, momentumAnnihilation, Ch04.totalNumber, Ch04.number, FockSpace]
  simp only [positionAnnihilation, A02.commutator, mul_smul_comm, smul_mul_assoc,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← smul_sub]
  change (A01.normalization L : ℂ) • (∑ k : Ch01.Band L, _ • A02.commutator (totalNumber L) (momentumAnnihilation L k)) = _
  simp_rw [hc]
  simp only [smul_neg, Finset.sum_neg_distrib]

end Fourier

section Energy
variable (L : ℕ)

lemma total_number_ket (S : A02.Occupation (Ch01.Band L)) :
    totalNumber L (A02.ket S) = (S.card : ℂ) • A02.ket S := by
  convert Ch04.total_number_ket S using 1
  all_goals simp [totalNumber, momentumNumber, momentumCreation, momentumAnnihilation,
    Ch04.totalNumber, Ch04.number, FockSpace, A02.ket, A02.occupationBasis, A02.occupationONB]

lemma bare_hamiltonian_ket (S : A02.Occupation (Ch01.Band L)) :
    bareHamiltonian L (A02.ket S) = (occupationEnergy L S : ℂ) • A02.ket S := by
  classical
  have hn (k : Ch01.Band L) : momentumNumber L k (A02.ket S) =
      (if k ∈ S then (1 : ℂ) else 0) • A02.ket S := by
    convert Ch04.number_ket k S using 1
    all_goals simp [momentumNumber, momentumCreation, momentumAnnihilation,
      Ch04.number, FockSpace, A02.ket, A02.occupationBasis, A02.occupationONB]
  simp only [bareHamiltonian, LinearMap.sum_apply, LinearMap.smul_apply, hn, smul_smul, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_smul]
  congr 1
  simp [occupationEnergy]

lemma shifted_hamiltonian_ket (S : A02.Occupation (Ch01.Band L)) :
    shiftedHamiltonian L (A02.ket S) =
      ((occupationEnergy L S - seaEnergy L : ℤ) : ℂ) • A02.ket S := by
  simp [shiftedHamiltonian, bare_hamiltonian_ket, ← sub_smul]

lemma bare_hamiltonian_adjoint :
    LinearMap.adjoint (bareHamiltonian L) = bareHamiltonian L := by
  have hn (k : Ch01.Band L) : LinearMap.adjoint (momentumNumber L k) = momentumNumber L k := by
    convert Ch04.number_adjoint k using 1
    all_goals simp [momentumNumber, momentumCreation, momentumAnnihilation, Ch04.number, FockSpace]
  simp only [bareHamiltonian, map_sum, map_smulₛₗ, hn, starRingEnd_apply]
  simp

lemma shifted_hamiltonian_adjoint :
    LinearMap.adjoint (shiftedHamiltonian L) = shiftedHamiltonian L := by
  simp only [shiftedHamiltonian, map_sub, bare_hamiltonian_adjoint, map_smulₛₗ]
  simp

lemma bare_creation_commutator (k : Ch01.Band L) :
    A02.commutator (bareHamiltonian L) (momentumCreation L k) =
      (k.val : ℂ) • momentumCreation L k := by
  classical
  have hc (i : Ch01.Band L) : A02.commutator (momentumNumber L i) (momentumCreation L k) =
      (if i = k then (1 : ℂ) else 0) • momentumCreation L k := by
    convert Ch04.number_creation_commutator i k using 1
    all_goals simp [momentumNumber, momentumCreation, momentumAnnihilation, Ch04.number, FockSpace]
  simp only [bareHamiltonian, A02.commutator, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, ← Finset.sum_sub_distrib, ← smul_sub]
  change (∑ i : Ch01.Band L, (i.val : ℂ) • A02.commutator (momentumNumber L i) (momentumCreation L k)) = _
  simp_rw [hc]
  simp

lemma bare_annihilation_commutator (k : Ch01.Band L) :
    A02.commutator (bareHamiltonian L) (momentumAnnihilation L k) =
      (-k.val : ℂ) • momentumAnnihilation L k := by
  classical
  have hc (i : Ch01.Band L) : A02.commutator (momentumNumber L i) (momentumAnnihilation L k) =
      -(if i = k then (1 : ℂ) else 0) • momentumAnnihilation L k := by
    convert Ch04.number_annihilation_commutator i k using 1
    all_goals simp [momentumNumber, momentumCreation, momentumAnnihilation, Ch04.number, FockSpace]
  simp only [bareHamiltonian, A02.commutator, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, ← Finset.sum_sub_distrib, ← smul_sub]
  change (∑ i : Ch01.Band L, (i.val : ℂ) • A02.commutator (momentumNumber L i) (momentumAnnihilation L k)) = _
  simp_rw [hc]
  simp

lemma shifted_creation_commutator (k : Ch01.Band L) :
    A02.commutator (shiftedHamiltonian L) (momentumCreation L k) =
      (k.val : ℂ) • momentumCreation L k := by
  have hs : A02.commutator (shiftedHamiltonian L) (momentumCreation L k) =
      A02.commutator (bareHamiltonian L) (momentumCreation L k) := by
    simp only [shiftedHamiltonian, A02.commutator, sub_mul, mul_sub, smul_mul_assoc,
      mul_smul_comm, one_mul, mul_one]
    abel
  rw [hs, bare_creation_commutator]

lemma shifted_annihilation_commutator (k : Ch01.Band L) :
    A02.commutator (shiftedHamiltonian L) (momentumAnnihilation L k) =
      (-k.val : ℂ) • momentumAnnihilation L k := by
  have hs : A02.commutator (shiftedHamiltonian L) (momentumAnnihilation L k) =
      A02.commutator (bareHamiltonian L) (momentumAnnihilation L k) := by
    simp only [shiftedHamiltonian, A02.commutator, sub_mul, mul_sub, smul_mul_assoc,
      mul_smul_comm, one_mul, mul_one]
    abel
  rw [hs, bare_annihilation_commutator]

lemma sea_ket_ne_zero : seaKet L ≠ 0 := by
  exact A02.ket_ne_zero _

lemma bare_hamiltonian_sea :
    bareHamiltonian L (seaKet L) = (seaEnergy L : ℂ) • seaKet L := by
  exact bare_hamiltonian_ket L (seaConfiguration L)

lemma shifted_hamiltonian_sea : shiftedHamiltonian L (seaKet L) = 0 := by
  simp [seaKet, shifted_hamiltonian_ket, seaEnergy]

end Energy

/-- These physical contracts use exactly the notes' positive-even lattice. -/
lemma sea_card_even (h : ℕ) (hh : 0 < h) : (seaConfiguration (2*h)).card = h := by
  have hmem (k : Ch01.Band (2*h)) : k ∈ seaConfiguration (2*h) ↔ k.val ≤ 0 := by
    simp [seaConfiguration]
  have hin (k : Ch01.Band (2*h)) (hk : k ∈ seaConfiguration (2*h)) :
      (-k.val).toNat ∈ Finset.range h := by
    have hk0 := (hmem k).mp hk
    have hkb := k.property
    simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat] at hkb
    simp only [Finset.mem_range]
    omega
  have hinj (k l : Ch01.Band (2*h)) (hk : k ∈ seaConfiguration (2*h))
      (hl : l ∈ seaConfiguration (2*h)) (he : (-k.val).toNat = (-l.val).toNat) : k = l := by
    have hk0 := (hmem k).mp hk
    have hl0 := (hmem l).mp hl
    apply Subtype.ext
    omega
  have hsurj (n : ℕ) (hn : n ∈ Finset.range h) :
      ∃ k, ∃ hk : k ∈ seaConfiguration (2*h), (-k.val).toNat = n := by
    simp only [Finset.mem_range] at hn
    have hb : Ch01.inBandPredicate (2*h) (-(n : ℤ)) := by
      simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat]
      omega
    refine ⟨⟨-(n : ℤ), hb⟩, ?_, ?_⟩
    · apply (hmem _).mpr
      simp
    · simp
  simpa using Finset.card_bij (fun (k : Ch01.Band (2*h)) _ => (-k.val).toNat) hin (fun k hk l hl => hinj k l hk hl) hsurj

lemma sea_energy_even (h : ℕ) (hh : 0 < h) :
    seaEnergy (2*h) = -((h : ℤ) * ((h : ℤ) - 1) / 2) := by
  have hmem (k : Ch01.Band (2*h)) : k ∈ seaConfiguration (2*h) ↔ k.val ≤ 0 := by
    simp [seaConfiguration]
  have hin (k : Ch01.Band (2*h)) (hk : k ∈ seaConfiguration (2*h)) :
      (-k.val).toNat ∈ Finset.range h := by
    have hk0 := (hmem k).mp hk
    have hkb := k.property
    simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat] at hkb
    simp only [Finset.mem_range]
    omega
  have hinj (k l : Ch01.Band (2*h)) (hk : k ∈ seaConfiguration (2*h))
      (hl : l ∈ seaConfiguration (2*h)) (he : (-k.val).toNat = (-l.val).toNat) : k = l := by
    have hk0 := (hmem k).mp hk
    have hl0 := (hmem l).mp hl
    apply Subtype.ext
    omega
  have hsurj (n : ℕ) (hn : n ∈ Finset.range h) :
      ∃ k, ∃ hk : k ∈ seaConfiguration (2*h), (-k.val).toNat = n := by
    simp only [Finset.mem_range] at hn
    have hb : Ch01.inBandPredicate (2*h) (-(n : ℤ)) := by
      simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat]
      omega
    refine ⟨⟨-(n : ℤ), hb⟩, ?_, ?_⟩
    · apply (hmem _).mpr
      simp
    · simp
  have hsum : seaEnergy (2*h) = ∑ n ∈ Finset.range h, -(n : ℤ) := by
    unfold seaEnergy occupationEnergy
    apply Finset.sum_bij (fun (k : Ch01.Band (2*h)) _ => (-k.val).toNat)
      hin (fun k hk l hl => hinj k l hk hl) hsurj
    intro k hk
    have hk0 := (hmem k).mp hk
    omega
  rw [hsum, Finset.sum_neg_distrib, ← Nat.cast_sum, Finset.sum_range_id,
    Int.natCast_ediv, Nat.cast_mul, Nat.cast_sub hh, Nat.cast_one]
  norm_num

lemma sea_energy_negative (h : ℕ) (hh : 2 ≤ h) : seaEnergy (2*h) < 0 := by
  rw [sea_energy_even h (by omega)]
  have hz : (2 : ℤ) ≤ h := by exact_mod_cast hh
  have hp : 2 ≤ (h : ℤ) * ((h : ℤ) - 1) := by nlinarith
  omega

lemma bare_sea_action_ne_zero (h : ℕ) (hh : 2 ≤ h) :
    bareHamiltonian (2*h) (seaKet (2*h)) ≠ 0 := by
  rw [bare_hamiltonian_sea]
  apply smul_ne_zero
  · exact Int.cast_ne_zero.mpr (ne_of_lt (sea_energy_negative h hh))
  · exact sea_ket_ne_zero _

lemma sea_energy_half_size_one : seaEnergy 2 = 0 := by
  norm_num [seaEnergy, occupationEnergy, seaConfiguration, Ch01.Band,
    Ch01.inBandPredicate, Finset.sum_filter]
  decide

end Bosonize.Ch05
