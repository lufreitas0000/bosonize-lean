module

public import BosonizeStubs.A02CARHilbert

/-!
# CH04: concrete finite occupation CAR
Phase A: basis-extension operators are complete; every lemma is an unproved review stub.
No budget compression or Wick ordering is introduced.
-/

@[expose] public section

namespace Bosonize.Ch04

open scoped BigOperators ComplexConjugate

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Number of occupied modes strictly preceding i in the chosen total order. -/
def precedingCount (i : ι) (S : A02.Occupation ι) : ℕ := (S.filter (· < i)).card

def fermionSign (i : ι) (S : A02.Occupation ι) : ℂ := (-1 : ℂ) ^ precedingCount i S

noncomputable def creation (i : ι) : Module.End ℂ (A02.FockSpace ι) :=
  A02.extendBasis fun S =>
    if i ∈ S then 0 else fermionSign i S • A02.ket (insert i S)

noncomputable def annihilation (i : ι) : Module.End ℂ (A02.FockSpace ι) :=
  A02.extendBasis fun S =>
    if i ∈ S then fermionSign i S • A02.ket (S.erase i) else 0

noncomputable def number (i : ι) : Module.End ℂ (A02.FockSpace ι) :=
  creation i * annihilation i

noncomputable def totalNumber : Module.End ℂ (A02.FockSpace ι) := ∑ i : ι, number i

/-- Ascending ordered product, since the ambient endomorphism ring is noncommutative. -/
noncomputable def parity : Module.End ℂ (A02.FockSpace ι) :=
  ((Finset.univ : Finset ι).sort (· ≤ ·)).map
    (fun i => 1 - (2 : ℂ) • number i) |>.prod

noncomputable def hopping (i j : ι) : Module.End ℂ (A02.FockSpace ι) :=
  creation i * annihilation j

lemma preceding_count_empty (i : ι) : precedingCount i ∅ = 0 := by sorry

lemma preceding_count_insert (i j : ι) (S : A02.Occupation ι) (hj : j ∉ S) :
    precedingCount i (insert j S) = precedingCount i S + if j < i then 1 else 0 := by sorry

lemma preceding_count_erase (i j : ι) (S : A02.Occupation ι) (hj : j ∈ S) :
    precedingCount i S = precedingCount i (S.erase j) + if j < i then 1 else 0 := by sorry

lemma preceding_count_insert_self (i : ι) (S : A02.Occupation ι) :
    precedingCount i (insert i S) = precedingCount i S := by sorry

lemma preceding_count_erase_self (i : ι) (S : A02.Occupation ι) :
    precedingCount i (S.erase i) = precedingCount i S := by sorry

lemma fermion_sign_empty (i : ι) : fermionSign i ∅ = 1 := by sorry

lemma fermion_sign_ne_zero (i : ι) (S : A02.Occupation ι) : fermionSign i S ≠ 0 := by sorry

lemma fermion_sign_square (i : ι) (S : A02.Occupation ι) :
    fermionSign i S * fermionSign i S = 1 := by sorry

lemma fermion_sign_conj (i : ι) (S : A02.Occupation ι) :
    conj (fermionSign i S) = fermionSign i S := by sorry

lemma fermion_sign_insert_self (i : ι) (S : A02.Occupation ι) :
    fermionSign i (insert i S) = fermionSign i S := by sorry

lemma fermion_sign_erase_self (i : ι) (S : A02.Occupation ι) :
    fermionSign i (S.erase i) = fermionSign i S := by sorry

lemma sign_insert_insert (i j : ι) (S : A02.Occupation ι)
    (hij : i ≠ j) (hi : i ∉ S) (hj : j ∉ S) :
    fermionSign j S * fermionSign i (insert j S) =
      -(fermionSign i S * fermionSign j (insert i S)) := by sorry

lemma sign_erase_erase (i j : ι) (S : A02.Occupation ι)
    (hij : i ≠ j) (hi : i ∈ S) (hj : j ∈ S) :
    fermionSign j S * fermionSign i (S.erase j) =
      -(fermionSign i S * fermionSign j (S.erase i)) := by sorry

lemma sign_insert_erase (i j : ι) (S : A02.Occupation ι)
    (hij : i ≠ j) (hi : i ∉ S) (hj : j ∈ S) :
    fermionSign j S * fermionSign i (S.erase j) =
      -(fermionSign i S * fermionSign j (insert i S)) := by sorry

lemma creation_ket (i : ι) (S : A02.Occupation ι) :
    creation i (A02.ket S) =
      if i ∈ S then 0 else fermionSign i S • A02.ket (insert i S) := by sorry

lemma annihilation_ket (i : ι) (S : A02.Occupation ι) :
    annihilation i (A02.ket S) =
      if i ∈ S then fermionSign i S • A02.ket (S.erase i) else 0 := by sorry

lemma creation_vacuum (i : ι) : creation i (A02.ket ∅) = A02.ket {i} := by sorry

lemma annihilation_vacuum (i : ι) : annihilation i (A02.ket ∅) = 0 := by sorry

lemma creation_vacuum_ne_zero (i : ι) : creation i (A02.ket ∅) ≠ 0 := by sorry

lemma annihilation_singleton (i : ι) : annihilation i (A02.ket {i}) = A02.ket ∅ := by sorry

lemma annihilation_singleton_ne_zero (i : ι) : annihilation i (A02.ket {i}) ≠ 0 := by sorry

lemma creation_square (i : ι) : creation i * creation i = 0 := by sorry

lemma annihilation_square (i : ι) : annihilation i * annihilation i = 0 := by sorry

lemma creation_adjoint_pairing (i : ι) (S T : A02.Occupation ι) :
    inner ℂ (A02.ket S) (annihilation i (A02.ket T)) =
      inner ℂ (creation i (A02.ket S)) (A02.ket T) := by sorry

lemma creation_eq_adjoint (i : ι) : creation i = LinearMap.adjoint (annihilation i) := by sorry

lemma annihilation_eq_adjoint (i : ι) : annihilation i = LinearMap.adjoint (creation i) := by sorry

lemma annihilation_car (i j : ι) : A02.anticommutator (annihilation i) (annihilation j) = 0 := by sorry

lemma creation_car (i j : ι) : A02.anticommutator (creation i) (creation j) = 0 := by sorry

lemma mixed_car (i j : ι) : A02.anticommutator (annihilation i) (creation j) =
    (if i = j then (1 : ℂ) else 0) • (1 : Module.End ℂ (A02.FockSpace ι)) := by sorry

/-- Proposed existence of the concrete representation, not an assumed CAR instance. -/
lemma concrete_car_exists : ∃ R : A02.CAR ι (A02.FockSpace ι),
    R.annihilation = annihilation ∧ R.creation = creation := by sorry

lemma number_ket (i : ι) (S : A02.Occupation ι) :
    number i (A02.ket S) = (if i ∈ S then (1 : ℂ) else 0) • A02.ket S := by sorry

lemma number_idempotent (i : ι) : number i * number i = number i := by sorry

lemma number_adjoint (i : ι) : LinearMap.adjoint (number i) = number i := by sorry

lemma number_commute (i j : ι) : number i * number j = number j * number i := by sorry

lemma total_number_ket (S : A02.Occupation ι) :
    totalNumber (ι := ι) (A02.ket S) = (S.card : ℂ) • A02.ket S := by sorry

lemma total_number_adjoint :
    LinearMap.adjoint (totalNumber (ι := ι)) = totalNumber (ι := ι) := by sorry

lemma parity_ket (S : A02.Occupation ι) :
    parity (ι := ι) (A02.ket S) = (-1 : ℂ) ^ S.card • A02.ket S := by sorry

lemma parity_square : parity (ι := ι) * parity (ι := ι) = 1 := by sorry

lemma parity_adjoint : LinearMap.adjoint (parity (ι := ι)) = parity (ι := ι) := by sorry

lemma parity_vacuum : parity (ι := ι) (A02.ket ∅) = A02.ket ∅ := by sorry

lemma parity_creation (i : ι) : parity (ι := ι) * creation i = -(creation i * parity (ι := ι)) := by sorry

lemma parity_annihilation (i : ι) :
    parity (ι := ι) * annihilation i = -(annihilation i * parity (ι := ι)) := by sorry

lemma bilinear_commutator (a b c d : ι) :
    A02.commutator (hopping a b) (hopping c d) =
      (if b = c then (1 : ℂ) else 0) • hopping a d -
      (if a = d then (1 : ℂ) else 0) • hopping c b := by sorry

lemma number_creation_commutator (i j : ι) : A02.commutator (number i) (creation j) =
    (if i = j then (1 : ℂ) else 0) • creation j := by sorry

lemma number_annihilation_commutator (i j : ι) : A02.commutator (number i) (annihilation j) =
    -(if i = j then (1 : ℂ) else 0) • annihilation j := by sorry

lemma total_number_creation_commutator (i : ι) :
    A02.commutator (totalNumber (ι := ι)) (creation i) = creation i := by sorry

lemma total_number_annihilation_commutator (i : ι) :
    A02.commutator (totalNumber (ι := ι)) (annihilation i) = -annihilation i := by sorry

lemma hopping_ket (i j : ι) (S : A02.Occupation ι) (hij : i ≠ j)
    (hi : i ∉ S) (hj : j ∈ S) :
    hopping i j (A02.ket S) = (fermionSign j S * fermionSign i (S.erase j)) •
      A02.ket (insert i (S.erase j)) := by sorry

lemma hopping_blocked (i j : ι) (S : A02.Occupation ι)
    (h : j ∉ S ∨ (i ≠ j ∧ i ∈ S)) : hopping i j (A02.ket S) = 0 := by sorry

lemma hopping_diagonal (i : ι) : hopping i i = number i := by sorry

lemma hopping_adjoint (i j : ι) : LinearMap.adjoint (hopping i j) = hopping j i := by sorry

end Bosonize.Ch04
