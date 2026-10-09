module

public import Bosonize.Core.A02CARHilbert

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

omit [Fintype ι] in
lemma preceding_count_empty (i : ι) : precedingCount i ∅ = 0 := by
  simp [precedingCount]

omit [Fintype ι] in
lemma preceding_count_insert (i j : ι) (S : A02.Occupation ι) (hj : j ∉ S) :
    precedingCount i (insert j S) = precedingCount i S + if j < i then 1 else 0 := by
  classical
  by_cases hji : j < i
  · simp [precedingCount, Finset.filter_insert, hji, hj]
  · simp [precedingCount, Finset.filter_insert, hji]

omit [Fintype ι] in
lemma preceding_count_erase (i j : ι) (S : A02.Occupation ι) (hj : j ∈ S) :
    precedingCount i S = precedingCount i (S.erase j) + if j < i then 1 else 0 := by
  have h := preceding_count_insert i j (S.erase j) (Finset.notMem_erase j S)
  simpa [Finset.insert_erase hj] using h

omit [Fintype ι] in
lemma preceding_count_insert_self (i : ι) (S : A02.Occupation ι) :
    precedingCount i (insert i S) = precedingCount i S := by
  simp [precedingCount, Finset.filter_insert]

omit [Fintype ι] in
lemma preceding_count_erase_self (i : ι) (S : A02.Occupation ι) :
    precedingCount i (S.erase i) = precedingCount i S := by
  simp [precedingCount, Finset.filter_erase, Finset.erase_eq_of_notMem]

omit [Fintype ι] in
lemma fermion_sign_empty (i : ι) : fermionSign i ∅ = 1 := by
  simp [fermionSign, preceding_count_empty]

omit [Fintype ι] in
lemma fermion_sign_ne_zero (i : ι) (S : A02.Occupation ι) : fermionSign i S ≠ 0 := by
  exact pow_ne_zero _ (by norm_num)

omit [Fintype ι] in
lemma fermion_sign_square (i : ι) (S : A02.Occupation ι) :
    fermionSign i S * fermionSign i S = 1 := by
  unfold fermionSign
  rw [← mul_pow]
  simp

omit [Fintype ι] in
lemma fermion_sign_conj (i : ι) (S : A02.Occupation ι) :
    conj (fermionSign i S) = fermionSign i S := by
  simp [fermionSign]

omit [Fintype ι] in
lemma fermion_sign_insert_self (i : ι) (S : A02.Occupation ι) :
    fermionSign i (insert i S) = fermionSign i S := by
  simp only [fermionSign, preceding_count_insert_self]

omit [Fintype ι] in
lemma fermion_sign_erase_self (i : ι) (S : A02.Occupation ι) :
    fermionSign i (S.erase i) = fermionSign i S := by
  simp only [fermionSign, preceding_count_erase_self]

omit [Fintype ι] in
lemma sign_insert_insert (i j : ι) (S : A02.Occupation ι)
    (hij : i ≠ j) (hi : i ∉ S) (hj : j ∉ S) :
    fermionSign j S * fermionSign i (insert j S) =
      -(fermionSign i S * fermionSign j (insert i S)) := by
  have hci := preceding_count_insert i j S hj
  have hcj := preceding_count_insert j i S hi
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · simp only [fermionSign, hci, hcj, ite_eq_right (not_lt_of_gt hlt), ite_eq_left hlt, add_zero, pow_succ]
    ring
  · simp only [fermionSign, hci, hcj, ite_eq_left hgt, ite_eq_right (not_lt_of_gt hgt), add_zero, pow_succ]
    ring

omit [Fintype ι] in
lemma sign_erase_erase (i j : ι) (S : A02.Occupation ι)
    (hij : i ≠ j) (hi : i ∈ S) (hj : j ∈ S) :
    fermionSign j S * fermionSign i (S.erase j) =
      -(fermionSign i S * fermionSign j (S.erase i)) := by
  have hci := preceding_count_erase i j S hj
  have hcj := preceding_count_erase j i S hi
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · simp only [ite_eq_right (not_lt_of_gt hlt), ite_eq_left hlt, add_zero] at hci hcj
    simp only [fermionSign, hci, hcj, pow_succ]
    ring
  · simp only [ite_eq_left hgt, ite_eq_right (not_lt_of_gt hgt), add_zero] at hci hcj
    simp only [fermionSign, hci, hcj, pow_succ]
    ring

omit [Fintype ι] in
lemma sign_insert_erase (i j : ι) (S : A02.Occupation ι)
    (hij : i ≠ j) (hi : i ∉ S) (hj : j ∈ S) :
    fermionSign j S * fermionSign i (S.erase j) =
      -(fermionSign i S * fermionSign j (insert i S)) := by
  have hci := preceding_count_erase i j S hj
  have hcj := preceding_count_insert j i S hi
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · simp only [ite_eq_right (not_lt_of_gt hlt), ite_eq_left hlt, add_zero] at hci hcj
    simp only [fermionSign, hci, hcj, pow_succ]
    ring
  · simp only [ite_eq_left hgt, ite_eq_right (not_lt_of_gt hgt), add_zero] at hci hcj
    simp only [fermionSign, hci, hcj, pow_succ]
    ring

lemma creation_ket (i : ι) (S : A02.Occupation ι) :
    creation i (A02.ket S) =
      if i ∈ S then 0 else fermionSign i S • A02.ket (insert i S) := by
  exact A02.extend_basis_ket _ S

lemma annihilation_ket (i : ι) (S : A02.Occupation ι) :
    annihilation i (A02.ket S) =
      if i ∈ S then fermionSign i S • A02.ket (S.erase i) else 0 := by
  exact A02.extend_basis_ket _ S

lemma creation_vacuum (i : ι) : creation i (A02.ket ∅) = A02.ket {i} := by
  simp [creation_ket, fermion_sign_empty]

lemma annihilation_vacuum (i : ι) : annihilation i (A02.ket ∅) = 0 := by
  simp [annihilation_ket]

lemma creation_vacuum_ne_zero (i : ι) : creation i (A02.ket ∅) ≠ 0 := by
  rw [creation_vacuum]; exact A02.ket_ne_zero {i}

lemma annihilation_singleton (i : ι) : annihilation i (A02.ket {i}) = A02.ket ∅ := by
  have hs : fermionSign i ({i} : A02.Occupation ι) = 1 := by
    simpa [fermion_sign_empty] using fermion_sign_insert_self i (∅ : A02.Occupation ι)
  simp [annihilation_ket, hs]

lemma annihilation_singleton_ne_zero (i : ι) : annihilation i (A02.ket {i}) ≠ 0 := by
  rw [annihilation_singleton]; exact A02.vacuum_ne_zero

lemma creation_square (i : ι) : creation i * creation i = 0 := by
  apply A02.end_ext_basis
  intro S
  simp only [Module.End.mul_apply, LinearMap.zero_apply, creation_ket]
  by_cases hi : i ∈ S
  · simp [hi]
  · simp [hi, map_smul, creation_ket]

lemma annihilation_square (i : ι) : annihilation i * annihilation i = 0 := by
  apply A02.end_ext_basis
  intro S
  simp only [Module.End.mul_apply, LinearMap.zero_apply, annihilation_ket]
  by_cases hi : i ∈ S
  · simp [hi, map_smul, annihilation_ket]
  · simp [hi]

lemma creation_adjoint_pairing (i : ι) (S T : A02.Occupation ι) :
    inner ℂ (A02.ket S) (annihilation i (A02.ket T)) =
      inner ℂ (creation i (A02.ket S)) (A02.ket T) := by
  simp only [annihilation_ket, creation_ket]
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
  · simp [hiS, hiT, inner_smul_right, A02.ket_inner]
    have hne : S ≠ T.erase i := by intro h; subst S; simp at hiS
    simp [hne]
  · simp [hiS, hiT]
  · simp only [hiS, hiT, ite_true, ite_false, inner_smul_right, inner_smul_left,
      A02.ket_inner, fermion_sign_conj]
    by_cases hST : S = T.erase i
    · subst S
      simp [Finset.insert_erase hiT, fermion_sign_erase_self]
    · have hTS : insert i S ≠ T := by
        intro h
        have he := congrArg (fun U : A02.Occupation ι => U.erase i) h
        exact hST (by simpa [Finset.erase_insert, hiS] using he)
      simp [hST, hTS]
  · simp [hiS, hiT, inner_smul_left, A02.ket_inner]
    have hne : insert i S ≠ T := by intro h; subst T; simp at hiT
    simp [hne]

lemma creation_eq_adjoint (i : ι) : creation i = LinearMap.adjoint (annihilation i) := by
  exact A02.adjoint_of_basis_pairing _ _ (creation_adjoint_pairing i)

lemma annihilation_eq_adjoint (i : ι) : annihilation i = LinearMap.adjoint (creation i) := by
  rw [creation_eq_adjoint, LinearMap.adjoint_adjoint]

lemma annihilation_car (i j : ι) : A02.anticommutator (annihilation i) (annihilation j) = 0 := by
  by_cases hij : i = j
  · subst j; simp [A02.anticommutator, annihilation_square]
  · apply A02.end_ext_basis
    intro S
    simp only [A02.anticommutator, LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply]
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      simp [annihilation_ket, hi, hj, hij, Ne.symm hij, map_smul, smul_smul]
    rw [Finset.erase_right_comm, ← add_smul, sign_erase_erase i j S hij hi hj]
    simp

lemma creation_car (i j : ι) : A02.anticommutator (creation i) (creation j) = 0 := by
  by_cases hij : i = j
  · subst j; simp [A02.anticommutator, creation_square]
  · apply A02.end_ext_basis
    intro S
    simp only [A02.anticommutator, LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply]
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      simp [creation_ket, hi, hj, hij, Ne.symm hij, map_smul, smul_smul]
    rw [Finset.insert_comm, ← add_smul, sign_insert_insert i j S hij hi hj]
    simp

lemma mixed_car (i j : ι) : A02.anticommutator (annihilation i) (creation j) =
    (if i = j then (1 : ℂ) else 0) • (1 : Module.End ℂ (A02.FockSpace ι)) := by
  apply A02.end_ext_basis
  intro S
  simp only [A02.anticommutator, LinearMap.add_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Module.End.one_apply]
  by_cases hij : i = j
  · subst j
    by_cases hi : i ∈ S
    · simp [annihilation_ket, creation_ket, hi, map_smul, smul_smul,
        fermion_sign_erase_self, fermion_sign_square, Finset.insert_erase hi]
    · simp [annihilation_ket, creation_ket, hi, map_smul, smul_smul,
        fermion_sign_insert_self, fermion_sign_square]
  · by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      simp [annihilation_ket, creation_ket, hi, hj, hij, Ne.symm hij, map_smul, smul_smul]
    rw [Finset.erase_insert_of_ne (Ne.symm hij), ← add_smul]
    have hs := sign_insert_erase j i S (Ne.symm hij) hj hi
    rw [hs]
    simp

/-- Proposed existence of the concrete representation, not an assumed CAR instance. -/
lemma concrete_car_exists : ∃ R : A02.CAR ι (A02.FockSpace ι),
    R.annihilation = annihilation ∧ R.creation = creation := by
  exact ⟨{ annihilation := annihilation
           creation := creation
           annihilation_car := annihilation_car
           creation_car := creation_car
           mixed_car := mixed_car
           adjoint_compat := creation_eq_adjoint }, rfl, rfl⟩

lemma number_ket (i : ι) (S : A02.Occupation ι) :
    number i (A02.ket S) = (if i ∈ S then (1 : ℂ) else 0) • A02.ket S := by
  unfold number
  simp only [Module.End.mul_apply, annihilation_ket]
  by_cases hi : i ∈ S
  · simp [hi, map_smul, creation_ket, fermion_sign_erase_self, smul_smul, fermion_sign_square, Finset.insert_erase hi]
  · simp [hi]

lemma number_idempotent (i : ι) : number i * number i = number i := by
  apply A02.end_ext_basis
  intro S
  simp only [Module.End.mul_apply, number_ket, map_smul]
  by_cases hi : i ∈ S <;> simp [hi]

lemma number_adjoint (i : ι) : LinearMap.adjoint (number i) = number i := by
  change LinearMap.adjoint ((creation i).comp (annihilation i)) = (creation i).comp (annihilation i)
  rw [LinearMap.adjoint_comp, ← creation_eq_adjoint, ← annihilation_eq_adjoint]

lemma number_commute (i j : ι) : number i * number j = number j * number i := by
  apply A02.end_ext_basis
  intro S
  simp only [Module.End.mul_apply, number_ket, map_smul, smul_smul]
  congr 1
  exact mul_comm _ _

lemma total_number_ket (S : A02.Occupation ι) :
    totalNumber (ι := ι) (A02.ket S) = (S.card : ℂ) • A02.ket S := by
  simp only [totalNumber, LinearMap.sum_apply, number_ket]
  rw [← Finset.sum_smul]
  congr 1
  simp

lemma total_number_adjoint :
    LinearMap.adjoint (totalNumber (ι := ι)) = totalNumber (ι := ι) := by
  simp [totalNumber, number_adjoint]

lemma parity_ket (S : A02.Occupation ι) :
    parity (ι := ι) (A02.ket S) = (-1 : ℂ) ^ S.card • A02.ket S := by
  have hl : ∀ l : List ι,
      (l.map (fun i => (1 : Module.End ℂ (A02.FockSpace ι)) - (2 : ℂ) • number i)).prod (A02.ket S) =
        (l.map (fun i => if i ∈ S then (-1 : ℂ) else 1)).prod • A02.ket S := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, map_smul,
        LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, number_ket]
      by_cases hi : i ∈ S
      · simp [hi, smul_smul, smul_sub]; module
      · simp [hi]
  unfold parity
  rw [hl, ← List.prod_toFinset _ (Finset.sort_nodup _ _)]
  simp only [Finset.sort_toFinset]
  rw [Finset.prod_ite]
  simp

lemma parity_square : parity (ι := ι) * parity (ι := ι) = 1 := by
  apply A02.end_ext_basis
  intro S
  simp only [Module.End.mul_apply, parity_ket, map_smul, Module.End.one_apply, smul_smul]
  rw [← mul_pow]
  simp

lemma parity_adjoint : LinearMap.adjoint (parity (ι := ι)) = parity (ι := ι) := by
  apply Eq.symm
  apply A02.adjoint_of_basis_pairing
  intro S T
  simp only [parity_ket, inner_smul_right, inner_smul_left, A02.ket_inner]
  by_cases h : S = T
  · subst T; simp
  · simp [h]

lemma parity_vacuum : parity (ι := ι) (A02.ket ∅) = A02.ket ∅ := by
  simp [parity_ket]

lemma parity_creation (i : ι) : parity (ι := ι) * creation i = -(creation i * parity (ι := ι)) := by
  apply A02.end_ext_basis
  intro S
  simp only [Module.End.mul_apply, LinearMap.neg_apply, parity_ket]
  by_cases hi : i ∈ S
  · simp [creation_ket, hi]
  · simp [creation_ket, hi, map_smul, parity_ket, Finset.card_insert_of_notMem hi,
      pow_succ, smul_smul, mul_comm]

lemma parity_annihilation (i : ι) :
    parity (ι := ι) * annihilation i = -(annihilation i * parity (ι := ι)) := by
  apply A02.end_ext_basis
  intro S
  simp only [Module.End.mul_apply, LinearMap.neg_apply, parity_ket]
  by_cases hi : i ∈ S
  · have hcard : S.card = (S.erase i).card + 1 := by
      simpa [Finset.insert_erase hi] using Finset.card_insert_of_notMem (Finset.notMem_erase i S)
    have hp : (-1 : ℂ) ^ S.card = -((-1 : ℂ) ^ (S.erase i).card) := by
      rw [hcard, pow_succ]; ring
    simp only [annihilation_ket, ite_eq_left hi, map_smul, parity_ket, hp, smul_smul]
    module
  · simp [annihilation_ket, hi]

lemma bilinear_commutator (a b c d : ι) :
    A02.commutator (hopping a b) (hopping c d) =
      (if b = c then (1 : ℂ) else 0) • hopping a d -
      (if a = d then (1 : ℂ) else 0) • hopping c b := by
  obtain ⟨R, ha, hc⟩ := concrete_car_exists (ι := ι)
  simpa [hopping, ha, hc] using A02.car_bilinear_commutator R.toAlgebraicCAR a b c d

lemma number_creation_commutator (i j : ι) : A02.commutator (number i) (creation j) =
    (if i = j then (1 : ℂ) else 0) • creation j := by
  obtain ⟨R, ha, hc⟩ := concrete_car_exists (ι := ι)
  simpa [A02.AlgebraicCAR.number, number, ha, hc] using
    A02.car_number_creation_commutator R.toAlgebraicCAR i j

lemma number_annihilation_commutator (i j : ι) : A02.commutator (number i) (annihilation j) =
    -(if i = j then (1 : ℂ) else 0) • annihilation j := by
  obtain ⟨R, ha, hc⟩ := concrete_car_exists (ι := ι)
  simpa [A02.AlgebraicCAR.number, number, ha, hc] using
    A02.car_number_annihilation_commutator R.toAlgebraicCAR i j

lemma total_number_creation_commutator (i : ι) :
    A02.commutator (totalNumber (ι := ι)) (creation i) = creation i := by
  simp only [totalNumber, A02.commutator, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  change (∑ j : ι, A02.commutator (number j) (creation i)) = _
  simp [number_creation_commutator]

lemma total_number_annihilation_commutator (i : ι) :
    A02.commutator (totalNumber (ι := ι)) (annihilation i) = -annihilation i := by
  simp only [totalNumber, A02.commutator, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  change (∑ j : ι, A02.commutator (number j) (annihilation i)) = _
  simp [number_annihilation_commutator]

lemma hopping_ket (i j : ι) (S : A02.Occupation ι) (hij : i ≠ j)
    (hi : i ∉ S) (hj : j ∈ S) :
    hopping i j (A02.ket S) = (fermionSign j S * fermionSign i (S.erase j)) •
      A02.ket (insert i (S.erase j)) := by
  unfold hopping
  simp [Module.End.mul_apply, annihilation_ket, hj, map_smul, creation_ket,
    hi, hij, smul_smul]

lemma hopping_blocked (i j : ι) (S : A02.Occupation ι)
    (h : j ∉ S ∨ (i ≠ j ∧ i ∈ S)) : hopping i j (A02.ket S) = 0 := by
  unfold hopping
  rcases h with hj | ⟨hij, hi⟩
  · simp [Module.End.mul_apply, annihilation_ket, hj]
  · by_cases hj : j ∈ S
    · simp [Module.End.mul_apply, annihilation_ket, hj, map_smul, creation_ket, hi, hij]
    · simp [Module.End.mul_apply, annihilation_ket, hj]

lemma hopping_diagonal (i : ι) : hopping i i = number i := by
  rfl

lemma hopping_adjoint (i j : ι) : LinearMap.adjoint (hopping i j) = hopping j i := by
  change LinearMap.adjoint ((creation i).comp (annihilation j)) = (creation j).comp (annihilation i)
  rw [LinearMap.adjoint_comp, ← creation_eq_adjoint, ← annihilation_eq_adjoint]

end Bosonize.Ch04
