module

public import Bosonize.Core.A02CARHilbert

/-!
# A03: coordinate budgets and filtered maps
Phase B: complete constructions and proofs of the approved coordinate contracts.
Signed integer cutoffs retain negative-energy annihilation and composition excursions.
This coordinate calculus is generic in charge and energy. For the same-sea linear
model, Ch06Ext.excitation_twist_cancel relates the integer excitation labels to
arbitrary real twist offsets; no twist is silently selected by this module.
-/

@[expose] public section

namespace Bosonize.A03

open scoped BigOperators Classical

section Coordinates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Operators (ι : Type*) [Fintype ι] [DecidableEq ι] := Module.End ℂ (A02.FockSpace ι)

noncomputable def coordinateSpace (U : Set (A02.Occupation ι)) : Submodule ℂ (A02.FockSpace ι) :=
  Submodule.span ℂ (A02.ket '' U)

noncomputable def diagonal (a : A02.Occupation ι → ℂ) : Operators ι :=
  A02.extendBasis (fun S => a S • A02.ket S)

noncomputable def coordinateProjection (U : Set (A02.Occupation ι)) : Operators ι := by
  classical
  exact diagonal (fun S => if S ∈ U then 1 else 0)

noncomputable def fixedEnergy (charge energy : A02.Occupation ι → ℤ) (N E : ℤ) :
    Submodule ℂ (A02.FockSpace ι) :=
  coordinateSpace {S | charge S = N ∧ energy S = E}

noncomputable def budget (charge energy : A02.Occupation ι → ℤ) (N K : ℤ) :
    Submodule ℂ (A02.FockSpace ι) :=
  coordinateSpace {S | charge S = N ∧ energy S ≤ K}

noncomputable def chargeBox (charge energy : A02.Occupation ι → ℤ) (K : ℤ) (Nmax : ℕ) :
    Submodule ℂ (A02.FockSpace ι) :=
  coordinateSpace {S | energy S ≤ K ∧ |charge S| ≤ (Nmax : ℤ)}

noncomputable def budgetProjection (charge energy : A02.Occupation ι → ℤ) (N K : ℤ) : Operators ι :=
  coordinateProjection {S | charge S = N ∧ energy S ≤ K}

noncomputable def boxProjection (charge energy : A02.Occupation ι → ℤ) (K : ℤ) (Nmax : ℕ) : Operators ι :=
  coordinateProjection {S | energy S ≤ K ∧ |charge S| ≤ (Nmax : ℤ)}

/-- Every input basis vector has output supported in the stated shifted coordinate set. -/
def Filtered (charge energy : A02.Occupation ι → ℤ) (A : Operators ι) (q d : ℤ) : Prop :=
  ∀ S, A (A02.ket S) ∈ coordinateSpace {T | charge T = charge S + q ∧ energy T ≤ energy S + d}

/-- Equality of the energy shift, for observable commutators rather than mere bounds. -/
def ExactShift (charge energy : A02.Occupation ι → ℤ) (A : Operators ι) (q d : ℤ) : Prop :=
  ∀ S, A (A02.ket S) ∈ coordinateSpace {T | charge T = charge S + q ∧ energy T = energy S + d}

noncomputable def compress (U : Set (A02.Occupation ι)) (A : Operators ι) : Operators ι :=
  coordinateProjection U * A * coordinateProjection U

lemma diagonal_ket (a : A02.Occupation ι → ℂ) (S : A02.Occupation ι) :
    diagonal a (A02.ket S) = a S • A02.ket S := by
  exact A02.extend_basis_ket _ S

lemma diagonal_adjoint (a : A02.Occupation ι → ℂ) :
    LinearMap.adjoint (diagonal a) = diagonal (fun S => star (a S)) := by
  apply (A02.adjoint_of_basis_pairing _ _ ?_).symm
  intro S T
  rw [diagonal_ket, diagonal_ket, inner_smul_right, inner_smul_left,
    A02.ket_inner]
  by_cases h : S = T
  · subst T; simp
  · simp [h]

lemma ket_mem_coordinate_space (U : Set (A02.Occupation ι)) (S : A02.Occupation ι) :
    A02.ket S ∈ coordinateSpace U ↔ S ∈ U := by
  constructor
  · intro h
    by_contra hn
    have hz : ∀ v ∈ coordinateSpace U, v S = 0 := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨T, hT, rfl⟩ := hx
        simp [A02.ket_apply, show S ≠ T by intro he; subst T; exact hn hT]
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul a x _ hx => simp [hx]
    have := hz _ h
    simp [A02.ket_apply] at this
  · intro h
    exact Submodule.subset_span ⟨S, h, rfl⟩

lemma coordinate_space_support (U : Set (A02.Occupation ι)) (v : A02.FockSpace ι) :
    v ∈ coordinateSpace U ↔ ∀ S, S ∉ U → A02.coordinates ι v S = 0 := by
  constructor
  · intro h S hS
    change v S = 0
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨T, hT, rfl⟩ := hx
      simp [A02.ket_apply, show S ≠ T by intro he; subst T; exact hS hT]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  · intro hv
    rw [A02.occupation_expansion v]
    apply Submodule.sum_mem
    intro S _
    by_cases hS : S ∈ U
    · exact Submodule.smul_mem _ _ ((ket_mem_coordinate_space U S).mpr hS)
    · have hz := hv S hS
      change v S = 0 at hz
      simp [hz]

lemma coordinate_space_mono (U V : Set (A02.Occupation ι)) (hUV : U ⊆ V) :
    coordinateSpace U ≤ coordinateSpace V := by
  exact Submodule.span_mono (Set.image_mono hUV)

lemma coordinate_space_empty : coordinateSpace (∅ : Set (A02.Occupation ι)) = ⊥ := by
  simp [coordinateSpace]

lemma coordinate_space_univ : coordinateSpace (Set.univ : Set (A02.Occupation ι)) = ⊤ := by
  apply top_unique
  intro v _
  exact (coordinate_space_support _ v).mpr (by simp)

lemma coordinate_space_union (U V : Set (A02.Occupation ι)) :
    coordinateSpace (U ∪ V) = coordinateSpace U ⊔ coordinateSpace V := by
  simp [coordinateSpace, Set.image_union, Submodule.span_union]

lemma coordinate_space_disjoint (U V : Set (A02.Occupation ι)) (hUV : Disjoint U V) :
    ∀ u ∈ coordinateSpace U, ∀ v ∈ coordinateSpace V, inner ℂ u v = 0 := by
  intro u hu v hv
  rw [A02.fock_inner]
  apply Finset.sum_eq_zero
  intro S _
  by_cases hS : S ∈ U
  · have hn : S ∉ V := fun hV => Set.disjoint_left.mp hUV hS hV
    have hz := (coordinate_space_support V v).mp hv S hn
    change v S = 0 at hz
    simp [hz]
  · have hz := (coordinate_space_support U u).mp hu S hS
    change u S = 0 at hz
    simp [hz]

lemma projection_ket (U : Set (A02.Occupation ι)) (S : A02.Occupation ι) :
    coordinateProjection U (A02.ket S) = if S ∈ U then A02.ket S else 0 := by
  classical
  simp [coordinateProjection, diagonal_ket]

lemma projection_idempotent (U : Set (A02.Occupation ι)) :
    coordinateProjection U * coordinateProjection U = coordinateProjection U := by
  apply A02.end_ext_basis
  intro S
  classical
  simp only [Module.End.mul_apply, projection_ket]
  split_ifs <;> simp [projection_ket, *]

lemma projection_adjoint (U : Set (A02.Occupation ι)) :
    LinearMap.adjoint (coordinateProjection U) = coordinateProjection U := by
  classical
  unfold coordinateProjection
  rw [diagonal_adjoint]
  congr 1
  funext S
  split_ifs <;> simp

lemma projection_range (U : Set (A02.Occupation ι)) :
    LinearMap.range (coordinateProjection U) = coordinateSpace U := by
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    rw [A02.occupation_expansion w, map_sum]
    apply Submodule.sum_mem
    intro S _
    rw [map_smul, projection_ket]
    split_ifs with hS
    · exact Submodule.smul_mem _ _ ((ket_mem_coordinate_space _ _).mpr hS)
    · simp
  · apply Submodule.span_le.mpr
    rintro v ⟨S, hS, rfl⟩
    exact ⟨A02.ket S, by simp [projection_ket, hS]⟩

lemma projection_fixed_iff (U : Set (A02.Occupation ι)) (v : A02.FockSpace ι) :
    coordinateProjection U v = v ↔ v ∈ coordinateSpace U := by
  constructor
  · intro h
    rw [← h]
    rw [← projection_range]
    exact ⟨v, rfl⟩
  · intro hv
    rw [← projection_range] at hv
    obtain ⟨w, rfl⟩ := hv
    exact congrArg (fun A : Operators ι => A w) (projection_idempotent U)

lemma projection_intersection (U V : Set (A02.Occupation ι)) :
    coordinateProjection U * coordinateProjection V = coordinateProjection (U ∩ V) := by
  apply A02.end_ext_basis
  intro S
  classical
  simp only [Module.End.mul_apply, projection_ket]
  by_cases hU : S ∈ U <;> by_cases hV : S ∈ V <;> simp [hU, hV, projection_ket]

lemma projection_commute (U V : Set (A02.Occupation ι)) :
    coordinateProjection U * coordinateProjection V = coordinateProjection V * coordinateProjection U := by
  rw [projection_intersection, projection_intersection, Set.inter_comm]

lemma projection_nonzero (U : Set (A02.Occupation ι)) (hU : U.Nonempty) :
    coordinateProjection U ≠ 0 := by
  obtain ⟨S, hS⟩ := hU
  intro hz
  have he := projection_ket U S
  rw [hz] at he
  simp only [LinearMap.zero_apply, ite_eq_left hS] at he
  exact A02.ket_ne_zero S he.symm

lemma budget_mono (charge energy : A02.Occupation ι → ℤ) (N K K' : ℤ) (hK : K ≤ K') :
    budget charge energy N K ≤ budget charge energy N K' := by
  apply coordinate_space_mono
  intro S hS
  exact ⟨hS.1, hS.2.trans hK⟩

lemma box_mono (charge energy : A02.Occupation ι → ℤ) (K K' : ℤ) (Nmax Nmax' : ℕ)
    (hK : K ≤ K') (hN : Nmax ≤ Nmax') :
    chargeBox charge energy K Nmax ≤ chargeBox charge energy K' Nmax' := by
  apply coordinate_space_mono
  intro S hS
  exact ⟨hS.1.trans hK, hS.2.trans (by exact_mod_cast hN)⟩

lemma negative_budget (charge energy : A02.Occupation ι → ℤ)
    (he : ∀ S, 0 ≤ energy S) (N K : ℤ) (hK : K < 0) : budget charge energy N K = ⊥ := by
  have hs : {S | charge S = N ∧ energy S ≤ K} = ∅ := by
    ext S
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hS
    have := he S
    omega
  change coordinateSpace _ = _
  rw [hs, coordinate_space_empty]

lemma energy_spaces_orthogonal (charge energy : A02.Occupation ι → ℤ)
    (N E N' E' : ℤ) (hne : N ≠ N' ∨ E ≠ E') :
    ∀ u ∈ fixedEnergy charge energy N E, ∀ v ∈ fixedEnergy charge energy N' E',
      inner ℂ u v = 0 := by
  apply coordinate_space_disjoint
  apply Set.disjoint_left.mpr
  intro S hS hS'
  rcases hne with h | h
  · exact h (hS.1.symm.trans hS'.1)
  · exact h (hS.2.symm.trans hS'.2)

lemma budget_energy_decomposition (charge energy : A02.Occupation ι → ℤ)
    (he : ∀ S, 0 ≤ energy S) (N : ℤ) (K : ℕ) :
    budget charge energy N K = ⨆ E : Fin (K+1), fixedEnergy charge energy N (E.val : ℤ) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨S, hS, rfl⟩
    change charge S = N ∧ energy S ≤ (K : ℤ) at hS
    have hE := he S
    have hbound : (energy S).toNat < K+1 := by omega
    apply (le_iSup (fun E : Fin (K+1) => fixedEnergy charge energy N (E.val : ℤ)) ⟨(energy S).toNat, hbound⟩)
    apply (ket_mem_coordinate_space _ S).mpr
    exact ⟨hS.1, (Int.toNat_of_nonneg hE).symm⟩
  · apply iSup_le
    intro E
    apply coordinate_space_mono
    intro S hS
    change charge S = N ∧ energy S = (E.val : ℤ) at hS
    exact ⟨hS.1, by have := E.isLt; omega⟩

lemma box_sector_decomposition (charge energy : A02.Occupation ι → ℤ) (K : ℤ) (Nmax : ℕ) :
    chargeBox charge energy K Nmax = ⨆ N : {N : ℤ // |N| ≤ (Nmax : ℤ)}, budget charge energy N.val K := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨S, hS, rfl⟩
    apply (le_iSup (fun N : {N : ℤ // |N| ≤ (Nmax : ℤ)} => budget charge energy N.val K) ⟨charge S, hS.2⟩)
    apply (ket_mem_coordinate_space _ S).mpr
    exact ⟨rfl, hS.1⟩
  · apply iSup_le
    intro N
    apply coordinate_space_mono
    intro S hS
    exact ⟨hS.2, by rw [hS.1]; exact N.property⟩

lemma exact_shift_filtered (charge energy : A02.Occupation ι → ℤ) (A : Operators ι) (q d : ℤ)
    (hA : ExactShift charge energy A q d) : Filtered charge energy A q d := by
  intro S
  apply coordinate_space_mono _ _ (by intro T hT; change charge T = charge S + q ∧ energy T = energy S + d at hT; exact ⟨hT.1, hT.2.le⟩)
  exact hA S

lemma filtered_identity (charge energy : A02.Occupation ι → ℤ) :
    Filtered charge energy (1 : Operators ι) 0 0 := by
  intro S
  apply (ket_mem_coordinate_space _ S).mpr
  simp

lemma filtered_budget_map (charge energy : A02.Occupation ι → ℤ) (A : Operators ι)
    (q d N K : ℤ) (hA : Filtered charge energy A q d) :
    ∀ v ∈ budget charge energy N K, A v ∈ budget charge energy (N+q) (K+d) := by
  intro v hv
  change v ∈ coordinateSpace _ at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, hS, rfl⟩ := hx
    change charge S = N ∧ energy S ≤ K at hS
    apply coordinate_space_mono _ _ (by
      intro T hT
      change charge T = charge S + q ∧ energy T ≤ energy S + d at hT
      exact ⟨by omega, by omega⟩)
    exact hA S
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa using Submodule.smul_mem _ a hx

lemma filtered_comp (charge energy : A02.Occupation ι → ℤ) (A B : Operators ι)
    (qA dA qB dB : ℤ) (hA : Filtered charge energy A qA dA) (hB : Filtered charge energy B qB dB) :
    Filtered charge energy (A*B) (qB+qA) (dB+dA) := by
  intro S
  change A (B (A02.ket S)) ∈ _
  have hm := filtered_budget_map charge energy A qA dA (charge S+qB) (energy S+dB) hA _ (hB S)
  simpa [budget, add_assoc] using hm

lemma filtered_lowering_zero (charge energy : A02.Occupation ι → ℤ)
    (he : ∀ S, 0 ≤ energy S) (A : Operators ι) (q d N K : ℤ)
    (hA : Filtered charge energy A q d) (hKd : K+d < 0) :
    ∀ v ∈ budget charge energy N K, A v = 0 := by
  intro v hv
  have hm := filtered_budget_map charge energy A q d N K hA v hv
  rw [negative_budget charge energy he (N+q) (K+d) hKd] at hm
  exact hm

lemma exact_shift_charge_commutator (charge energy : A02.Occupation ι → ℤ)
    (A : Operators ι) (q d : ℤ) (hA : ExactShift charge energy A q d) :
    A02.commutator (diagonal (fun S => (charge S : ℂ))) A = (q : ℂ) • A := by
  apply A02.end_ext_basis
  intro S
  have eig : diagonal (fun T => (charge T : ℂ)) (A (A02.ket S)) =
      ((charge S+q : ℤ) : ℂ) • A (A02.ket S) := by
    have hs := (coordinate_space_support _ _).mp (hA S)
    conv_lhs => rw [A02.occupation_expansion (A (A02.ket S))]
    conv_rhs => rw [A02.occupation_expansion (A (A02.ket S))]
    rw [map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro T _
    by_cases hT : T ∈ {T | charge T = charge S+q ∧ energy T = energy S+d}
    · simp only [map_smul, diagonal_ket, smul_smul]
      rw [hT.1]
      congr 1; ring
    · have hz := hs T hT
      change A (A02.ket S) T = 0 at hz
      simp [hz]
  change diagonal (fun T => (charge T : ℂ)) (A (A02.ket S)) -
      A (diagonal (fun T => (charge T : ℂ)) (A02.ket S)) = (q : ℂ) • A (A02.ket S)
  rw [eig, diagonal_ket, map_smul, ← sub_smul]
  congr 1
  push_cast
  ring

lemma exact_shift_energy_commutator (charge energy : A02.Occupation ι → ℤ)
    (A : Operators ι) (q d : ℤ) (hA : ExactShift charge energy A q d) :
    A02.commutator (diagonal (fun S => (energy S : ℂ))) A = (d : ℂ) • A := by
  apply A02.end_ext_basis
  intro S
  have eig : diagonal (fun T => (energy T : ℂ)) (A (A02.ket S)) =
      ((energy S+d : ℤ) : ℂ) • A (A02.ket S) := by
    have hs := (coordinate_space_support _ _).mp (hA S)
    conv_lhs => rw [A02.occupation_expansion (A (A02.ket S))]
    conv_rhs => rw [A02.occupation_expansion (A (A02.ket S))]
    rw [map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro T _
    by_cases hT : T ∈ {T | charge T = charge S+q ∧ energy T = energy S+d}
    · simp only [map_smul, diagonal_ket, smul_smul]
      rw [hT.2]
      congr 1; ring
    · have hz := hs T hT
      change A (A02.ket S) T = 0 at hz
      simp [hz]
  change diagonal (fun T => (energy T : ℂ)) (A (A02.ket S)) -
      A (diagonal (fun T => (energy T : ℂ)) (A02.ket S)) = (d : ℂ) • A (A02.ket S)
  rw [eig, diagonal_ket, map_smul, ← sub_smul]
  congr 1
  push_cast
  ring

lemma compression_maps (U : Set (A02.Occupation ι)) (A : Operators ι) :
    ∀ v ∈ coordinateSpace U, compress U A v ∈ coordinateSpace U := by
  intro v _
  rw [← projection_range]
  exact ⟨A (coordinateProjection U v), rfl⟩

lemma compression_adjoint (U : Set (A02.Occupation ι)) (A : Operators ι) :
    LinearMap.adjoint (compress U A) = compress U (LinearMap.adjoint A) := by
  change LinearMap.adjoint ((coordinateProjection U).comp (A.comp (coordinateProjection U))) = _
  rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, projection_adjoint]
  rfl

lemma restricted_adjoint (P A B : Operators ι) (hP : LinearMap.adjoint P = P)
    (hAB : (A-B)*P = 0) : P*(LinearMap.adjoint A-LinearMap.adjoint B) = 0 := by
  have h := congrArg LinearMap.adjoint hAB
  rw [map_zero] at h
  change LinearMap.adjoint ((A-B).comp P) = 0 at h
  simpa only [LinearMap.adjoint_comp, map_sub, hP, Module.End.mul_eq_comp] using h

lemma compressed_square_remainder (U : Set (A02.Occupation ι)) (A : Operators ι) :
    compress U (A^2) - (compress U A)^2 =
      coordinateProjection U*A*(1-coordinateProjection U)*A*coordinateProjection U := by
  unfold compress
  have hP := projection_idempotent U
  simp only [pow_two]
  calc
    coordinateProjection U * (A*A) * coordinateProjection U -
        (coordinateProjection U*A*coordinateProjection U)*(coordinateProjection U*A*coordinateProjection U) =
        coordinateProjection U*A*A*coordinateProjection U -
        coordinateProjection U*A*(coordinateProjection U*coordinateProjection U)*A*coordinateProjection U := by simp only [mul_assoc]
    _ = _ := by rw [hP]; noncomm_ring

end Coordinates

section Restricted
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- An actual linear map between submodule carriers, given its checked image condition. -/
def restrictedMap (U W : Submodule ℂ V) (A : Module.End ℂ V)
    (hA : ∀ v ∈ U, A v ∈ W) : U →ₗ[ℂ] W :=
  (A.domRestrict U).codRestrict W (fun v => hA v v.property)

/-- The list is in application order: [A,B] evaluates to B*A. -/
def applicationWord (As : List (Module.End ℂ V)) : Module.End ℂ V := As.reverse.prod

lemma restricted_map_apply (U W : Submodule ℂ V) (A : Module.End ℂ V)
    (hA : ∀ v ∈ U, A v ∈ W) (v : U) : (restrictedMap U W A hA v : V) = A v := by
  rfl

lemma comp_agree (U W : Submodule ℂ V) (A B C : Module.End ℂ V)
    (hC : ∀ v ∈ U, C v ∈ W) (hAB : ∀ w ∈ W, A w = B w) :
    ∀ v ∈ U, (A*C) v = (B*C) v := by
  intro v hv; exact hAB _ (hC v hv)

lemma projection_product_remainder (Ptarget Pmiddle Psource A B : Module.End ℂ V) :
    Ptarget*A*B*Psource - Ptarget*A*Pmiddle*B*Psource =
      Ptarget*A*(1-Pmiddle)*B*Psource := by
  noncomm_ring

lemma projected_product_eq_iff (Ptarget Pmiddle Psource A B : Module.End ℂ V) :
    Ptarget*A*B*Psource = Ptarget*A*Pmiddle*B*Psource ↔
      Ptarget*A*(1-Pmiddle)*B*Psource = 0 := by
  rw [← projection_product_remainder]; exact sub_eq_zero.symm

lemma projected_product_eq_of_maps (Ptarget Pmiddle Psource A B : Module.End ℂ V)
    (hB : Pmiddle*B*Psource = B*Psource) :
    Ptarget*A*B*Psource = Ptarget*A*Pmiddle*B*Psource := by
  calc
    Ptarget*A*B*Psource = Ptarget*A*(B*Psource) := by simp only [mul_assoc]
    _ = Ptarget*A*(Pmiddle*B*Psource) := by rw [hB]
    _ = _ := by simp only [mul_assoc]

end Restricted

/-- Prefixes are listed in application order, beginning with the zero shift. -/
def prefixShifts (ds : List ℤ) : List ℤ := ds.scanl (· + ·) 0

def upwardExcursion (ds : List ℤ) : ℤ := (prefixShifts ds).foldl max 0

def positiveExcursion (ds : List ℤ) : ℤ := (ds.map (fun d => max d 0)).sum

def uniformCutoff (h M K Nmax : ℕ) : Prop := 2*M+K+Nmax ≤ h

def wordCutoff (h M K Nmax : ℕ) (ds : List ℤ) : Prop :=
  2*M+K+(upwardExcursion ds).toNat+Nmax ≤ h

lemma excursion_nonneg (ds : List ℤ) : 0 ≤ upwardExcursion ds := by
  have bound (xs : List ℤ) (a : ℤ) : a ≤ xs.foldl max a := by
    induction xs generalizing a with
    | nil => exact le_rfl
    | cons x xs ih => exact (le_max_left a x).trans (ih (max a x))
  exact bound _ 0

lemma prefix_le_excursion (ds : List ℤ) (d : ℤ) (hd : d ∈ prefixShifts ds) :
    d ≤ upwardExcursion ds := by
  have bound (xs : List ℤ) (a : ℤ) : a ≤ xs.foldl max a := by
    induction xs generalizing a with
    | nil => exact le_rfl
    | cons x xs ih => exact (le_max_left a x).trans (ih (max a x))
  have member (xs : List ℤ) (a d : ℤ) (hd : d ∈ xs) : d ≤ xs.foldl max a := by
    induction xs generalizing a with
    | nil => simp at hd
    | cons x xs ih =>
      rcases List.mem_cons.mp hd with rfl | hd
      · exact (le_max_right a d).trans (bound xs _)
      · exact ih _ hd
  exact member _ 0 d hd

lemma excursion_le_positive (ds : List ℤ) : upwardExcursion ds ≤ positiveExcursion ds := by
  have positive (xs : List ℤ) : 0 ≤ (xs.map (fun d => max d 0)).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons]; have := le_max_right x 0; omega
  have scanBound (xs : List ℤ) (a d : ℤ) (hd : d ∈ xs.scanl (· + ·) a) :
      d ≤ a+(xs.map (fun x => max x 0)).sum := by
    induction xs generalizing a with
    | nil =>
      have he : d = a := by simpa using hd
      simpa using he.le
    | cons x xs ih =>
      rw [List.scanl_cons] at hd
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hd with rfl | hd
      · have := positive xs; have := le_max_right x 0; omega
      · have hb := ih (a+x) hd; have := le_max_left x 0; omega
  have fold (xs : List ℤ) (a b : ℤ) (hab : a ≤ b) (hx : ∀ x ∈ xs, x ≤ b) : xs.foldl max a ≤ b := by
    induction xs generalizing a with
    | nil => exact hab
    | cons x xs ih =>
      apply ih (max a x) (max_le hab (hx x (by simp)))
      intro y hy
      exact hx y (by simp [hy])
  apply fold _ _ _ (positive ds)
  intro d hd
  simpa [positiveExcursion] using scanBound ds 0 d hd

lemma excursion_up_down : upwardExcursion [2,-2] = 2 := by
  norm_num [upwardExcursion, prefixShifts]

lemma excursion_down_up : upwardExcursion [-2,2] = 0 := by
  norm_num [upwardExcursion, prefixShifts]

lemma word_cutoff_prefix (h M K Nmax : ℕ) (ds : List ℤ) (hw : wordCutoff h M K Nmax ds)
    (d : ℤ) (hd : d ∈ prefixShifts ds) :
    (2*M : ℤ)+(K : ℤ)+d+(Nmax : ℤ) ≤ (h : ℤ) := by
  have hb := prefix_le_excursion ds d hd
  have hn := Int.toNat_of_nonneg (excursion_nonneg ds)
  unfold wordCutoff at hw
  omega

section Words
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma filtered_application_word (charge energy : A02.Occupation ι → ℤ)
    (word : List (Operators ι × (ℤ × ℤ)))
    (hw : ∀ step ∈ word, Filtered charge energy step.1 step.2.1 step.2.2) :
    Filtered charge energy (applicationWord (word.map Prod.fst))
      (word.map (fun step => step.2.1)).sum (word.map (fun step => step.2.2)).sum := by
  have maps : ∀ (xs : List (Operators ι × (ℤ × ℤ))),
      (∀ step ∈ xs, Filtered charge energy step.1 step.2.1 step.2.2) →
      ∀ (N K : ℤ) (v : A02.FockSpace ι), v ∈ budget charge energy N K →
      applicationWord (xs.map Prod.fst) v ∈ budget charge energy
        (N+(xs.map (fun x => x.2.1)).sum) (K+(xs.map (fun x => x.2.2)).sum) := by
    intro xs
    induction xs with
    | nil => intro _ N K v hv; simpa [applicationWord] using hv
    | cons x xs ih =>
      intro hx N K v hv
      have hs := filtered_budget_map (ι := ι) charge energy x.1 x.2.1 x.2.2 N K
        (hx x List.mem_cons_self) v hv
      have hr := ih (fun y hy => hx y (List.mem_cons_of_mem x hy))
        (N+x.2.1) (K+x.2.2) (x.1 v) hs
      simpa only [applicationWord, List.map_cons, List.reverse_cons, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply, List.sum_cons,
        add_assoc] using hr
  intro S
  exact maps word hw (charge S) (energy S) (A02.ket S)
    ((ket_mem_coordinate_space _ S).mpr ⟨rfl, le_rfl⟩)

lemma charge_preserving_word_prefix (charge energy : A02.Occupation ι → ℤ)
    (word : List (Operators ι × ℤ))
    (hw : ∀ step ∈ word, Filtered charge energy step.1 0 step.2)
    (N K : ℤ) (r : ℕ) :
    ∀ v ∈ budget charge energy N K,
      applicationWord ((word.take r).map Prod.fst) v ∈
        budget charge energy N (K+upwardExcursion (word.map Prod.snd)) := by
  have maps : ∀ (xs : List (Operators ι × ℤ)),
      (∀ step ∈ xs, Filtered charge energy step.1 0 step.2) →
      ∀ (N K : ℤ) (v : A02.FockSpace ι), v ∈ budget charge energy N K →
      applicationWord (xs.map Prod.fst) v ∈ budget charge energy N (K+(xs.map Prod.snd).sum) := by
    intro xs
    induction xs with
    | nil => intro _ N K v hv; simpa [applicationWord] using hv
    | cons x xs ih =>
      intro hx N K v hv
      have hs := filtered_budget_map (ι := ι) charge energy x.1 0 x.2 N K
        (hx x List.mem_cons_self) v hv
      rw [add_zero] at hs
      have hr := ih (fun y hy => hx y (List.mem_cons_of_mem x hy)) N (K+x.2) (x.1 v) hs
      simpa only [applicationWord, List.map_cons, List.reverse_cons, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply, List.sum_cons,
        add_assoc] using hr
  have scanMember (xs : List ℤ) (r : ℕ) (a : ℤ) :
      a+(xs.take r).sum ∈ xs.scanl (· + ·) a := by
    induction xs generalizing r a with
    | nil => simp
    | cons x xs ih =>
      cases r with
      | zero => simp [List.scanl_cons]
      | succ r =>
        simp only [List.take_succ_cons, List.sum_cons, List.scanl_cons, List.mem_cons]
        exact Or.inr (by simpa only [add_assoc] using ih r (a+x))
  have hm : ((word.take r).map Prod.snd).sum ∈ prefixShifts (word.map Prod.snd) := by
    simpa only [prefixShifts, List.map_take, zero_add] using scanMember (word.map Prod.snd) r 0
  have hb := prefix_le_excursion (word.map Prod.snd) _ hm
  intro v hv
  apply budget_mono charge energy N (K+((word.take r).map Prod.snd).sum) (K+upwardExcursion (word.map Prod.snd)) (by omega)
  exact maps (word.take r) (fun x hx => hw x (List.mem_of_mem_take hx)) N K v hv

end Words

end Bosonize.A03
