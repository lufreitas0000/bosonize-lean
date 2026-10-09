module

public import Bosonize.Core.A02CARHilbert

/-!
# A03: coordinate budgets and filtered maps
Phase A: complete constructions and one-sorry theorem contracts.
Signed integer cutoffs retain negative-energy annihilation and composition excursions.
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
    diagonal a (A02.ket S) = a S • A02.ket S := by sorry

lemma diagonal_adjoint (a : A02.Occupation ι → ℂ) :
    LinearMap.adjoint (diagonal a) = diagonal (fun S => star (a S)) := by sorry

lemma ket_mem_coordinate_space (U : Set (A02.Occupation ι)) (S : A02.Occupation ι) :
    A02.ket S ∈ coordinateSpace U ↔ S ∈ U := by sorry

lemma coordinate_space_support (U : Set (A02.Occupation ι)) (v : A02.FockSpace ι) :
    v ∈ coordinateSpace U ↔ ∀ S, S ∉ U → A02.coordinates ι v S = 0 := by sorry

lemma coordinate_space_mono (U V : Set (A02.Occupation ι)) (hUV : U ⊆ V) :
    coordinateSpace U ≤ coordinateSpace V := by sorry

lemma coordinate_space_empty : coordinateSpace (∅ : Set (A02.Occupation ι)) = ⊥ := by sorry

lemma coordinate_space_univ : coordinateSpace (Set.univ : Set (A02.Occupation ι)) = ⊤ := by sorry

lemma coordinate_space_union (U V : Set (A02.Occupation ι)) :
    coordinateSpace (U ∪ V) = coordinateSpace U ⊔ coordinateSpace V := by sorry

lemma coordinate_space_disjoint (U V : Set (A02.Occupation ι)) (hUV : Disjoint U V) :
    ∀ u ∈ coordinateSpace U, ∀ v ∈ coordinateSpace V, inner ℂ u v = 0 := by sorry

lemma projection_ket (U : Set (A02.Occupation ι)) (S : A02.Occupation ι) :
    coordinateProjection U (A02.ket S) = if S ∈ U then A02.ket S else 0 := by sorry

lemma projection_idempotent (U : Set (A02.Occupation ι)) :
    coordinateProjection U * coordinateProjection U = coordinateProjection U := by sorry

lemma projection_adjoint (U : Set (A02.Occupation ι)) :
    LinearMap.adjoint (coordinateProjection U) = coordinateProjection U := by sorry

lemma projection_range (U : Set (A02.Occupation ι)) :
    LinearMap.range (coordinateProjection U) = coordinateSpace U := by sorry

lemma projection_fixed_iff (U : Set (A02.Occupation ι)) (v : A02.FockSpace ι) :
    coordinateProjection U v = v ↔ v ∈ coordinateSpace U := by sorry

lemma projection_intersection (U V : Set (A02.Occupation ι)) :
    coordinateProjection U * coordinateProjection V = coordinateProjection (U ∩ V) := by sorry

lemma projection_commute (U V : Set (A02.Occupation ι)) :
    coordinateProjection U * coordinateProjection V = coordinateProjection V * coordinateProjection U := by sorry

lemma projection_nonzero (U : Set (A02.Occupation ι)) (hU : U.Nonempty) :
    coordinateProjection U ≠ 0 := by sorry

lemma budget_mono (charge energy : A02.Occupation ι → ℤ) (N K K' : ℤ) (hK : K ≤ K') :
    budget charge energy N K ≤ budget charge energy N K' := by sorry

lemma box_mono (charge energy : A02.Occupation ι → ℤ) (K K' : ℤ) (Nmax Nmax' : ℕ)
    (hK : K ≤ K') (hN : Nmax ≤ Nmax') :
    chargeBox charge energy K Nmax ≤ chargeBox charge energy K' Nmax' := by sorry

lemma negative_budget (charge energy : A02.Occupation ι → ℤ)
    (he : ∀ S, 0 ≤ energy S) (N K : ℤ) (hK : K < 0) : budget charge energy N K = ⊥ := by sorry

lemma energy_spaces_orthogonal (charge energy : A02.Occupation ι → ℤ)
    (N E N' E' : ℤ) (hne : N ≠ N' ∨ E ≠ E') :
    ∀ u ∈ fixedEnergy charge energy N E, ∀ v ∈ fixedEnergy charge energy N' E',
      inner ℂ u v = 0 := by sorry

lemma budget_energy_decomposition (charge energy : A02.Occupation ι → ℤ)
    (he : ∀ S, 0 ≤ energy S) (N : ℤ) (K : ℕ) :
    budget charge energy N K = ⨆ E : Fin (K+1), fixedEnergy charge energy N (E.val : ℤ) := by sorry

lemma box_sector_decomposition (charge energy : A02.Occupation ι → ℤ) (K : ℤ) (Nmax : ℕ) :
    chargeBox charge energy K Nmax = ⨆ N : {N : ℤ // |N| ≤ (Nmax : ℤ)}, budget charge energy N.val K := by sorry

lemma exact_shift_filtered (charge energy : A02.Occupation ι → ℤ) (A : Operators ι) (q d : ℤ)
    (hA : ExactShift charge energy A q d) : Filtered charge energy A q d := by sorry

lemma filtered_identity (charge energy : A02.Occupation ι → ℤ) :
    Filtered charge energy (1 : Operators ι) 0 0 := by sorry

lemma filtered_budget_map (charge energy : A02.Occupation ι → ℤ) (A : Operators ι)
    (q d N K : ℤ) (hA : Filtered charge energy A q d) :
    ∀ v ∈ budget charge energy N K, A v ∈ budget charge energy (N+q) (K+d) := by sorry

lemma filtered_comp (charge energy : A02.Occupation ι → ℤ) (A B : Operators ι)
    (qA dA qB dB : ℤ) (hA : Filtered charge energy A qA dA) (hB : Filtered charge energy B qB dB) :
    Filtered charge energy (A*B) (qB+qA) (dB+dA) := by sorry

lemma filtered_lowering_zero (charge energy : A02.Occupation ι → ℤ)
    (he : ∀ S, 0 ≤ energy S) (A : Operators ι) (q d N K : ℤ)
    (hA : Filtered charge energy A q d) (hKd : K+d < 0) :
    ∀ v ∈ budget charge energy N K, A v = 0 := by sorry

lemma exact_shift_charge_commutator (charge energy : A02.Occupation ι → ℤ)
    (A : Operators ι) (q d : ℤ) (hA : ExactShift charge energy A q d) :
    A02.commutator (diagonal (fun S => (charge S : ℂ))) A = (q : ℂ) • A := by sorry

lemma exact_shift_energy_commutator (charge energy : A02.Occupation ι → ℤ)
    (A : Operators ι) (q d : ℤ) (hA : ExactShift charge energy A q d) :
    A02.commutator (diagonal (fun S => (energy S : ℂ))) A = (d : ℂ) • A := by sorry

lemma compression_maps (U : Set (A02.Occupation ι)) (A : Operators ι) :
    ∀ v ∈ coordinateSpace U, compress U A v ∈ coordinateSpace U := by sorry

lemma compression_adjoint (U : Set (A02.Occupation ι)) (A : Operators ι) :
    LinearMap.adjoint (compress U A) = compress U (LinearMap.adjoint A) := by sorry

lemma restricted_adjoint (P A B : Operators ι) (hP : LinearMap.adjoint P = P)
    (hAB : (A-B)*P = 0) : P*(LinearMap.adjoint A-LinearMap.adjoint B) = 0 := by sorry

lemma compressed_square_remainder (U : Set (A02.Occupation ι)) (A : Operators ι) :
    compress U (A^2) - (compress U A)^2 =
      coordinateProjection U*A*(1-coordinateProjection U)*A*coordinateProjection U := by sorry

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
    (hA : ∀ v ∈ U, A v ∈ W) (v : U) : (restrictedMap U W A hA v : V) = A v := by sorry

lemma comp_agree (U W : Submodule ℂ V) (A B C : Module.End ℂ V)
    (hC : ∀ v ∈ U, C v ∈ W) (hAB : ∀ w ∈ W, A w = B w) :
    ∀ v ∈ U, (A*C) v = (B*C) v := by sorry

lemma projection_product_remainder (Ptarget Pmiddle Psource A B : Module.End ℂ V) :
    Ptarget*A*B*Psource - Ptarget*A*Pmiddle*B*Psource =
      Ptarget*A*(1-Pmiddle)*B*Psource := by sorry

lemma projected_product_eq_iff (Ptarget Pmiddle Psource A B : Module.End ℂ V) :
    Ptarget*A*B*Psource = Ptarget*A*Pmiddle*B*Psource ↔
      Ptarget*A*(1-Pmiddle)*B*Psource = 0 := by sorry

lemma projected_product_eq_of_maps (Ptarget Pmiddle Psource A B : Module.End ℂ V)
    (hB : Pmiddle*B*Psource = B*Psource) :
    Ptarget*A*B*Psource = Ptarget*A*Pmiddle*B*Psource := by sorry

end Restricted

/-- Prefixes are listed in application order, beginning with the zero shift. -/
def prefixShifts (ds : List ℤ) : List ℤ := ds.scanl (· + ·) 0

def upwardExcursion (ds : List ℤ) : ℤ := (prefixShifts ds).foldl max 0

def positiveExcursion (ds : List ℤ) : ℤ := (ds.map (fun d => max d 0)).sum

def uniformCutoff (h M K Nmax : ℕ) : Prop := 2*M+K+Nmax ≤ h

def wordCutoff (h M K Nmax : ℕ) (ds : List ℤ) : Prop :=
  2*M+K+(upwardExcursion ds).toNat+Nmax ≤ h

lemma excursion_nonneg (ds : List ℤ) : 0 ≤ upwardExcursion ds := by sorry

lemma prefix_le_excursion (ds : List ℤ) (d : ℤ) (hd : d ∈ prefixShifts ds) :
    d ≤ upwardExcursion ds := by sorry

lemma excursion_le_positive (ds : List ℤ) : upwardExcursion ds ≤ positiveExcursion ds := by sorry

lemma excursion_up_down : upwardExcursion [2,-2] = 2 := by sorry

lemma excursion_down_up : upwardExcursion [-2,2] = 0 := by sorry

lemma word_cutoff_prefix (h M K Nmax : ℕ) (ds : List ℤ) (hw : wordCutoff h M K Nmax ds)
    (d : ℤ) (hd : d ∈ prefixShifts ds) :
    (2*M : ℤ)+(K : ℤ)+d+(Nmax : ℤ) ≤ (h : ℤ) := by sorry

section Words
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma filtered_application_word (charge energy : A02.Occupation ι → ℤ)
    (word : List (Operators ι × (ℤ × ℤ)))
    (hw : ∀ step ∈ word, Filtered charge energy step.1 step.2.1 step.2.2) :
    Filtered charge energy (applicationWord (word.map Prod.fst))
      (word.map (fun step => step.2.1)).sum (word.map (fun step => step.2.2)).sum := by sorry

lemma charge_preserving_word_prefix (charge energy : A02.Occupation ι → ℤ)
    (word : List (Operators ι × ℤ))
    (hw : ∀ step ∈ word, Filtered charge energy step.1 0 step.2)
    (N K : ℤ) (r : ℕ) :
    ∀ v ∈ budget charge energy N K,
      applicationWord ((word.take r).map Prod.fst) v ∈
        budget charge energy N (K+upwardExcursion (word.map Prod.snd)) := by sorry

end Words

end Bosonize.A03
