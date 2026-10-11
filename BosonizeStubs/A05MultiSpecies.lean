module

public import Bosonize.Core.Ch11HaldaneCompleteness
public import Mathlib.Order.Prod.Lex.Basic

/-! A05 multispecies prerequisites for CH13. Complete finite data, Phase A contracts.
The actual occupation carrier and total-excitation budget are the frozen CH07 ones. -/
@[expose] public section
namespace Bosonize.A05
open scoped BigOperators Classical
variable {σ : Type*} [Fintype σ] [LinearOrder σ]

abbrev Mode (σ : Type*) (h : ℕ) := σ × Ch01.Band (2*h)

/-- Equip the ordinary product carrier with the lexicographic total order. -/
@[instance_reducible] noncomputable def speciesOrder (h : ℕ) : LinearOrder (Mode σ h) :=
  inferInstanceAs (LinearOrder (σ ×ₗ Ch01.Band (2*h)))

noncomputable local instance localModeLinearOrder (h : ℕ) : LinearOrder (Mode σ h) := speciesOrder h
noncomputable local instance localModeLT (h : ℕ) : LT (Mode σ h) := (speciesOrder h).toLT
noncomputable local instance localModeLE (h : ℕ) : LE (Mode σ h) := (speciesOrder h).toLE
noncomputable local instance localModeDecidableEq (h : ℕ) : DecidableEq (Mode σ h) := (speciesOrder h).toDecidableEq

abbrev Occupation (σ : Type*) [Fintype σ] [LinearOrder σ] (h : ℕ) := A02.Occupation (Mode σ h)
abbrev FockSpace (σ : Type*) [Fintype σ] [LinearOrder σ] (h : ℕ) := A02.FockSpace (Mode σ h)
abbrev Operators (σ : Type*) [Fintype σ] [LinearOrder σ] (h : ℕ) := Module.End ℂ (FockSpace σ h)

/-- This is exactly CH07's actual total-energy budget, not a product of K-cutoffs. -/
noncomputable abbrev jointBudget (h : ℕ) (Ns : σ → ℤ) (K : ℕ) := Ch07.speciesBudget h Ns (K : ℤ)

def admissible (h : ℕ) (Ns : σ → ℤ) : Prop := ∀ ν, Ch07.admissible h (Ns ν)
def r2 (h K : ℕ) (Ns : σ → ℤ) : Prop := ∀ ν, 2*(K : ℤ)+|Ns ν| ≤ (h : ℤ)

noncomputable def jointConfiguration (h : ℕ) (Ss : σ → Ch07.Occupation h) : Occupation σ h :=
  Finset.univ.biUnion (fun ν => (Ss ν).image (fun k => (ν,k)))

noncomputable def groundConfiguration (h : ℕ) (Ns : σ → ℤ) : Occupation σ h :=
  jointConfiguration h (fun ν => Ch07.groundConfiguration h (Ns ν))

noncomputable def groundKet (h : ℕ) (Ns : σ → ℤ) : FockSpace σ h :=
  A02.ket (groundConfiguration h Ns)

/-- Coordinate product in the actual fermionic occupation carrier. Its equality
with actual species creator-word states is a separate theorem below. -/
noncomputable def tensorVector (h : ℕ) (vs : σ → Ch07.FockSpace h) : FockSpace σ h :=
  (A02.coordinates (Mode σ h)).symm (fun S => ∏ ν, vs ν (Ch07.speciesConfiguration h S ν))

noncomputable def annihilation (h : ℕ) (ν : σ) (k : Ch01.Band (2*h)) : Operators σ h :=
  Ch04.annihilation (ν,k)
noncomputable def creation (h : ℕ) (ν : σ) (k : Ch01.Band (2*h)) : Operators σ h :=
  Ch04.creation (ν,k)

noncomputable def rho (h : ℕ) (ν : σ) (m : ℤ) : Operators σ h :=
  ∑ z ∈ A04.validPairs (2*h) m, Ch04.hopping (ν,z.1) (ν,z.2)

noncomputable def chargeObservable (h : ℕ) (ν : σ) : Operators σ h :=
  A03.diagonal (fun S => (Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) : ℂ))

noncomputable def creatorWord (h : ℕ) (parts : σ → List ℕ) : Operators σ h :=
  ((Finset.univ : Finset σ).sort (· ≤ ·)).map
    (fun ν => ((parts ν).map (fun m => rho h ν (m : ℤ))).prod) |>.prod

noncomputable def wordState (h : ℕ) (Ns : σ → ℤ) (parts : σ → List ℕ) : FockSpace σ h :=
  creatorWord h parts (groundKet h Ns)

/-- Finite labels of energy splits with total energy at most K. -/
abbrev JointPartitions (σ : Type*) [Fintype σ] (K : ℕ) :=
  {ps : σ → Ch11.BudgetPartitions K // ∑ ν, (ps ν).1.val ≤ K}

noncomputable instance jointPartitionsFintype (K : ℕ) : Fintype (JointPartitions σ K) :=
  Fintype.ofFinite _

def jointEnergy {K : ℕ} (p : JointPartitions σ K) : ℕ := ∑ ν, (p.val ν).1.val

def jointNormalization {K : ℕ} (p : JointPartitions σ K) : ℕ :=
  ∏ ν, Ch11.partitionNormalization (p.val ν).2

noncomputable def partitionState (h : ℕ) (Ns : σ → ℤ) {K : ℕ}
    (p : JointPartitions σ K) : FockSpace σ h :=
  wordState h Ns (fun ν => Ch11.partitionList (p.val ν).2)

/-- Every species keeps its own external boundary field parameter. -/
noncomputable def liftedAnnihilation (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (ν : σ) (x : ℤ) : Operators σ h :=
  (A01.normalization (2*h) : ℂ) •
    ∑ k : Ch01.Band (2*h), Ch06Ext.twistedCharacter (2*h) (b ν) k x • annihilation h ν k

omit [Fintype σ] in
lemma mode_lt_iff (h : ℕ) (ν η : σ) (k l : Ch01.Band (2*h)) :
    (ν,k) < (η,l) ↔ ν < η ∨ ν=η ∧ k<l := by
  exact Prod.Lex.toLex_lt_toLex (x := (ν,k)) (y := (η,l))

lemma species_joint_configuration (h : ℕ) (Ss : σ → Ch07.Occupation h) (ν : σ) :
    Ch07.speciesConfiguration h (jointConfiguration h Ss) ν = Ss ν := by
  ext k
  simp only [Ch07.speciesConfiguration, jointConfiguration, Finset.mem_image,
    Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
  aesop

lemma joint_species_configuration (h : ℕ) (S : Occupation σ h) :
    jointConfiguration h (fun ν => Ch07.speciesConfiguration h S ν) = S := by
  ext p
  simp only [jointConfiguration, Ch07.speciesConfiguration, Finset.mem_image,
    Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
  aesop

lemma tensor_kets (h : ℕ) (Ss : σ → Ch07.Occupation h) :
    tensorVector h (fun ν => A02.ket (Ss ν)) = A02.ket (jointConfiguration h Ss) := by
  apply (A02.coordinates (Mode σ h)).injective
  funext S
  simp only [tensorVector, LinearEquiv.apply_symm_apply, A02.coordinates_ket]
  by_cases he : S = jointConfiguration h Ss
  · subst S
    simp [A02.ket_apply, species_joint_configuration]
  · have hn : ¬ ∀ ν, Ch07.speciesConfiguration h S ν = Ss ν := by
      intro ha
      apply he
      rw [← joint_species_configuration h S]
      congr 1
      funext ν
      exact ha ν
    push Not at hn
    obtain ⟨ν, hν⟩ := hn
    rw [ite_eq_right he]
    apply Finset.prod_eq_zero (Finset.mem_univ ν)
    simp [A02.ket_apply, hν]

lemma tensor_inner (h : ℕ) (vs ws : σ → Ch07.FockSpace h) :
    inner ℂ (tensorVector h vs) (tensorVector h ws) = ∏ ν, inner ℂ (vs ν) (ws ν) := by sorry

lemma rho_tensor (h : ℕ) (ν : σ) (m : ℤ) (vs : σ → Ch07.FockSpace h) :
    rho h ν m (tensorVector h vs) =
      tensorVector h (Function.update vs ν (Ch09.rho h m (vs ν))) := by sorry

lemma word_tensor (h : ℕ) (Ns : σ → ℤ) (hN : admissible h Ns) (parts : σ → List ℕ) :
    wordState h Ns parts = tensorVector h (fun ν => Ch11.wordState h (Ns ν) (hN ν) (parts ν)) := by sorry

lemma annihilation_car (h : ℕ) (i j : Mode σ h) :
    A02.anticommutator (annihilation h i.1 i.2) (annihilation h j.1 j.2) = 0 := by
  simpa only [annihilation, Prod.mk.eta] using Ch04.annihilation_car i j

lemma creation_car (h : ℕ) (i j : Mode σ h) :
    A02.anticommutator (creation h i.1 i.2) (creation h j.1 j.2) = 0 := by
  simpa only [creation, Prod.mk.eta] using Ch04.creation_car i j

lemma mixed_car (h : ℕ) (i j : Mode σ h) :
    A02.anticommutator (annihilation h i.1 i.2) (creation h j.1 j.2) =
      (if i=j then (1 : ℂ) else 0) • (1 : Operators σ h) := by
  simpa only [annihilation, creation, Prod.mk.eta] using Ch04.mixed_car i j

/-- The preceding-species parity occurs twice in this same-species even hop. -/
lemma hopping_tensor (h : ℕ) (ν : σ) (p k : Ch01.Band (2*h)) (vs : σ → Ch07.FockSpace h) :
    Ch04.hopping (ν,p) (ν,k) (tensorVector h vs) =
      tensorVector h (Function.update vs ν (Ch04.hopping p k (vs ν))) := by sorry

lemma preceding_count_split (h : ℕ) (ν : σ) (k : Ch01.Band (2*h)) (S : Occupation σ h) :
    Ch04.precedingCount (ν,k) S =
      (∑ η ∈ Finset.univ.filter (· < ν), (Ch07.speciesConfiguration h S η).card) +
        Ch04.precedingCount k (Ch07.speciesConfiguration h S ν) := by sorry

lemma creation_adjoint (h : ℕ) (ν : σ) (k : Ch01.Band (2*h)) :
    LinearMap.adjoint (annihilation h ν k) = creation h ν k := by
  exact (Ch04.creation_eq_adjoint (ν,k)).symm

lemma rho_adjoint (h : ℕ) (ν : σ) (m : ℤ) :
    LinearMap.adjoint (rho h ν m) = rho h ν (-m) := by sorry

lemma rho_cross_commute (h : ℕ) (ν η : σ) (hne : ν ≠ η) (m n : ℤ) :
    A02.commutator (rho h ν m) (rho h η n) = 0 := by sorry

lemma rho_positive_commute (h : ℕ) (ν : σ) (m n : ℕ) :
    A02.commutator (rho h ν (m : ℤ)) (rho h ν (n : ℤ)) = 0 := by sorry

lemma rho_budget_map (h : ℕ) (ν : σ) (m : ℤ) (Ns : σ → ℤ) (K : ℕ)
    (v : FockSpace σ h) (hv : v ∈ jointBudget h Ns K) :
    rho h ν m v ∈ Ch07.speciesBudget h Ns ((K : ℤ)+m) := by sorry

lemma rho_lowering_budget_zero (h : ℕ) (hh : 0 < h) (ν : σ) (m K : ℕ)
    (hm : K < m) (Ns : σ → ℤ) (v : FockSpace σ h) (hv : v ∈ jointBudget h Ns K) :
    rho h ν (-(m : ℤ)) v = 0 := by sorry

lemma ground_mem_budget (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (hN : admissible h Ns) (K : ℕ) :
    groundKet h Ns ∈ jointBudget h Ns K := by
  apply (Ch07.species_budget_ket h (groundConfiguration h Ns) Ns (K : ℤ)).mpr
  have hc : ∀ ν : σ, Ch07.speciesConfiguration h (groundConfiguration h Ns) ν = Ch07.groundConfiguration h (Ns ν) := by
    intro ν
    exact species_joint_configuration h _ ν
  constructor
  · intro ν
    rw [hc ν]
    exact Ch07.ground_configuration_charge h hh (Ns ν) (hN ν)
  · unfold Ch07.totalExcitation
    simp only [hc, Ch07.ground_configuration_excitation h hh _ (hN _)]
    simp

lemma ground_ne_zero (h : ℕ) (Ns : σ → ℤ) : groundKet h Ns ≠ 0 := by
  exact A02.ket_ne_zero (groundConfiguration h Ns)

lemma word_mem_budget (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (hN : admissible h Ns)
    (parts : σ → List ℕ) (K : ℕ) (hE : ∑ ν, (parts ν).sum ≤ K) :
    wordState h Ns parts ∈ jointBudget h Ns K := by sorry

lemma partition_mem_budget (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : admissible h Ns) (K : ℕ) (p : JointPartitions σ K) :
    partitionState h Ns p ∈ jointBudget h Ns K := by sorry

omit [LinearOrder σ] in
lemma joint_normalization_positive (K : ℕ) (p : JointPartitions σ K) :
    0 < jointNormalization p := by
  unfold jointNormalization
  apply Finset.prod_pos
  intro ν _
  exact Ch11.hall_factor_positive (p.val ν).2.parts (fun m hm => (p.val ν).2.parts_pos hm)

lemma partition_gram (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : admissible h Ns) (K : ℕ) (hR2 : r2 h K Ns) (p q : JointPartitions σ K) :
    inner ℂ (partitionState h Ns p) (partitionState h Ns q) =
      if p=q then (jointNormalization p : ℂ) else 0 := by sorry

lemma partition_ne_zero (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : admissible h Ns) (K : ℕ) (hR2 : r2 h K Ns) (p : JointPartitions σ K) :
    partitionState h Ns p ≠ 0 := by sorry

lemma partition_spanning (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : admissible h Ns) (K : ℕ) (hR2 : r2 h K Ns) :
    Submodule.span ℂ (Set.range (partitionState h Ns (K := K))) = jointBudget h Ns K := by sorry

lemma partition_basis (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : admissible h Ns) (K : ℕ) (hR2 : r2 h K Ns) :
    ∃ b : Module.Basis (JointPartitions σ K) ℂ (jointBudget h Ns K),
      ∀ p, (b p : FockSpace σ h) = partitionState h Ns p := by sorry

lemma charge_budget (h : ℕ) (ν : σ) (Ns : σ → ℤ) (K : ℕ)
    (v : FockSpace σ h) (hv : v ∈ jointBudget h Ns K) :
    chargeObservable h ν v = (Ns ν : ℂ) • v := by
  change v ∈ A03.coordinateSpace _ at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨S, hS, rfl⟩
    change (∀ η, Ch07.relativeCharge h (Ch07.speciesConfiguration h S η) = Ns η) ∧ _ at hS
    rw [chargeObservable, A03.diagonal_ket, hS.1 ν]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy, smul_add]
  | smul a x _ hx => simp only [map_smul, hx, smul_comm a]

end Bosonize.A05
