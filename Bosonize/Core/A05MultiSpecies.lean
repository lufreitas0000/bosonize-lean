module

public import Bosonize.Core.Ch11HaldaneCompleteness
public import Mathlib.Order.Prod.Lex.Basic

/-! A05 multispecies prerequisites for CH13. Verified finite constructions and proofs.
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
    inner ℂ (tensorVector h vs) (tensorVector h ws) = ∏ ν, inner ℂ (vs ν) (ws ν) := by
  classical
  let e : Occupation σ h ≃ (σ → Ch07.Occupation h) :=
    { toFun := fun S ν => Ch07.speciesConfiguration h S ν
      invFun := jointConfiguration h
      left_inv := joint_species_configuration h
      right_inv := fun Ss => by funext ν; exact species_joint_configuration h Ss ν }
  simp only [PiLp.inner_apply, RCLike.inner_apply']
  change (∑ S : Occupation σ h,
    star (∏ ν, vs ν (Ch07.speciesConfiguration h S ν)) *
      (∏ ν, ws ν (Ch07.speciesConfiguration h S ν))) =
    ∏ ν, ∑ T : Ch07.Occupation h, star (vs ν T) * ws ν T
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv e
  intro S
  simp only [e, Equiv.coe_fn_mk, star_prod, Finset.prod_mul_distrib]

lemma preceding_count_split (h : ℕ) (ν : σ) (k : Ch01.Band (2*h)) (S : Occupation σ h) :
    Ch04.precedingCount (ν,k) S =
      (∑ η ∈ Finset.univ.filter (· < ν), (Ch07.speciesConfiguration h S η).card) +
        Ch04.precedingCount k (Ch07.speciesConfiguration h S ν) := by
  have hmem (η : σ) (l : Ch01.Band (2*h)) :
      l ∈ Ch07.speciesConfiguration h S η ↔ (η,l) ∈ S := by
    simp only [Ch07.speciesConfiguration, Finset.mem_image, Finset.mem_filter]
    aesop
  have hfiber (η : σ) :
      ((S.filter (· < (ν,k))).filter (fun a => a.1=η)) =
        ((Ch07.speciesConfiguration h S η).filter (fun l => (η,l)<(ν,k))).image (fun l => (η,l)) := by
    ext a
    rcases a with ⟨α,l⟩
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨hS, hlt⟩, rfl⟩
      exact ⟨l, ⟨(hmem _ _).mpr hS, hlt⟩, rfl⟩
    · rintro ⟨b, ⟨hb, hlt⟩, he⟩
      cases he
      exact ⟨⟨(hmem _ _).mp hb, hlt⟩, rfl⟩
  have hc (η : σ) :
      ((S.filter (· < (ν,k))).filter (fun a => a.1=η)).card =
        (if η<ν then (Ch07.speciesConfiguration h S η).card else 0) +
          (if η=ν then Ch04.precedingCount k (Ch07.speciesConfiguration h S ν) else 0) := by
    rw [hfiber, Finset.card_image_of_injective _ (by intro a b he; exact Prod.mk.inj he |>.2)]
    by_cases hlt : η<ν
    · have hne : η≠ν := ne_of_lt hlt
      simp [mode_lt_iff, hlt, hne]
    · by_cases he : η=ν
      · subst η
        simp [mode_lt_iff, Ch04.precedingCount]
      · simp [mode_lt_iff, hlt, he]
  unfold Ch04.precedingCount
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ) (by intro a ha; exact Finset.mem_univ a.1)]
  simp only [hc, Finset.sum_add_distrib]
  simp [Finset.sum_filter]
  rfl

/-- The preceding-species parity occurs twice in this same-species even hop. -/
lemma hopping_tensor (h : ℕ) (ν : σ) (p k : Ch01.Band (2*h)) (vs : σ → Ch07.FockSpace h) :
    Ch04.hopping (ν,p) (ν,k) (tensorVector h vs) =
      tensorVector h (Function.update vs ν (Ch04.hopping p k (vs ν))) := by
  let T : MultilinearMap ℂ (fun _ : σ => Ch07.FockSpace h) (FockSpace σ h) := by
    have hf : ∀ [DecidableEq σ] (m : σ → Ch07.FockSpace h) (i : σ) (x : Ch07.FockSpace h)
        (f : σ → Ch07.Occupation h),
        (∏ η, Function.update m i x η (f η)) =
          x (f i) *
            ∏ η ∈ (Finset.univ : Finset σ).erase i, m η (f η) := by
      intro decEq
      let _ := decEq
      intro m i x f
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      simp only [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro η hη
      rw [Function.update_of_ne (Finset.mem_erase.mp hη).1]
    refine { toFun := tensorVector h, map_update_add' := ?_, map_update_smul' := ?_ }
    · intro decEq
      let _ := decEq
      intro m i x y
      apply (A02.coordinates (Mode σ h)).injective
      funext S
      simp only [map_add, tensorVector, LinearEquiv.apply_symm_apply, Pi.add_apply]
      rw [hf, hf, hf]
      simp only [PiLp.add_apply]
      ring
    · intro decEq
      let _ := decEq
      intro m i c x
      apply (A02.coordinates (Mode σ h)).injective
      funext S
      simp only [map_smul, tensorVector, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul]
      rw [hf, hf]
      simp only [PiLp.smul_apply, smul_eq_mul]
      ring
  let : DecidableEq (Ch01.Band (2*h)) := (inferInstance : LinearOrder (Ch01.Band (2*h))).toDecidableEq
  have hket (Ss : σ → Ch07.Occupation h) :
      Ch04.hopping (ν,p) (ν,k) (tensorVector h (fun η => A02.ket (Ss η))) =
        tensorVector h (Function.update (fun η => A02.ket (Ss η)) ν (Ch04.hopping p k (A02.ket (Ss ν)))) := by
    have hkets (ss : σ → Ch07.Occupation h) :
        tensorVector h (fun η => A02.ket (ss η)) = A02.ket (jointConfiguration h ss) := by
      apply (A02.coordinates (Mode σ h)).injective
      funext S
      simp only [tensorVector, LinearEquiv.apply_symm_apply, A02.coordinates_ket]
      by_cases he : S=jointConfiguration h ss
      · subst S
        simp [A02.ket_apply, species_joint_configuration]
      · have hn : ¬ ∀ η, Ch07.speciesConfiguration h S η = ss η := by
          intro ha
          apply he
          rw [← joint_species_configuration h S]
          congr 1
          funext η
          exact ha η
        push Not at hn
        obtain ⟨η,hη⟩ := hn
        rw [ite_eq_right he]
        apply Finset.prod_eq_zero (Finset.mem_univ η)
        simp [A02.ket_apply, hη]
    have hjoin (ss : σ → Ch07.Occupation h) (η : σ) (l : Ch01.Band (2*h)) :
        (η,l) ∈ jointConfiguration h ss ↔ l ∈ ss η := by simp [jointConfiguration]
    have hmem (S : Occupation σ h) (η : σ) (l : Ch01.Band (2*h)) :
        l ∈ Ch07.speciesConfiguration h S η ↔ (η,l) ∈ S := by
      simp only [Ch07.speciesConfiguration, Finset.mem_image, Finset.mem_filter]
      aesop
    have herase (S : Occupation σ h) :
        Ch07.speciesConfiguration h (S.erase (ν,k)) =
          Function.update (Ch07.speciesConfiguration h S) ν ((Ch07.speciesConfiguration h S ν).erase k) := by
      funext η
      ext l
      by_cases he : η=ν
      · subst η
        simp only [hmem, Function.update_self, Finset.mem_erase, ne_eq, Prod.mk.injEq, true_and]
      · simp only [hmem, Function.update_of_ne he, Finset.mem_erase, ne_eq, Prod.mk.injEq, he, false_and, not_false_eq_true, true_and]
    have hcfig : jointConfiguration h (Function.update Ss ν (insert p ((Ss ν).erase k))) =
        insert (ν,p) ((jointConfiguration h Ss).erase (ν,k)) := by
      ext ⟨η,l⟩
      by_cases he : η=ν
      · subst η
        simp only [hjoin, Function.update_self, Finset.mem_insert, Finset.mem_erase,
          Prod.mk.injEq, true_and]
        simp only [ne_eq, Prod.mk.injEq, true_and]
      · simp [hjoin, he]
    rw [hkets]
    change Ch04.hopping (ν,p) (ν,k) (A02.ket (jointConfiguration h Ss)) =
      T (Function.update (fun η => A02.ket (Ss η)) ν (Ch04.hopping p k (A02.ket (Ss ν))))
    by_cases hpk : p=k
    · subst p
      rw [Ch04.hopping_diagonal, Ch04.number_ket, Ch04.hopping_diagonal, Ch04.number_ket,
        T.map_update_smul]
      simp only [hjoin]
      have hU : Function.update (fun η => A02.ket (Ss η)) ν (A02.ket (Ss ν)) = (fun η => A02.ket (Ss η)) := Function.update_eq_self _ _
      rw [hU]
      change _ = _ • tensorVector h (fun η => A02.ket (Ss η))
      rw [hkets]
    · by_cases hk : k ∈ Ss ν
      · by_cases hp : p ∈ Ss ν
        · rw [Ch04.hopping_blocked p k (Ss ν) (Or.inr ⟨hpk,hp⟩), T.map_update_zero]
          exact Ch04.hopping_blocked (ν,p) (ν,k) _ (Or.inr ⟨by simpa using hpk, (hjoin _ _ _).mpr hp⟩)
        · rw [Ch04.hopping_ket p k (Ss ν) hpk hp hk,
            T.map_update_smul, Ch04.hopping_ket (ν,p) (ν,k) _ (by simpa using hpk)
              (by simpa only [hjoin] using hp) ((hjoin _ _ _).mpr hk)]
          have hcoef : Ch04.fermionSign (ν,k) (jointConfiguration h Ss) *
              Ch04.fermionSign (ν,p) ((jointConfiguration h Ss).erase (ν,k)) =
              Ch04.fermionSign k (Ss ν) * Ch04.fermionSign p ((Ss ν).erase k) := by
            simp only [Ch04.fermionSign]
            rw [preceding_count_split, preceding_count_split, herase]
            simp only [species_joint_configuration, Function.update_self]
            have hsum : (∑ η ∈ Finset.univ.filter (· < ν),
                (Function.update (Ch07.speciesConfiguration h (jointConfiguration h Ss)) ν
                  ((Ss ν).erase k) η).card) =
                ∑ η ∈ Finset.univ.filter (· < ν), (Ss η).card := by
              apply Finset.sum_congr rfl
              intro η hη
              rw [Function.update_of_ne (ne_of_lt (Finset.mem_filter.mp hη).2)]
              rw [species_joint_configuration]
            rw [hsum, pow_add, pow_add]
            have hc : ((-1 : ℂ)^(∑ η ∈ Finset.univ.filter (· < ν), (Ss η).card))^2=1 := by
              rw [← pow_mul, Nat.mul_comm, pow_mul]
              norm_num
            calc
              _ = ((-1 : ℂ)^(∑ η ∈ Finset.univ.filter (· < ν), (Ss η).card))^2 *
                  ((-1 : ℂ)^Ch04.precedingCount k (Ss ν) * (-1 : ℂ)^Ch04.precedingCount p ((Ss ν).erase k)) := by ring
              _ = _ := by rw [hc, one_mul]
          rw [hcoef]
          congr 1
          have hU : Function.update (fun η => A02.ket (Ss η)) ν (A02.ket (insert p ((Ss ν).erase k))) =
              (fun η => A02.ket (Function.update Ss ν (insert p ((Ss ν).erase k)) η)) := by
            funext η
            by_cases he : η=ν <;> simp [he, Function.update_of_ne]
          rw [hU]
          change _ = tensorVector h _
          rw [hkets, hcfig]
      · rw [Ch04.hopping_blocked p k (Ss ν) (Or.inl hk), T.map_update_zero]
        exact Ch04.hopping_blocked (ν,p) (ν,k) _ (Or.inl (by simpa only [hjoin] using hk))
  let ls : σ → Module.End ℂ (Ch07.FockSpace h) :=
    Function.update (fun _ => 1) ν (Ch04.hopping p k)
  have hls (ws : σ → Ch07.FockSpace h) :
      (fun η => ls η (ws η)) = Function.update ws ν (Ch04.hopping p k (ws ν)) := by
    funext η
    by_cases he : η=ν
    · subst η
      simp [ls]
    · simp [ls, he]
  have heq : (Ch04.hopping (ν,p) (ν,k)).compMultilinearMap T = T.compLinearMap ls := by
    apply Module.Basis.ext_multilinear (fun _ : σ => A02.occupationBasis (Ch01.Band (2*h)))
    intro Ss
    change Ch04.hopping (ν,p) (ν,k) (tensorVector h (fun η => A02.ket (Ss η))) =
      tensorVector h (fun η => ls η (A02.ket (Ss η)))
    rw [hls]
    exact hket Ss
  have hw := congrArg (fun F : MultilinearMap ℂ (fun _ : σ => Ch07.FockSpace h) (FockSpace σ h) => F vs) heq
  change Ch04.hopping (ν,p) (ν,k) (tensorVector h vs) = tensorVector h (fun η => ls η (vs η)) at hw
  rw [hls] at hw
  exact hw

lemma rho_tensor (h : ℕ) (ν : σ) (m : ℤ) (vs : σ → Ch07.FockSpace h) :
    rho h ν m (tensorVector h vs) =
      tensorVector h (Function.update vs ν (Ch09.rho h m (vs ν))) := by
  have hf (x : Ch07.FockSpace h) (S : Occupation σ h) :
      (∏ η, Function.update vs ν x η (Ch07.speciesConfiguration h S η)) =
        x (Ch07.speciesConfiguration h S ν) *
          ∏ η ∈ (Finset.univ : Finset σ).erase ν, vs η (Ch07.speciesConfiguration h S η) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ν)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro η hη
    rw [Function.update_of_ne (Finset.mem_erase.mp hη).1]
  let L : Ch07.FockSpace h →ₗ[ℂ] FockSpace σ h := {
    toFun := fun x => tensorVector h (Function.update vs ν x)
    map_add' := by
      intro x y
      apply (A02.coordinates (Mode σ h)).injective
      funext S
      simp only [map_add, tensorVector, LinearEquiv.apply_symm_apply, Pi.add_apply]
      rw [hf, hf, hf]
      simp only [PiLp.add_apply]
      ring
    map_smul' := by
      intro c x
      apply (A02.coordinates (Mode σ h)).injective
      funext S
      simp only [map_smul, tensorVector, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul]
      rw [hf, hf]
      simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring }
  change rho h ν m (tensorVector h vs) = L (Ch09.rho h m (vs ν))
  simp only [rho, Ch09.rho_valid_pairs, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro z hz
  exact hopping_tensor h ν z.1 z.2 vs

lemma word_tensor (h : ℕ) (Ns : σ → ℤ) (hN : admissible h Ns) (parts : σ → List ℕ) :
    wordState h Ns parts = tensorVector h (fun ν => Ch11.wordState h (Ns ν) (hN ν) (parts ν)) := by
  classical
  have hs (ν : σ) (xs : List ℕ) (vs : σ → Ch07.FockSpace h) :
      ((xs.map (fun m : ℕ => rho h ν (m : ℤ))).prod) (tensorVector h vs) =
        tensorVector h (Function.update vs ν
          (((xs.map (fun m : ℕ => Ch09.rho h (m : ℤ))).prod) (vs ν))) := by
    induction xs generalizing vs with
    | nil => simp
    | cons m xs ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [ih, rho_tensor]
      simp
  let g : σ → Ch07.FockSpace h := fun ν => Ch07.groundKet h (Ns ν) (hN ν)
  let op : σ → Operators σ h := fun ν =>
    ((parts ν).map (fun m : ℕ => rho h ν (m : ℤ))).prod
  let w : σ → Ch07.FockSpace h := fun ν =>
    (((parts ν).map (fun m : ℕ => Ch09.rho h (m : ℤ))).prod) (g ν)
  have ho (ls : List σ) (hn : ls.Nodup) :
      ((ls.map op).prod) (tensorVector h g) =
        tensorVector h (fun ν => if ν ∈ ls then w ν else g ν) := by
    induction ls with
    | nil => simp
    | cons ν ls ih =>
      obtain ⟨hν, hls⟩ := List.nodup_cons.mp hn
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [ih hls]
      change (((parts ν).map (fun m : ℕ => rho h ν (m : ℤ))).prod)
        (tensorVector h (fun η => if η ∈ ls then w η else g η)) = _
      rw [hs]
      congr 1
      funext η
      by_cases he : η = ν
      · subst η
        simp [hν, w]
      · simp [he]
  have hg : tensorVector h g = groundKet h Ns := by
    simpa only [g, Ch07.groundKet, groundKet, groundConfiguration] using
      tensor_kets h (fun ν => Ch07.groundConfiguration h (Ns ν))
  unfold wordState creatorWord
  simp only [Ch11.wordState, Ch11.creatorWord, bind_pure_comp]
  change (((Finset.univ : Finset σ).sort (· ≤ ·)).map
    (fun ν => (((parts ν).map (fun m : ℕ => (m : ℤ))).map (rho h ν)).prod)).prod
    (groundKet h Ns) = tensorVector h (fun ν =>
      (((parts ν).map (fun m : ℕ => (m : ℤ))).map (Ch09.rho h)).prod
        (Ch07.groundKet h (Ns ν) (hN ν)))
  simp only [List.map_map, Function.comp_def]
  rw [← hg]
  have hh := ho ((Finset.univ : Finset σ).sort (· ≤ ·)) (Finset.sort_nodup _ _)
  simpa only [op, w, g, Finset.mem_sort, Finset.mem_univ, ite_true] using hh

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

lemma creation_adjoint (h : ℕ) (ν : σ) (k : Ch01.Band (2*h)) :
    LinearMap.adjoint (annihilation h ν k) = creation h ν k := by
  exact (Ch04.creation_eq_adjoint (ν,k)).symm

lemma rho_adjoint (h : ℕ) (ν : σ) (m : ℤ) :
    LinearMap.adjoint (rho h ν m) = rho h ν (-m) := by
  unfold rho
  simp only [map_sum, Ch04.hopping_adjoint]
  apply Finset.sum_bij (fun z _ => (z.2,z.1))
  · intro z hz
    rw [A04.mem_valid_pairs] at hz ⊢
    omega
  · intro z hz w hw he
    exact Prod.swap_injective he
  · intro z hz
    refine ⟨(z.2,z.1), ?_, rfl⟩
    rw [A04.mem_valid_pairs] at hz ⊢
    omega
  · intro z hz
    rfl

lemma rho_cross_commute (h : ℕ) (ν η : σ) (hne : ν ≠ η) (m n : ℤ) :
    A02.commutator (rho h ν m) (rho h η n) = 0 := by
  have hsum (s t : Finset (Ch01.Band (2*h) × Ch01.Band (2*h))) :
      A02.commutator (∑ z ∈ s, Ch04.hopping (ν,z.1) (ν,z.2))
        (∑ z ∈ t, Ch04.hopping (η,z.1) (η,z.2)) =
      ∑ z ∈ s, ∑ w ∈ t,
        A02.commutator (Ch04.hopping (ν,z.1) (ν,z.2))
          (Ch04.hopping (η,w.1) (η,w.2)) := by
    simp only [A02.commutator, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
  unfold rho
  rw [hsum]
  have he (a b : Ch01.Band (2*h)) : (ν,a) ≠ (η,b) := by
    intro he
    exact hne (congrArg Prod.fst he)
  simp only [Ch04.bilinear_commutator, ite_eq_right (he _ _), zero_smul, sub_self,
    Finset.sum_const_zero]

lemma rho_positive_commute (h : ℕ) (ν : σ) (m n : ℕ) :
    A02.commutator (rho h ν (m : ℤ)) (rho h ν (n : ℤ)) = 0 := by
  let E (a : ℤ) : Matrix (Mode σ h) (Mode σ h) ℂ :=
    fun i j => if i.1=ν then if j.1=ν then A04.shift (2*h) a i.2 j.2 else 0 else 0
  have hd (a : ℤ) : rho h ν a =
      ∑ p, ∑ k, A04.shift (2*h) a p k • Ch04.hopping (ν,p) (ν,k) := by
    simp only [rho, A04.shift, A04.validPairs, Finset.sum_filter,
      ite_smul, one_smul, zero_smul]
    exact Fintype.sum_prod_type _
  have hl (a : ℤ) : rho h ν a = A04.dGamma (E a) := by
    rw [hd]
    simp [A04.dGamma, E, Fintype.sum_prod_type]
  have hm (a b : ℤ) (ha : 0≤a) (hb : 0≤b) (i j : Mode σ h) :
      (∑ k : Mode σ h, E a i k * E b k j) = E (a+b) i j := by
    simp only [E, Fintype.sum_prod_type]
    by_cases hi : i.1=ν <;> by_cases hj : j.1=ν
    · simp only [hi, hj, ite_true]
      have hs := congrFun (congrFun (A04.shift_mul_nonnegative (2*h) a b ha hb) i.2) j.2
      simpa [Matrix.mul_apply] using hs
    · simp [hi, hj]
    · simp [hi]
    · simp [hi]
  rw [hl, hl, A04.dGamma_commutator]
  rw [← A04.dGamma_zero (ι := Mode σ h)]
  congr 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.zero_apply, Matrix.mul_apply]
  rw [hm _ _ (by omega) (by omega), hm _ _ (by omega) (by omega)]
  simp [add_comm]

lemma rho_budget_map (h : ℕ) (ν : σ) (m : ℤ) (Ns : σ → ℤ) (K : ℕ)
    (v : FockSpace σ h) (hv : v ∈ jointBudget h Ns K) :
    rho h ν m v ∈ Ch07.speciesBudget h Ns ((K : ℤ)+m) := by
  change v ∈ A03.coordinateSpace _ at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, hS, rfl⟩ := hx
    change (∀ η, Ch07.relativeCharge h (Ch07.speciesConfiguration h S η) = Ns η) ∧
      Ch07.totalExcitation h S ≤ (K : ℤ) at hS
    let Ss := fun η => Ch07.speciesConfiguration h S η
    let vs := fun η => A02.ket (Ss η)
    have hk : A02.ket S = tensorVector h vs := by
      rw [tensor_kets, joint_species_configuration]
    rw [hk, rho_tensor]
    let out := Ch09.rho h m (vs ν)
    have ho : out ∈ Ch07.fixedBudget h (Ns ν) (Ch07.excitationEnergy h (Ss ν) + m) :=
      Ch09.rho_budget_map h m (Ns ν) (Ch07.excitationEnergy h (Ss ν)) _
        ((Ch07.ket_mem_fixed_budget h _ _ _).mpr ⟨hS.1 ν, le_rfl⟩)
    let : DecidableEq (Mode σ h) := instDecidableEqProd
    apply (A03.coordinate_space_support _ _).mpr
    intro T hT
    change (∏ η, (Function.update vs ν out) η (Ch07.speciesConfiguration h T η)) = 0
    by_contra hn
    have hcoeff (η : σ) : (Function.update vs ν out) η (Ch07.speciesConfiguration h T η) ≠ 0 := by
      intro hz
      exact hn (Finset.prod_eq_zero (Finset.mem_univ η) hz)
    have hν : Ch07.relativeCharge h (Ch07.speciesConfiguration h T ν) = Ns ν ∧
        Ch07.excitationEnergy h (Ch07.speciesConfiguration h T ν) ≤ Ch07.excitationEnergy h (Ss ν)+m := by
      by_contra hbad
      have hz := (A03.coordinate_space_support _ out).mp ho (Ch07.speciesConfiguration h T ν) hbad
      exact hcoeff ν (by simpa [A02.coordinates, out] using hz)
    have he (η : σ) (hην : η ≠ ν) : Ch07.speciesConfiguration h T η = Ss η := by
      have hc := hcoeff η
      simp only [Function.update_of_ne hην, vs, A02.ket_apply] at hc
      by_contra hne
      exact hc (by simp [hne])
    apply hT
    constructor
    · intro η
      by_cases hην : η = ν
      · subst η
        exact hν.1
      · rw [he η hην]
        exact hS.1 η
    · change (∑ η : σ, Ch07.excitationEnergy h (Ch07.speciesConfiguration h T η)) ≤ (K : ℤ)+m
      have hbound : (∑ η : σ, Ch07.excitationEnergy h (Ch07.speciesConfiguration h T η)) ≤
          ∑ η : σ, (Ch07.excitationEnergy h (Ss η) + if η=ν then m else 0) := by
        apply Finset.sum_le_sum
        intro η _
        by_cases hην : η=ν
        · subst η
          simpa using hν.2
        · rw [he η hην]
          simp [hην]
      have hsum : (∑ η : σ, (Ch07.excitationEnergy h (Ss η) + if η=ν then m else 0)) =
          Ch07.totalExcitation h S+m := by
        simp [Finset.sum_add_distrib, Ss, Ch07.totalExcitation]
      rw [hsum] at hbound
      omega
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa using Submodule.smul_mem _ a hx

lemma rho_lowering_budget_zero (h : ℕ) (hh : 0 < h) (ν : σ) (m K : ℕ)
    (hm : K < m) (Ns : σ → ℤ) (v : FockSpace σ h) (hv : v ∈ jointBudget h Ns K) :
    rho h ν (-(m : ℤ)) v = 0 := by
  have hv' := rho_budget_map h ν (-(m : ℤ)) Ns K v hv
  rw [Ch07.species_budget_negative h hh Ns ((K : ℤ) + -(m : ℤ)) (by omega)] at hv'
  exact (Submodule.mem_bot ℂ).mp hv'

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
    wordState h Ns parts ∈ jointBudget h Ns K := by
  classical
  have hs (ν : σ) (xs : List ℕ) (J : ℕ) (v : FockSpace σ h)
      (hv : v ∈ jointBudget h Ns J) :
      (((xs.map (fun m : ℕ => rho h ν (m : ℤ))).prod) v) ∈
        jointBudget h Ns (J + xs.sum) := by
    induction xs with
    | nil => simpa using hv
    | cons m xs ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.sum_cons]
      have ht := rho_budget_map h ν (m : ℤ) Ns (J + xs.sum)
        (((xs.map (fun n : ℕ => rho h ν (n : ℤ))).prod) v) ih
      simpa only [jointBudget, Nat.cast_add, add_assoc, add_comm, add_left_comm] using ht
  let op : σ → Operators σ h := fun ν =>
    ((parts ν).map (fun m : ℕ => rho h ν (m : ℤ))).prod
  have ho (ls : List σ) :
      ((ls.map op).prod) (groundKet h Ns) ∈
        jointBudget h Ns ((ls.map (fun ν => (parts ν).sum)).sum) := by
    induction ls with
    | nil => simpa using ground_mem_budget h hh Ns hN 0
    | cons ν ls ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.sum_cons]
      simpa only [Nat.add_comm] using hs ν (parts ν)
        ((ls.map (fun η => (parts η).sum)).sum) (((ls.map op).prod) (groundKet h Ns)) ih
  have he : ((((Finset.univ : Finset σ).sort (· ≤ ·)).map
      (fun ν => (parts ν).sum)).sum) = ∑ ν, (parts ν).sum := by
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq]
    rfl
  have ht := ho ((Finset.univ : Finset σ).sort (· ≤ ·))
  rw [he] at ht
  have hsub : jointBudget h Ns (∑ ν, (parts ν).sum) ≤ jointBudget h Ns K := by
    unfold jointBudget Ch07.speciesBudget
    apply @A03.coordinate_space_mono (σ × Ch01.Band (2*h)) _ instDecidableEqProd
    intro S hS
    exact ⟨hS.1, le_trans hS.2 (by exact_mod_cast hE)⟩
  have hz := hsub ht
  unfold wordState creatorWord
  simp only [bind_pure_comp]
  change (((Finset.univ : Finset σ).sort (· ≤ ·)).map
    (fun ν => (((parts ν).map (fun m : ℕ => (m : ℤ))).map (rho h ν)).prod)).prod
      (groundKet h Ns) ∈ jointBudget h Ns K
  simpa only [op, List.map_map, Function.comp_def] using hz

lemma partition_mem_budget (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : admissible h Ns) (K : ℕ) (p : JointPartitions σ K) :
    partitionState h Ns p ∈ jointBudget h Ns K := by
  apply word_mem_budget h hh Ns hN _ K
  simpa only [Ch11.partition_list_sum] using p.property

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
      if p=q then (jointNormalization p : ℂ) else 0 := by
  unfold partitionState
  rw [word_tensor h Ns hN, word_tensor h Ns hN, tensor_inner]
  have hg : ∀ ν : σ,
      inner ℂ (Ch11.wordState h (Ns ν) (hN ν) (Ch11.partitionList (p.val ν).2))
        (Ch11.wordState h (Ns ν) (hN ν) (Ch11.partitionList (q.val ν).2)) =
      if p.val ν = q.val ν then (Ch11.partitionNormalization (p.val ν).2 : ℂ) else 0 := by
    intro ν
    exact Ch11.budget_partition_gram h hh (Ns ν) (hN ν) K (hR2 ν) (p.val ν) (q.val ν)
  simp_rw [hg]
  by_cases he : p = q
  · subst q
    simp [jointNormalization, Nat.cast_prod]
  · rw [ite_eq_right he]
    have hn : ¬ ∀ ν, p.val ν = q.val ν := by
      intro ha
      apply he
      apply Subtype.ext
      funext ν
      exact ha ν
    push Not at hn
    obtain ⟨ν, hν⟩ := hn
    apply Finset.prod_eq_zero (Finset.mem_univ ν)
    exact ite_eq_right hν

lemma partition_ne_zero (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : admissible h Ns) (K : ℕ) (hR2 : r2 h K Ns) (p : JointPartitions σ K) :
    partitionState h Ns p ≠ 0 := by
  intro hz
  have hg := partition_gram h hh Ns hN K hR2 p p
  rw [hz] at hg
  simp only [inner_zero_left, ite_true] at hg
  have hp := joint_normalization_positive K p
  exact (Nat.cast_ne_zero.mpr (by omega) : (jointNormalization p : ℂ) ≠ 0) hg.symm

lemma partition_spanning (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : admissible h Ns) (K : ℕ) (hR2 : r2 h K Ns) :
    Submodule.span ℂ (Set.range (partitionState h Ns (K := K))) = jointBudget h Ns K := by
  change ∀ ν, Ch07.admissible h (Ns ν) at hN
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    exact partition_mem_budget h hh Ns hN K p
  · change Submodule.span ℂ (A02.ket '' {S | (∀ ν, Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) = Ns ν) ∧
        Ch07.totalExcitation h S ≤ (K : ℤ)}) ≤ _
    apply Submodule.span_le.mpr
    rintro _ ⟨S, ⟨hSN, hSK⟩, rfl⟩
    let Ss := fun ν => Ch07.speciesConfiguration h S ν
    let Es := fun ν => (Ch07.excitationEnergy h (Ss ν)).toNat
    have hEs (ν : σ) : (Es ν : ℤ) = Ch07.excitationEnergy h (Ss ν) :=
      Int.toNat_of_nonneg (Ch07.excitation_nonneg h hh _)
    have hsum : ∑ ν, Es ν ≤ K := by
      have hc : ((∑ ν, Es ν : ℕ) : ℤ) = Ch07.totalExcitation h S := by
        simp only [Nat.cast_sum, hEs, Ch07.totalExcitation, Ss]
      omega
    have hEK (ν : σ) : Es ν ≤ K :=
      le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ ν)) hsum
    have hMR (ν : σ) : 2*(Es ν : ℤ)+|Ns ν| ≤ (h : ℤ) := by
      have := hR2 ν
      have := hEK ν
      omega
    let bs := fun ν => Classical.choose (Ch11.fixed_energy_basis h hh (Ns ν) (hN ν) (Es ν) (hMR ν))
    have hb (ν : σ) (p : Nat.Partition (Es ν)) :
        ((bs ν) p : Ch07.FockSpace h) = Ch11.partitionState h (Ns ν) (hN ν) p :=
      Classical.choose_spec (Ch11.fixed_energy_basis h hh (Ns ν) (hN ν) (Es ν) (hMR ν)) p
    have hm (ν : σ) : A02.ket (Ss ν) ∈ Ch07.energySpace h (Ns ν) (Es ν : ℤ) := by
      apply (A03.ket_mem_coordinate_space _ _).mpr
      exact ⟨hSN ν, (hEs ν).symm⟩
    let cs := fun ν => (bs ν).repr ⟨A02.ket (Ss ν), hm ν⟩
    have hex (ν : σ) : (∑ p : Nat.Partition (Es ν), cs ν p •
        Ch11.partitionState h (Ns ν) (hN ν) p) = A02.ket (Ss ν) := by
      have he := congrArg (fun v : Ch07.energySpace h (Ns ν) (Es ν : ℤ) => (v : Ch07.FockSpace h))
        ((bs ν).sum_repr ⟨A02.ket (Ss ν), hm ν⟩)
      simpa only [Submodule.coe_sum, Submodule.coe_smul, hb, cs] using he
    let jointLabel : (∀ ν, Nat.Partition (Es ν)) → JointPartitions σ K :=
      fun ps => ⟨fun ν => ⟨⟨Es ν, Nat.lt_succ_of_le (hEK ν)⟩, ps ν⟩, hsum⟩
    have ht (ps : ∀ ν, Nat.Partition (Es ν)) :
        tensorVector h (fun ν => Ch11.partitionState h (Ns ν) (hN ν) (ps ν)) =
          partitionState h Ns (jointLabel ps) := by
      exact (word_tensor h Ns hN _).symm
    have he : A02.ket S = ∑ ps : (∀ ν, Nat.Partition (Es ν)),
        (∏ ν, cs ν (ps ν)) • partitionState h Ns (jointLabel ps) := by
      rw [← joint_species_configuration h S, ← tensor_kets]
      simp_rw [← ht]
      apply (A02.coordinates (Mode σ h)).injective
      funext T
      simp only [map_sum, map_smul, tensorVector, LinearEquiv.apply_symm_apply, Finset.sum_apply, Pi.smul_apply]
      change (∏ ν, A02.ket (Ss ν) (Ch07.speciesConfiguration h T ν)) =
        ∑ ps : (∀ ν, Nat.Partition (Es ν)), (∏ ν, cs ν (ps ν)) *
          (∏ ν, Ch11.partitionState h (Ns ν) (hN ν) (ps ν) (Ch07.speciesConfiguration h T ν))
      simp_rw [← Finset.prod_mul_distrib]
      rw [← Fintype.prod_sum (fun ν (q : Nat.Partition (Es ν)) => cs ν q *
        Ch11.partitionState h (Ns ν) (hN ν) q (Ch07.speciesConfiguration h T ν))]
      apply Finset.prod_congr rfl
      intro ν _
      have hx := congrArg (fun v : Ch07.FockSpace h => v (Ch07.speciesConfiguration h T ν)) (hex ν)
      simpa using hx.symm
    rw [he]
    apply Submodule.sum_mem
    intro ps _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨jointLabel ps, rfl⟩

lemma partition_basis (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : admissible h Ns) (K : ℕ) (hR2 : r2 h K Ns) :
    ∃ b : Module.Basis (JointPartitions σ K) ℂ (jointBudget h Ns K),
      ∀ p, (b p : FockSpace σ h) = partitionState h Ns p := by
  let v : JointPartitions σ K → jointBudget h Ns K :=
    fun p => ⟨partitionState h Ns p, partition_mem_budget h hh Ns hN K p⟩
  have hi : LinearIndependent ℂ (partitionState h Ns (K := K)) := by
    apply linearIndependent_of_ne_zero_of_inner_eq_zero
    · intro p
      exact partition_ne_zero h hh Ns hN K hR2 p
    · intro p q hpq
      rw [partition_gram h hh Ns hN K hR2 p q, ite_eq_right hpq]
  have hv : LinearIndependent ℂ v := hi.of_comp (jointBudget h Ns K).subtype
  have hs : Submodule.span ℂ (Set.range v) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff _
      (fun p => partition_mem_budget h hh Ns hN K p)).mpr
        (partition_spanning h hh Ns hN K hR2)
  refine ⟨Module.Basis.mk hv hs.ge, ?_⟩
  intro p
  rw [Module.Basis.coe_mk]

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
