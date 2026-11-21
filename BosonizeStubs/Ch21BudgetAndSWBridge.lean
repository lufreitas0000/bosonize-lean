import BosonizeStubs.Ch21CocycleAndLeakage

/-!
# Chapter 21 Bridge: Graded Energy-Budget Direct Sum, General-`h` Singlet Klein Sign, and `Ch21 → A10` Schrieffer-Wolff Instantiation

Constructive Phase B formalization closing the remaining finite-CAR and algebraic Chapter 21 gaps
identified in `docs/plans/v1-s9/v1_release_readiness_audit.md` on top of
`BosonizeStubs.Ch21CocycleAndLeakage` and frozen Core (`Bosonize.Core.*`):

1. **Graded Direct-Sum Decomposition vs. Product-Cutoff Counterexample**
   (`eq:ch21-budget-energy-sum`, `eq:ch21-not-product-cutoff`):
   - Per-species energy-graded subspaces `gradedSectorSpace h Ns es` realizing
     `⨂_{α} ℋ_{α, N_α}^{(e_α)}` inside `A05.FockSpace SpinBranch h`, mutual orthogonality
     and `iSupIndep` internal direct-sum independence, exact graded decomposition
     `A05.jointBudget h Ns K = ⨆_{∑ e_α ≤ K} gradedSectorSpace h Ns es`, and natural inclusion
     into `productCutoffSpace h Ns K`.
   - Explicit `K = 1` counterexample (`k1_product_cutoff_strict_superset`) for every `0 < h`:
     `k1DoubleExciteKet h hh` places one energy-1 excitation in each of `L↑` and `L↓`
     (`L↑, L↓, R↑, R↓` each individually inside `Ch07.fixedBudget h 0 1`), has total excitation
     `2 > 1`, lies strictly outside `A05.jointBudget h (fun _ => 0) 1`, and proves
     `A05.jointBudget h (fun _ => 0) 1 < productCutoffSpace h (fun _ => 0) 1`.

2. **General-`h` Singlet Klein-Product Sign** (`eq:ch21-pair-general-sign`):
   - For all `0 < h` and `x : Fin (2 * h)`, proves that both spin-singlet pairing channels
     `singletBranchesB` (`R↑, L↓`) and `singletBranchesA` (`R↓, L↑`) have exact CAR Klein-sign
     product `(-1)^(h + 1)`, yielding exact ground-to-ground amplitudes
     `(-1)^(h + 1) / (2 * h)` and `-(-1)^(h + 1) / (2 * h)` for `singletOrderSC` on their two
     mutually orthogonal target ground kets, specializing cleanly to `∓1/4` at `h = 2`.

3. **Explicit Sum-Over-States Formula for `W^(2)` (`prop:ch21-sw-intermediate`) and
   `Ch21 → A10` Finite Schrieffer-Wolff Umklapp Block Instantiation**:
   - Proves the exact off-diagonal sum-over-`I_Q` matrix-entry formula
     `eq:ch21-sw-intermediate-sum`, diagonal energy shift `eq:ch21-sw-diagonal-shift`, and
     strictly ordered nonpositivity sign rule in the finite-matrix `A10` setting.
   - Instantiates both the finite-matrix `A10` generator/non-resonance hypotheses AND the
     operator-level `A10.sw_compressed_bch_second_order` theorem directly on the spinful `Ch21`
     Umklapp-coupled block connecting `|Ω₀⟩ ∈ jointBudget h 0 0` to
     `umklappZeroChargeWitness h hh ∈ jointBudget h (+1,+1,-1,-1) (2*(h-1))` under the genuine
     spinful free-fermion Hamiltonian `spinfulFreeHamiltonian h`, yielding the exact second-order
     shift `-g_U^2 / (32 * h^5)` (`-g_U^2 / 1024` at `h = 2`).
-/

namespace Bosonize.Ch21

open scoped BigOperators ComplexConjugate

noncomputable local instance localModeLinearOrderCh21Bridge (h : ℕ) :
    LinearOrder (A05.Mode (Fin 4) h) := A05.speciesOrder h
noncomputable local instance localModeLTCh21Bridge (h : ℕ) :
    LT (A05.Mode (Fin 4) h) := (A05.speciesOrder h).toLT
noncomputable local instance localModeLECh21Bridge (h : ℕ) :
    LE (A05.Mode (Fin 4) h) := (A05.speciesOrder h).toLE
noncomputable local instance localModeDecidableEqCh21Bridge (h : ℕ) :
    DecidableEq (A05.Mode (Fin 4) h) := A05.localModeDecidableEq h

/-! ## Local Helpers for `DecidableEq` Bridging & Two-Site CAR Inner Products -/

private lemma ket_prod_eq_local (h : ℕ) (S : A05.Occupation SpinBranch h) :
    @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S = A02.ket S := by
  have hdec : (instDecidableEqProd : DecidableEq (A05.Mode SpinBranch h)) =
      A05.localModeDecidableEq h := Subsingleton.elim _ _
  exact congrArg (fun d => @A02.ket (A05.Mode SpinBranch h) _ d S) hdec

private lemma speciesConfig_erase_local (h : ℕ)
    (S : A05.Occupation SpinBranch h) (ν η : SpinBranch) (k : Ch01.Band (2 * h)) :
    Ch07.speciesConfiguration h (S.erase (ν, k)) η =
      if η = ν then (Ch07.speciesConfiguration h S η).erase k
      else Ch07.speciesConfiguration h S η := by
  ext j
  by_cases hη : η = ν
  · subst η
    simp [Ch07.speciesConfiguration, Finset.mem_erase]
  · simp [Ch07.speciesConfiguration, Finset.mem_erase, hη]

private lemma ch14_proj_eq_prod_local (h : ℕ) (Ns : SpinBranch → ℤ) (K : ℕ) :
    Ch14.projection h Ns K =
      @A03.coordinateProjection (A05.Mode SpinBranch h) _ instDecidableEqProd
        (Ch14.budgetSet h Ns K) := by
  apply @A02.end_ext_basis (A05.Mode SpinBranch h) _ instDecidableEqProd
  intro S
  have hket : @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S =
      @A02.ket (A05.Mode SpinBranch h) _ (Ch14.localModeDecidableEq h) S := by
    have hdec : (instDecidableEqProd : DecidableEq (A05.Mode SpinBranch h)) =
        Ch14.localModeDecidableEq h := Subsingleton.elim _ _
    exact congrArg (fun d => @A02.ket (A05.Mode SpinBranch h) _ d S) hdec
  unfold Ch14.projection
  rw [@A03.projection_ket (A05.Mode SpinBranch h) _ instDecidableEqProd, hket,
    @A03.projection_ket (A05.Mode SpinBranch h) _ (Ch14.localModeDecidableEq h)]

private lemma siteField_ket_local (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h))
    (S : A05.Occupation SpinBranch h) (ν : SpinBranch) (x : ℤ) :
    siteField h b ν x (A02.ket S) =
      (A01.normalization (2 * h) : ℂ) •
        ∑ k : Ch01.Band (2 * h),
          if (ν, k) ∈ S then
            (Ch06Ext.twistedCharacter (2 * h) (b ν) k x *
              Ch04.fermionSign (ν, k) S) • A02.ket (S.erase (ν, k))
          else 0 := by
  simp only [siteField, A05.liftedAnnihilation, LinearMap.smul_apply,
    LinearMap.sum_apply, A05.annihilation, Ch04.annihilation_ket]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with hk
  · simp only [smul_smul]
  · simp

private lemma map_if_zero_local {V W : Type*} [AddCommMonoid V] [AddCommMonoid W]
    [Module ℂ V] [Module ℂ W] (f : V →ₗ[ℂ] W) (p : Prop) [Decidable p] (v : V) :
    f (if p then v else 0) = if p then f v else 0 := by
  split_ifs <;> simp

private lemma twoSiteField_ket_local (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h))
    (S : A05.Occupation SpinBranch h) (ν₁ ν₂ : SpinBranch) (x : ℤ) :
    siteField h b ν₂ x (siteField h b ν₁ x (A02.ket S)) =
      ((A01.normalization (2 * h) : ℂ) ^ 2) •
        ∑ k₁ : Ch01.Band (2 * h), ∑ k₂ : Ch01.Band (2 * h),
          if (ν₁, k₁) ∈ S ∧ (ν₂, k₂) ∈ S.erase (ν₁, k₁) then
            (Ch06Ext.twistedCharacter (2 * h) (b ν₂) k₂ x *
              Ch04.fermionSign (ν₂, k₂) (S.erase (ν₁, k₁)) *
              (Ch06Ext.twistedCharacter (2 * h) (b ν₁) k₁ x *
                Ch04.fermionSign (ν₁, k₁) S)) •
              A02.ket ((S.erase (ν₁, k₁)).erase (ν₂, k₂))
          else 0 := by
  rw [siteField_ket_local]
  simp only [map_smul, map_sum]
  simp_rw [map_if_zero_local, map_smul, siteField_ket_local]
  rw [show (A01.normalization (2 * h) : ℂ) ^ 2 =
      (A01.normalization (2 * h) : ℂ) * (A01.normalization (2 * h) : ℂ) by ring, ← smul_smul]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k₁ _
  by_cases hk₁ : (ν₁, k₁) ∈ S
  · rw [ite_eq_left hk₁, smul_comm _ (A01.normalization (2 * h) : ℂ)]
    congr 1
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k₂ _
    by_cases hk₂ : (ν₂, k₂) ∈ S.erase (ν₁, k₁)
    · rw [ite_eq_left hk₂, ite_eq_left ⟨hk₁, hk₂⟩, smul_smul]
      congr 1
      ring
    · simp [hk₁, hk₂]
  · simp [hk₁]

private lemma erase_eq_erase_imp_eq_local {α : Type*} [DecidableEq α]
    {s : Finset α} {a b : α} (ha : a ∈ s)
    (heq : s.erase a = s.erase b) : a = b := by
  by_contra hne
  have hmem : a ∈ s.erase b := Finset.mem_erase.mpr ⟨hne, ha⟩
  rw [← heq] at hmem
  exact (Finset.mem_erase.mp hmem).1 rfl

private lemma sum_single_pair_local {ι : Type*} [Fintype ι]
    (a b : ι) (f : ι → ι → ℂ)
    (g : ι → ι → Prop) [∀ i j, Decidable (g i j)]
    (huniq : ∀ i j, g i j → i = a ∧ j = b)
    (hab : g a b) :
    (∑ i, ∑ j, if g i j then f i j else 0) = f a b := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp [hab]
    · intro j _ hj
      have hnot : ¬ g a j := fun h => hj (huniq a j h).2
      simp [hnot]
    · simp
  · intro i _ hi
    have hzero : ∀ j, ¬ g i j := fun j h => hi (huniq i j h).1
    simp [hzero]
  · simp

private lemma twoSiteField_inner_unique_local (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h))
    (S T : A05.Occupation SpinBranch h) (ν₁ ν₂ : SpinBranch) (x : ℤ)
    (a₁ a₂ : Ch01.Band (2 * h))
    (hmem₁ : (ν₁, a₁) ∈ S)
    (hmem₂ : (ν₂, a₂) ∈ S.erase (ν₁, a₁))
    (heqT : (S.erase (ν₁, a₁)).erase (ν₂, a₂) = T)
    (huniq : ∀ k₁ k₂, (ν₁, k₁) ∈ S ∧ (ν₂, k₂) ∈ S.erase (ν₁, k₁) ∧
        (S.erase (ν₁, k₁)).erase (ν₂, k₂) = T → k₁ = a₁ ∧ k₂ = a₂) :
    inner ℂ (A02.ket T) (siteField h b ν₂ x (siteField h b ν₁ x (A02.ket S))) =
      ((A01.normalization (2 * h) : ℂ) ^ 2) *
        (Ch06Ext.twistedCharacter (2 * h) (b ν₂) a₂ x *
          Ch04.fermionSign (ν₂, a₂) (S.erase (ν₁, a₁)) *
          (Ch06Ext.twistedCharacter (2 * h) (b ν₁) a₁ x *
            Ch04.fermionSign (ν₁, a₁) S)) := by
  rw [twoSiteField_ket_local, inner_smul_right]
  congr 1
  simp_rw [inner_sum]
  let g (k₁ k₂ : Ch01.Band (2 * h)) : Prop :=
    (ν₁, k₁) ∈ S ∧ (ν₂, k₂) ∈ S.erase (ν₁, k₁) ∧ (S.erase (ν₁, k₁)).erase (ν₂, k₂) = T
  have hre : (∑ k₁ : Ch01.Band (2 * h), ∑ k₂ : Ch01.Band (2 * h),
      inner ℂ (A02.ket T)
        (if (ν₁, k₁) ∈ S ∧ (ν₂, k₂) ∈ S.erase (ν₁, k₁) then
          (Ch06Ext.twistedCharacter (2 * h) (b ν₂) k₂ x *
            Ch04.fermionSign (ν₂, k₂) (S.erase (ν₁, k₁)) *
            (Ch06Ext.twistedCharacter (2 * h) (b ν₁) k₁ x *
              Ch04.fermionSign (ν₁, k₁) S)) •
            A02.ket ((S.erase (ν₁, k₁)).erase (ν₂, k₂))
        else 0)) =
      ∑ k₁ : Ch01.Band (2 * h), ∑ k₂ : Ch01.Band (2 * h),
        if g k₁ k₂ then
          Ch06Ext.twistedCharacter (2 * h) (b ν₂) k₂ x *
            Ch04.fermionSign (ν₂, k₂) (S.erase (ν₁, k₁)) *
            (Ch06Ext.twistedCharacter (2 * h) (b ν₁) k₁ x *
              Ch04.fermionSign (ν₁, k₁) S)
        else 0 := by
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun k₂ _ => ?_))
    dsimp only [g]
    by_cases h12 : (ν₁, k₁) ∈ S ∧ (ν₂, k₂) ∈ S.erase (ν₁, k₁)
    · rw [ite_eq_left h12, inner_smul_right, A02.ket_inner]
      by_cases hT : (S.erase (ν₁, k₁)).erase (ν₂, k₂) = T
      · rw [ite_eq_left hT.symm, mul_one, ite_eq_left ⟨h12.1, h12.2, hT⟩]
      · rw [ite_eq_right (fun h => hT h.symm), mul_zero, ite_eq_right (fun h => hT h.2.2)]
    · rw [ite_eq_right h12, inner_zero_right, ite_eq_right (fun h => h12 ⟨h.1, h.2.1⟩)]
  rw [hre]
  exact sum_single_pair_local a₁ a₂ _ g huniq ⟨hmem₁, hmem₂, heqT⟩

private lemma twoSiteField_unique_pair_local (h : ℕ)
    (S : A05.Occupation SpinBranch h) (ν₁ ν₂ : SpinBranch) (hν : ν₁ ≠ ν₂)
    (a₁ a₂ : Ch01.Band (2 * h)) :
    ∀ k₁ k₂,
      (ν₁, k₁) ∈ S ∧ (ν₂, k₂) ∈ S.erase (ν₁, k₁) ∧
      (S.erase (ν₁, k₁)).erase (ν₂, k₂) = (S.erase (ν₁, a₁)).erase (ν₂, a₂) →
      k₁ = a₁ ∧ k₂ = a₂ := by
  intro k₁ k₂ ⟨hk₁, hk₂, heq⟩
  have hspec₁ := congrArg (fun U => Ch07.speciesConfiguration h U ν₁) heq
  have hspec₂ := congrArg (fun U => Ch07.speciesConfiguration h U ν₂) heq
  simp only [speciesConfig_erase_local, ite_eq_right hν, ite_eq_right hν.symm] at hspec₁ hspec₂
  have hk₁S : k₁ ∈ Ch07.speciesConfiguration h S ν₁ :=
    Finset.mem_image.mpr ⟨(ν₁, k₁), Finset.mem_filter.mpr ⟨hk₁, rfl⟩, rfl⟩
  have hk₂S : k₂ ∈ Ch07.speciesConfiguration h S ν₂ :=
    Finset.mem_image.mpr ⟨(ν₂, k₂), Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hk₂, rfl⟩, rfl⟩
  exact ⟨erase_eq_erase_imp_eq_local hk₁S hspec₁, erase_eq_erase_imp_eq_local hk₂S hspec₂⟩

private lemma orderSC_maps_sector_local (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches SpinBranch) (x : ℤ)
    (Ns : SpinBranch → ℤ) (v : A05.FockSpace SpinBranch h) (hv : v ∈ chargeSector h Ns) :
    Ch20.orderSC h b branches x v ∈ chargeSector h (Ch20.scTarget branches Ns) := by
  have htarget : Ch20.scTarget branches Ns = fun ν => Ns ν + Ch20.scShift branches ν := by
    funext ν
    exact Ch20.scTarget_apply branches Ns ν
  rw [htarget]
  exact charge_commutator_maps_sector h (Ch20.orderSC h b branches x) (Ch20.scShift branches)
    (fun ν => Ch20.orderSC_charge_commutator h b branches x ν) Ns v hv

/-! ## 1. Graded Direct-Sum Decomposition vs. Product-Cutoff Counterexample (`eq:ch21-budget-energy-sum`, `eq:ch21-not-product-cutoff`) -/

/-- Occupation set with exact per-species charges `Ns` and exact per-species excitation grades `es`. -/
def gradedSectorSet (h : ℕ) (Ns : SpinBranch → ℤ) (es : SpinBranch → ℕ) :
    Set (A05.Occupation SpinBranch h) :=
  {S | ∀ ν, Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) = Ns ν ∧
            Ch07.excitationEnergy h (Ch07.speciesConfiguration h S ν) = (es ν : ℤ)}

/-- Exact graded tensor-product subspace `⨂_{α ∈ Fin 4} ℋ_{α, N_α}^{(e_α)}` inside `FockSpace`. -/
noncomputable def gradedSectorSpace (h : ℕ) (Ns : SpinBranch → ℤ) (es : SpinBranch → ℕ) :
    Submodule ℂ (A05.FockSpace SpinBranch h) :=
  @A03.coordinateSpace (A05.Mode SpinBranch h) _ instDecidableEqProd (gradedSectorSet h Ns es)

/-- Per-species product-cutoff occupation set: every species individually has excitation `≤ K`. -/
def productCutoffSet (h : ℕ) (Ns : SpinBranch → ℤ) (K : ℕ) :
    Set (A05.Occupation SpinBranch h) :=
  {S | ∀ ν, Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) = Ns ν ∧
            Ch07.excitationEnergy h (Ch07.speciesConfiguration h S ν) ≤ (K : ℤ)}

/-- Per-species product-cutoff subspace `⨂_{α} (⨁_{e=0}^K ℋ_{α, N_α}^{(e)})` inside `FockSpace`. -/
noncomputable def productCutoffSpace (h : ℕ) (Ns : SpinBranch → ℤ) (K : ℕ) :
    Submodule ℂ (A05.FockSpace SpinBranch h) :=
  @A03.coordinateSpace (A05.Mode SpinBranch h) _ instDecidableEqProd (productCutoffSet h Ns K)

/-- Index predicate for 4-branch excitation-grade tuples `(e_α)` with total cost `∑_α e_α ≤ K`. -/
def gradeTupleIndex (K : ℕ) : Set (SpinBranch → ℕ) :=
  {es | ∑ ν : SpinBranch, es ν ≤ K}

/-- Basis ket characterization of `gradedSectorSpace` via single-species `Ch07.energySpace`. -/
lemma ket_mem_gradedSectorSpace_iff (h : ℕ) (Ns : SpinBranch → ℤ) (es : SpinBranch → ℕ)
    (S : A05.Occupation SpinBranch h) :
    A02.ket S ∈ gradedSectorSpace h Ns es ↔
      ∀ ν, A02.ket (Ch07.speciesConfiguration h S ν) ∈ Ch07.energySpace h (Ns ν) (es ν : ℤ) := by
  rw [← ket_prod_eq_local, gradedSectorSpace,
    @A03.ket_mem_coordinate_space (A05.Mode SpinBranch h) _ instDecidableEqProd]
  constructor
  · intro hS ν
    exact (A03.ket_mem_coordinate_space _ _).mpr (hS ν)
  · intro hS ν
    exact (A03.ket_mem_coordinate_space _ _).mp (hS ν)

/-- Ordered tensor product `A05.tensorVector` maps `∏_ν ℋ_{ν, N_ν}^{(e_ν)}` into `gradedSectorSpace`. -/
lemma tensorVector_mem_gradedSectorSpace (h : ℕ) (Ns : SpinBranch → ℤ) (es : SpinBranch → ℕ)
    (vs : SpinBranch → Ch07.FockSpace h)
    (hvs : ∀ ν, vs ν ∈ Ch07.energySpace h (Ns ν) (es ν : ℤ)) :
    A05.tensorVector h vs ∈ gradedSectorSpace h Ns es := by
  rw [gradedSectorSpace, @A03.coordinate_space_support (A05.Mode SpinBranch h) _ instDecidableEqProd]
  intro S hS
  simp only [gradedSectorSet, Set.mem_ofPred_eq, not_forall] at hS
  obtain ⟨ν, hν⟩ := hS
  have hzero : A02.coordinates (Ch01.Band (2 * h)) (vs ν) (Ch07.speciesConfiguration h S ν) = 0 :=
    (A03.coordinate_space_support _ (vs ν)).mp (hvs ν) (Ch07.speciesConfiguration h S ν) hν
  change (∏ η : SpinBranch, vs η (Ch07.speciesConfiguration h S η)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ ν) hzero

/-- Distinct excitation-grade tuples yield mutually orthogonal graded subspaces (`eq:ch21-budget-energy-sum`). -/
lemma gradedSectorSpace_orthogonal (h : ℕ) (Ns : SpinBranch → ℤ)
    (es₁ es₂ : SpinBranch → ℕ) (hne : es₁ ≠ es₂)
    (u : A05.FockSpace SpinBranch h) (hu : u ∈ gradedSectorSpace h Ns es₁)
    (v : A05.FockSpace SpinBranch h) (hv : v ∈ gradedSectorSpace h Ns es₂) :
    inner ℂ u v = 0 := by
  exact @A03.coordinate_space_disjoint (A05.Mode SpinBranch h) _ instDecidableEqProd _ _
    (by
      rw [Set.disjoint_left]
      intro S hS₁ hS₂
      apply hne
      funext ν
      have heq : (es₁ ν : ℤ) = (es₂ ν : ℤ) := (hS₁ ν).2.symm.trans (hS₂ ν).2
      exact Int.ofNat.inj heq)
    u hu v hv

/-- Pairwise orthogonality implies linear independence (`iSupIndep`) of the graded direct summands. -/
theorem gradedSectorSpace_iSupIndep (h : ℕ) (Ns : SpinBranch → ℤ) (K : ℕ) :
    iSupIndep (fun es : {e : SpinBranch → ℕ // ∑ ν : SpinBranch, e ν ≤ K} =>
      gradedSectorSpace h Ns es.val) := by
  rw [iSupIndep_def]
  intro es
  rw [Submodule.disjoint_def]
  intro v hv₁ hv₂
  have horth : ∀ w ∈ ⨆ (es' : {e : SpinBranch → ℕ // ∑ ν : SpinBranch, e ν ≤ K}) (_ : es' ≠ es),
      gradedSectorSpace h Ns es'.val, inner ℂ v w = 0 := by
    intro w hw
    induction hw using Submodule.iSup_induction' with
    | mem es' x hx =>
      induction hx using Submodule.iSup_induction' with
      | mem hne y hy =>
        exact gradedSectorSpace_orthogonal h Ns es.val es'.val
          (fun heq => hne (Subtype.ext heq.symm)) v hv₁ y hy
      | zero => simp
      | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  exact inner_self_eq_zero.mp (horth v hv₂)

/-- Set-level partition of `Ch14.budgetSet h Ns K` into disjoint graded energy-tuple sets (`0 < h`). -/
lemma budgetSet_eq_iUnion_gradedSectorSet (h : ℕ) (hh : 0 < h) (Ns : SpinBranch → ℤ) (K : ℕ) :
    Ch14.budgetSet h Ns K =
      ⋃ es : {e : SpinBranch → ℕ // ∑ ν : SpinBranch, e ν ≤ K}, gradedSectorSet h Ns es.val := by
  ext S
  simp only [Ch14.budgetSet, gradedSectorSet, Set.mem_ofPred_eq, Set.mem_iUnion, Subtype.exists]
  constructor
  · rintro ⟨hchg, htot⟩
    let es : SpinBranch → ℕ := fun ν => (Ch07.excitationEnergy h (Ch07.speciesConfiguration h S ν)).toNat
    have hcast (ν : SpinBranch) : (es ν : ℤ) = Ch07.excitationEnergy h (Ch07.speciesConfiguration h S ν) :=
      Int.toNat_of_nonneg (Ch07.excitation_nonneg h hh _)
    have hsum : ∑ ν : SpinBranch, es ν ≤ K := by
      have htot' : ((∑ ν : SpinBranch, es ν : ℕ) : ℤ) = Ch07.totalExcitation h S := by
        simp only [Nat.cast_sum, hcast, Ch07.totalExcitation]
      omega
    exact ⟨es, hsum, fun ν => ⟨hchg ν, (hcast ν).symm⟩⟩
  · rintro ⟨es, hsum, hS⟩
    refine ⟨fun ν => (hS ν).1, ?_⟩
    unfold Ch07.totalExcitation
    simp_rw [fun ν => (hS ν).2]
    have hcast : (∑ ν : SpinBranch, (es ν : ℤ)) = ((∑ ν : SpinBranch, es ν : ℕ) : ℤ) := by
      simp
    rw [hcast]
    exact_mod_cast hsum

/-- Exact basis-ket characterization of `A05.jointBudget h Ns K` via per-species charges and
summable per-species excitation grades `∑_α e_α ≤ K`. -/
theorem ket_mem_jointBudget_iff_graded (h : ℕ) (hh : 0 < h) (Ns : SpinBranch → ℤ) (K : ℕ)
    (S : A05.Occupation SpinBranch h) :
    A02.ket S ∈ A05.jointBudget h Ns K ↔
      ∃ es : SpinBranch → ℕ, (∑ ν : SpinBranch, es ν ≤ K) ∧
        ∀ ν, Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) = Ns ν ∧
             Ch07.excitationEnergy h (Ch07.speciesConfiguration h S ν) = (es ν : ℤ) := by
  rw [← ket_prod_eq_local, A05.jointBudget, Ch07.species_budget_ket]
  have hmem := Set.ext_iff.mp (budgetSet_eq_iUnion_gradedSectorSet h hh Ns K) S
  simpa only [Ch14.budgetSet, gradedSectorSet, Set.mem_ofPred_eq, Set.mem_iUnion,
    Subtype.exists, exists_prop] using hmem

/-- Equation `eq:ch21-budget-energy-sum`: exact orthogonal graded direct-sum decomposition
`ℬ_{N, K} = ⨁_{∑ e_α ≤ K} ⨂_α ℋ_{α, N_α}^{(e_α)}` on the CAR Fock space (`0 < h`). -/
theorem jointBudget_eq_graded_sum (h : ℕ) (hh : 0 < h) (Ns : SpinBranch → ℤ) (K : ℕ) :
    A05.jointBudget h Ns K =
      ⨆ es : {e : SpinBranch → ℕ // ∑ ν : SpinBranch, e ν ≤ K}, gradedSectorSpace h Ns es.val := by
  apply le_antisymm
  · unfold A05.jointBudget Ch07.speciesBudget A03.coordinateSpace
    apply Submodule.span_le.mpr
    rintro _ ⟨S, hS, rfl⟩
    have hmem : S ∈ ⋃ es : {e : SpinBranch → ℕ // ∑ ν : SpinBranch, e ν ≤ K},
        gradedSectorSet h Ns es.val := by
      rw [← budgetSet_eq_iUnion_gradedSectorSet h hh Ns K]
      exact hS
    rcases Set.mem_iUnion.mp hmem with ⟨es, hes⟩
    exact Submodule.mem_iSup_of_mem es
      ((@A03.ket_mem_coordinate_space (A05.Mode SpinBranch h) _ instDecidableEqProd
        (gradedSectorSet h Ns es.val) S).mpr hes)
  · apply iSup_le
    intro es
    unfold gradedSectorSpace A05.jointBudget Ch07.speciesBudget
    apply @A03.coordinate_space_mono (A05.Mode SpinBranch h) _ instDecidableEqProd
    intro S hS
    have hmem : S ∈ Ch14.budgetSet h Ns K := by
      rw [budgetSet_eq_iUnion_gradedSectorSet h hh Ns K]
      exact Set.mem_iUnion.mpr ⟨es, hS⟩
    exact hmem

/-- Natural inclusion `ℬ_{N, K} ≤ ⨂_α (⨁_{e=0}^K ℋ_{α, N_α}^{(e)})` for every `0 < h`. -/
theorem jointBudget_le_productCutoff (h : ℕ) (hh : 0 < h) (Ns : SpinBranch → ℤ) (K : ℕ) :
    A05.jointBudget h Ns K ≤ productCutoffSpace h Ns K := by
  unfold A05.jointBudget Ch07.speciesBudget productCutoffSpace
  apply @A03.coordinate_space_mono (A05.Mode SpinBranch h) _ instDecidableEqProd
  intro S ⟨hchg, htot⟩ ν
  refine ⟨hchg ν, ?_⟩
  have hsingle : Ch07.excitationEnergy h (Ch07.speciesConfiguration h S ν) ≤ Ch07.totalExcitation h S :=
    Finset.single_le_sum (fun η _ => Ch07.excitation_nonneg h hh _) (Finset.mem_univ ν)
  exact le_trans hsingle htot

/-- Exact graded direct-sum decomposition of `productCutoffSpace` over `∀ ν, e_ν ≤ K`. -/
theorem productCutoffSpace_eq_graded_sum (h : ℕ) (hh : 0 < h) (Ns : SpinBranch → ℤ) (K : ℕ) :
    productCutoffSpace h Ns K =
      ⨆ es : {e : SpinBranch → ℕ // ∀ ν : SpinBranch, e ν ≤ K}, gradedSectorSpace h Ns es.val := by
  apply le_antisymm
  · unfold productCutoffSpace A03.coordinateSpace
    apply Submodule.span_le.mpr
    rintro _ ⟨S, hS, rfl⟩
    let es : SpinBranch → ℕ := fun ν => (Ch07.excitationEnergy h (Ch07.speciesConfiguration h S ν)).toNat
    have hcast (ν : SpinBranch) : (es ν : ℤ) = Ch07.excitationEnergy h (Ch07.speciesConfiguration h S ν) :=
      Int.toNat_of_nonneg (Ch07.excitation_nonneg h hh _)
    have hle : ∀ ν : SpinBranch, es ν ≤ K := fun ν => by
      have := (hS ν).2
      have := hcast ν
      omega
    exact Submodule.mem_iSup_of_mem ⟨es, hle⟩
      ((@A03.ket_mem_coordinate_space (A05.Mode SpinBranch h) _ instDecidableEqProd
        (gradedSectorSet h Ns es) S).mpr (fun ν => ⟨(hS ν).1, (hcast ν).symm⟩))
  · apply iSup_le
    intro es
    unfold gradedSectorSpace productCutoffSpace
    apply @A03.coordinate_space_mono (A05.Mode SpinBranch h) _ instDecidableEqProd
    intro S hS ν
    refine ⟨(hS ν).1, ?_⟩
    rw [(hS ν).2]
    exact_mod_cast es.property ν

/-! ### 1.1 Explicit `K = 1` Product-Cutoff Counterexample (`eq:ch21-not-product-cutoff`) -/

/-- Canonical Fermi-surface momentum `k = 0` inside `Ch01.Band (2 * h)` for every `0 < h`. -/
def bandZero (h : ℕ) (hh : 0 < h) : Ch01.Band (2 * h) :=
  ⟨0, by simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat]; omega⟩

/-- Single-species zero-charge energy-1 configuration: promote `k = 0` to `k = 1` out of the sea. -/
def singleExciteZero (h : ℕ) (hh : 0 < h) : Ch07.Occupation h :=
  insert (witnessUpperMode h hh) ((Ch07.groundConfiguration h 0).erase (bandZero h hh))

lemma singleExciteZero_charge_and_excitation (h : ℕ) (hh : 0 < h) :
    Ch07.relativeCharge h (singleExciteZero h hh) = 0 ∧
    Ch07.excitationEnergy h (singleExciteZero h hh) = 1 := by
  have h0adm : Ch07.admissible h 0 := by unfold Ch07.admissible; omega
  have hz0 : bandZero h hh ∈ Ch07.groundConfiguration h 0 := by
    simp [Ch07.groundConfiguration, bandZero]
  have h1not : witnessUpperMode h hh ∉ (Ch07.groundConfiguration h 0).erase (bandZero h hh) := by
    intro hmem
    exact witnessUpperMode_not_mem_ground_zero h hh (Finset.mem_of_mem_erase hmem)
  have hchg0 := Ch07.ground_configuration_charge h hh 0 h0adm
  have hexc0 := Ch07.ground_configuration_excitation h hh 0 h0adm
  have hchg_er : Ch07.relativeCharge h ((Ch07.groundConfiguration h 0).erase (bandZero h hh)) = -1 := by
    rw [Ch07.charge_erase h _ _ hz0, hchg0]; ring
  have hexc_er : Ch07.excitationEnergy h ((Ch07.groundConfiguration h 0).erase (bandZero h hh)) = 0 := by
    rw [Ch07.excitation_erase h _ _ hz0, hexc0, hchg0]
    simp [bandZero]
  constructor
  · unfold singleExciteZero
    rw [Ch07.charge_insert h _ _ h1not, hchg_er]; ring
  · unfold singleExciteZero
    rw [Ch07.excitation_insert h _ _ h1not, hexc_er, hchg_er]
    simp [witnessUpperMode]

/-- Per-species configuration for the `K = 1` counterexample: energy `1` in `L↑` and `L↓`,
energy `0` in `R↑` and `R↓`. -/
def k1DoubleExciteSpeciesConfig (h : ℕ) (hh : 0 < h) (ν : SpinBranch) : Ch07.Occupation h :=
  if ν = brLUp ∨ ν = brLDown then singleExciteZero h hh else Ch07.groundConfiguration h 0

/-- Combined 4-branch occupation configuration for the `K = 1` product-cutoff counterexample. -/
noncomputable def k1DoubleExciteConfig (h : ℕ) (hh : 0 < h) : A05.Occupation SpinBranch h :=
  A05.jointConfiguration h (k1DoubleExciteSpeciesConfig h hh)

/-- Basis ket `|1_{L↑}, 1_{L↓}, 0_{R↑}, 0_{R↓}⟩` witnessing strictness of `eq:ch21-not-product-cutoff`. -/
noncomputable def k1DoubleExciteKet (h : ℕ) (hh : 0 < h) : A05.FockSpace SpinBranch h :=
  A02.ket (k1DoubleExciteConfig h hh)

/-- Explicit `K = 1` counterexample (`eq:ch21-not-product-cutoff`) for every `0 < h`:
a basis ket with one energy-1 excitation in each of two distinct species (`L↑, L↓`) belongs to each
individual `K = 1` species budget and to `productCutoffSpace h 0 1`, yet has total excitation
`2 > 1`, lies strictly outside `A05.jointBudget h 0 1`, and proves strict inclusion
`A05.jointBudget h 0 1 < productCutoffSpace h 0 1`. -/
theorem k1_product_cutoff_strict_superset (h : ℕ) (hh : 0 < h) :
    (∀ ν : SpinBranch,
      A02.ket (Ch07.speciesConfiguration h (k1DoubleExciteConfig h hh) ν) ∈
        Ch07.fixedBudget h 0 1) ∧
    k1DoubleExciteKet h hh ∈ productCutoffSpace h (fun _ => 0) 1 ∧
    Ch07.totalExcitation h (k1DoubleExciteConfig h hh) = 2 ∧
    k1DoubleExciteKet h hh ∉ A05.jointBudget h (fun _ => 0) 1 ∧
    A05.jointBudget h (fun _ => 0) 1 < productCutoffSpace h (fun _ => 0) 1 := by
  have h0adm : Ch07.admissible h 0 := by unfold Ch07.admissible; omega
  have hspec (ν : SpinBranch) :
      Ch07.speciesConfiguration h (k1DoubleExciteConfig h hh) ν =
        k1DoubleExciteSpeciesConfig h hh ν :=
    A05.species_joint_configuration h (k1DoubleExciteSpeciesConfig h hh) ν
  have h1 := singleExciteZero_charge_and_excitation h hh
  have hchg0 := Ch07.ground_configuration_charge h hh 0 h0adm
  have hexc0 := Ch07.ground_configuration_excitation h hh 0 h0adm
  have hper (ν : SpinBranch) :
      Ch07.relativeCharge h (Ch07.speciesConfiguration h (k1DoubleExciteConfig h hh) ν) = 0 ∧
      Ch07.excitationEnergy h (Ch07.speciesConfiguration h (k1DoubleExciteConfig h hh) ν) ≤ 1 := by
    rw [hspec ν]
    unfold k1DoubleExciteSpeciesConfig
    split_ifs
    · exact ⟨h1.1, by omega⟩
    · exact ⟨hchg0, by omega⟩
  have hprod_mem : k1DoubleExciteKet h hh ∈ productCutoffSpace h (fun _ => 0) 1 := by
    rw [k1DoubleExciteKet, ← ket_prod_eq_local, productCutoffSpace,
      @A03.ket_mem_coordinate_space (A05.Mode SpinBranch h) _ instDecidableEqProd]
    exact hper
  have htot : Ch07.totalExcitation h (k1DoubleExciteConfig h hh) = 2 := by
    unfold Ch07.totalExcitation
    rw [Fin.sum_univ_four]
    change Ch07.excitationEnergy h (Ch07.speciesConfiguration h (k1DoubleExciteConfig h hh) brLUp) +
        Ch07.excitationEnergy h (Ch07.speciesConfiguration h (k1DoubleExciteConfig h hh) brLDown) +
        Ch07.excitationEnergy h (Ch07.speciesConfiguration h (k1DoubleExciteConfig h hh) brRUp) +
        Ch07.excitationEnergy h (Ch07.speciesConfiguration h (k1DoubleExciteConfig h hh) brRDown) = 2
    rw [hspec brLUp, hspec brLDown, hspec brRUp, hspec brRDown]
    have h2 : ¬ (brRUp = brLUp ∨ brRUp = brLDown) := by decide
    have h3 : ¬ (brRDown = brLUp ∨ brRDown = brLDown) := by decide
    simp only [k1DoubleExciteSpeciesConfig, true_or, or_true, ↓reduceIte,
      ite_eq_right h2, ite_eq_right h3, h1.2, hexc0]
    norm_num
  have hnot_mem : k1DoubleExciteKet h hh ∉ A05.jointBudget h (fun _ => 0) 1 := by
    rw [k1DoubleExciteKet, ← ket_prod_eq_local, A05.jointBudget, Ch07.species_budget_ket]
    intro hmem
    have := hmem.2
    omega
  refine ⟨fun ν => (Ch07.ket_mem_fixed_budget h _ 0 1).mpr (hper ν), hprod_mem, htot, hnot_mem, ?_⟩
  exact lt_of_le_of_ne (jointBudget_le_productCutoff h hh (fun _ => 0) 1)
    (fun heq => hnot_mem (heq ▸ hprod_mem))

/-! ## 2. General-`h` Singlet Klein-Product Sign (`eq:ch21-pair-general-sign`) -/

private lemma ground0_card_general (h : ℕ) (hh : 0 < h) :
    (Ch07.groundConfiguration h 0).card = h := by
  have hz := Ch07.ground_configuration_card h hh 0 (by unfold Ch07.admissible; omega)
  omega

private lemma groundM1_card_general (h : ℕ) (hh : 0 < h) :
    (Ch07.groundConfiguration h (-1)).card = h - 1 := by
  have hz := Ch07.ground_configuration_card h hh (-1) (by unfold Ch07.admissible; omega)
  omega

private lemma erase_bandZero_ground0 (h : ℕ) (hh : 0 < h) :
    (Ch07.groundConfiguration h 0).erase (bandZero h hh) = Ch07.groundConfiguration h (-1) := by
  ext l
  simp only [Finset.mem_erase, Ch07.groundConfiguration, Finset.mem_filter, Finset.mem_univ,
    true_and, ne_eq, Subtype.ext_iff, bandZero]
  omega

private lemma prec_bandZero_ground0 (h : ℕ) (hh : 0 < h) :
    Ch04.precedingCount (bandZero h hh) (Ch07.groundConfiguration h 0) = h - 1 := by
  have hfilt : (Ch07.groundConfiguration h 0).filter (· < bandZero h hh) =
      Ch07.groundConfiguration h (-1) := by
    ext l
    simp only [Finset.mem_filter, Ch07.groundConfiguration, Finset.mem_univ, true_and]
    change (l.val ≤ 0 ∧ l.val < (0 : ℤ)) ↔ l.val ≤ -1
    omega
  unfold Ch04.precedingCount
  rw [hfilt]
  exact groundM1_card_general h hh

private lemma normalization_sq_general (h : ℕ) (hh : 0 < h) :
    (A01.normalization (2 * h) : ℂ) ^ 2 = (2 * (h : ℂ))⁻¹ := by
  let _ : NeZero (2 * h) := ⟨by omega⟩
  have hsq : ((2 * h : ℕ) : ℂ) * (A01.normalization (2 * h) : ℂ) ^ 2 = 1 :=
    A01.normalization_square_complex (2 * h)
  apply eq_inv_of_mul_eq_one_right
  simpa [Nat.cast_mul, Nat.cast_ofNat] using hsq

/-- Equation `eq:ch21-pair-general-sign`: for every `0 < h`, the CAR Klein-sign products of
both singlet channels equal `(-1)^(h + 1)` (exponents `(2h - 1) + (3h - 2)` for channel 1
`singletBranchesB`, and `(h - 1) + (4h - 2)` for channel 2 `singletBranchesA`). -/
theorem singlet_klein_product_sign_eq (h : ℕ) (hh : 0 < h) :
    let S₀ := A05.groundConfiguration h (fun _ : SpinBranch => (0 : ℤ))
    let k₀ := bandZero h hh
    Ch04.fermionSign (brRUp, k₀) (S₀.erase (brLDown, k₀)) * Ch04.fermionSign (brLDown, k₀) S₀ =
      (-1 : ℂ) ^ (h + 1) ∧
    Ch04.fermionSign (brRDown, k₀) (S₀.erase (brLUp, k₀)) * Ch04.fermionSign (brLUp, k₀) S₀ =
      (-1 : ℂ) ^ (h + 1) := by
  dsimp only
  let S₀ := A05.groundConfiguration h (fun _ : SpinBranch => (0 : ℤ))
  let k₀ := bandZero h hh
  have hS0_spec (ν : SpinBranch) :
      Ch07.speciesConfiguration h S₀ ν = Ch07.groundConfiguration h 0 :=
    A05.species_joint_configuration h (fun _ => Ch07.groundConfiguration h 0) ν
  have hc0 := ground0_card_general h hh
  have hcm1 := groundM1_card_general h hh
  have her := erase_bandZero_ground0 h hh
  have hpr := prec_bandZero_ground0 h hh
  have hp1B : Ch04.precedingCount (brLDown, k₀) S₀ = 2 * h - 1 := by
    rw [A05.preceding_count_split]
    have hfilt : (Finset.univ.filter (· < brLDown) : Finset SpinBranch) = {brLUp} := by decide
    rw [hfilt, Finset.sum_singleton, hS0_spec brLUp, hS0_spec brLDown, hc0, hpr]
    omega
  have hp2B : Ch04.precedingCount (brRUp, k₀) (S₀.erase (brLDown, k₀)) = 3 * h - 2 := by
    rw [A05.preceding_count_split]
    have hfilt : (Finset.univ.filter (· < brRUp) : Finset SpinBranch) = {brLUp, brLDown} := by
      decide
    rw [hfilt, Finset.sum_insert (by decide), Finset.sum_singleton,
      speciesConfig_erase_local, speciesConfig_erase_local, speciesConfig_erase_local,
      ite_eq_right brLUp_ne_brLDown, ite_eq_left rfl, ite_eq_right brLDown_ne_brRUp.symm,
      hS0_spec brLUp, hS0_spec brLDown, hS0_spec brRUp, her, hc0, hcm1, hpr]
    omega
  have hp1A : Ch04.precedingCount (brLUp, k₀) S₀ = h - 1 := by
    rw [A05.preceding_count_split]
    have hfilt : (Finset.univ.filter (· < brLUp) : Finset SpinBranch) = ∅ := by decide
    rw [hfilt, Finset.sum_empty, zero_add, hS0_spec brLUp, hpr]
  have hp2A : Ch04.precedingCount (brRDown, k₀) (S₀.erase (brLUp, k₀)) = 4 * h - 2 := by
    rw [A05.preceding_count_split]
    have hfilt : (Finset.univ.filter (· < brRDown) : Finset SpinBranch) =
        {brLUp, brLDown, brRUp} := by decide
    rw [hfilt, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      speciesConfig_erase_local, speciesConfig_erase_local,
      speciesConfig_erase_local, speciesConfig_erase_local,
      ite_eq_left rfl, ite_eq_right brLUp_ne_brLDown.symm,
      ite_eq_right brLUp_ne_brRUp.symm, ite_eq_right brLUp_ne_brRDown.symm,
      hS0_spec brLUp, hS0_spec brLDown, hS0_spec brRUp, hS0_spec brRDown,
      her, hcm1, hc0, hpr]
    omega
  have hexpB : (3 * h - 2) + (2 * h - 1) = (h + 1) + 2 * (2 * h - 2) := by omega
  have hexpA : (4 * h - 2) + (h - 1) = (h + 1) + 2 * (2 * h - 2) := by omega
  constructor
  · unfold Ch04.fermionSign
    rw [hp2B, hp1B, ← pow_add, hexpB, pow_add, pow_mul]
    norm_num
  · unfold Ch04.fermionSign
    rw [hp2A, hp1A, ← pow_add, hexpA, pow_add, pow_mul]
    norm_num

/-- General-`h` channel-1 (`singletBranchesB`: `R↑, L↓`) ground-to-ground matrix element
`(-1)^(h + 1) / (2 * h)` for arbitrary `0 < h` and `x : ℤ`. -/
theorem singlet_klein_sign_channel1 (h : ℕ) (hh : 0 < h) (x : ℤ) :
    inner ℂ (A05.groundKet h (Ch20.scTarget singletBranchesB (fun _ => 0)))
      (Ch20.orderSC h (fun _ => Ch06Ext.periodicTwist (2 * h)) singletBranchesB x
        (A05.groundKet h (fun _ => 0))) =
      (-1 : ℂ) ^ (h + 1) / (2 * (h : ℂ)) := by
  let b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h) := fun _ => Ch06Ext.periodicTwist (2 * h)
  let S₀ : A05.Occupation SpinBranch h := A05.groundConfiguration h (fun _ => 0)
  let T₁ : A05.Occupation SpinBranch h :=
    A05.groundConfiguration h (Ch20.scTarget singletBranchesB (fun _ => 0))
  let k₀ : Ch01.Band (2 * h) := bandZero h hh
  have hS0_mem (ν : SpinBranch) (k : Ch01.Band (2 * h)) :
      (ν, k) ∈ S₀ ↔ k ∈ Ch07.groundConfiguration h 0 := by
    simp [S₀, A05.groundConfiguration, A05.jointConfiguration]
  have hz0 : k₀ ∈ Ch07.groundConfiguration h 0 := by
    simp [Ch07.groundConfiguration, k₀, bandZero]
  have ha₁ : (brLDown, k₀) ∈ S₀ := (hS0_mem brLDown k₀).mpr hz0
  have ha₂ : (brRUp, k₀) ∈ S₀ := (hS0_mem brRUp k₀).mpr hz0
  have ha₂' : (brRUp, k₀) ∈ S₀.erase (brLDown, k₀) :=
    Finset.mem_erase.mpr ⟨fun h => brLDown_ne_brRUp.symm (congrArg Prod.fst h), ha₂⟩
  have hT1_mem (ν : SpinBranch) (k : Ch01.Band (2 * h)) :
      (ν, k) ∈ T₁ ↔ k ∈ Ch07.groundConfiguration h (Ch20.scTarget singletBranchesB (fun _ => 0) ν) := by
    simp [T₁, A05.groundConfiguration, A05.jointConfiguration]
  have heqT : (S₀.erase (brLDown, k₀)).erase (brRUp, k₀) = T₁ := by
    ext ⟨ν, k⟩
    simp only [Finset.mem_erase, ne_eq, Prod.mk.injEq, hS0_mem, hT1_mem]
    fin_cases ν <;>
      simp [Ch20.scTarget_apply, Ch20.scShift, singletBranchesB, brLDown, brRUp,
        Ch07.groundConfiguration, k₀, bandZero, Subtype.ext_iff] <;> omega
  have huniq := twoSiteField_unique_pair_local h S₀ brLDown brRUp brLDown_ne_brRUp k₀ k₀
  rw [show Ch20.orderSC h b singletBranchesB x (A05.groundKet h (fun _ => 0)) =
      siteField h b brRUp x (siteField h b brLDown x (A02.ket S₀)) from rfl]
  change inner ℂ (A02.ket T₁) (siteField h b brRUp x (siteField h b brLDown x (A02.ket S₀))) = _
  rw [twoSiteField_inner_unique_local h b S₀ T₁ brLDown brRUp x k₀ k₀ ha₁ ha₂' heqT
    (fun k₁ k₂ h => huniq k₁ k₂ ⟨h.1, h.2.1, h.2.2.trans heqT.symm⟩)]
  have htw (ν : SpinBranch) : Ch06Ext.twistedCharacter (2 * h) (b ν) k₀ x = 1 := by
    simp [b, Ch06Ext.twistedCharacter, Ch06Ext.liftPhase, Ch06Ext.periodicTwist,
      A01.integerCharacter, k₀, bandZero]
  rw [htw brRUp, one_mul, one_mul, (singlet_klein_product_sign_eq h hh).1,
    normalization_sq_general h hh, div_eq_inv_mul]

/-- General-`h` channel-2 (`singletBranchesA`: `R↓, L↑`) ground-to-ground matrix element
`(-1)^(h + 1) / (2 * h)` for arbitrary `0 < h` and `x : ℤ`. -/
theorem singlet_klein_sign_channel2 (h : ℕ) (hh : 0 < h) (x : ℤ) :
    inner ℂ (A05.groundKet h (Ch20.scTarget singletBranchesA (fun _ => 0)))
      (Ch20.orderSC h (fun _ => Ch06Ext.periodicTwist (2 * h)) singletBranchesA x
        (A05.groundKet h (fun _ => 0))) =
      (-1 : ℂ) ^ (h + 1) / (2 * (h : ℂ)) := by
  let b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h) := fun _ => Ch06Ext.periodicTwist (2 * h)
  let S₀ : A05.Occupation SpinBranch h := A05.groundConfiguration h (fun _ => 0)
  let T₂ : A05.Occupation SpinBranch h :=
    A05.groundConfiguration h (Ch20.scTarget singletBranchesA (fun _ => 0))
  let k₀ : Ch01.Band (2 * h) := bandZero h hh
  have hS0_mem (ν : SpinBranch) (k : Ch01.Band (2 * h)) :
      (ν, k) ∈ S₀ ↔ k ∈ Ch07.groundConfiguration h 0 := by
    simp [S₀, A05.groundConfiguration, A05.jointConfiguration]
  have hz0 : k₀ ∈ Ch07.groundConfiguration h 0 := by
    simp [Ch07.groundConfiguration, k₀, bandZero]
  have ha₁ : (brLUp, k₀) ∈ S₀ := (hS0_mem brLUp k₀).mpr hz0
  have ha₂ : (brRDown, k₀) ∈ S₀ := (hS0_mem brRDown k₀).mpr hz0
  have ha₂' : (brRDown, k₀) ∈ S₀.erase (brLUp, k₀) :=
    Finset.mem_erase.mpr ⟨fun h => brLUp_ne_brRDown.symm (congrArg Prod.fst h), ha₂⟩
  have hT2_mem (ν : SpinBranch) (k : Ch01.Band (2 * h)) :
      (ν, k) ∈ T₂ ↔ k ∈ Ch07.groundConfiguration h (Ch20.scTarget singletBranchesA (fun _ => 0) ν) := by
    simp [T₂, A05.groundConfiguration, A05.jointConfiguration]
  have heqT : (S₀.erase (brLUp, k₀)).erase (brRDown, k₀) = T₂ := by
    ext ⟨ν, k⟩
    simp only [Finset.mem_erase, ne_eq, Prod.mk.injEq, hS0_mem, hT2_mem]
    fin_cases ν <;>
      simp [Ch20.scTarget_apply, Ch20.scShift, singletBranchesA, brLUp, brRDown,
        Ch07.groundConfiguration, k₀, bandZero, Subtype.ext_iff] <;> omega
  have huniq := twoSiteField_unique_pair_local h S₀ brLUp brRDown brLUp_ne_brRDown k₀ k₀
  rw [show Ch20.orderSC h b singletBranchesA x (A05.groundKet h (fun _ => 0)) =
      siteField h b brRDown x (siteField h b brLUp x (A02.ket S₀)) from rfl]
  change inner ℂ (A02.ket T₂) (siteField h b brRDown x (siteField h b brLUp x (A02.ket S₀))) = _
  rw [twoSiteField_inner_unique_local h b S₀ T₂ brLUp brRDown x k₀ k₀ ha₁ ha₂' heqT
    (fun k₁ k₂ h => huniq k₁ k₂ ⟨h.1, h.2.1, h.2.2.trans heqT.symm⟩)]
  have htw (ν : SpinBranch) : Ch06Ext.twistedCharacter (2 * h) (b ν) k₀ x = 1 := by
    simp [b, Ch06Ext.twistedCharacter, Ch06Ext.liftPhase, Ch06Ext.periodicTwist,
      A01.integerCharacter, k₀, bandZero]
  rw [htw brRDown, one_mul, one_mul, (singlet_klein_product_sign_eq h hh).2,
    normalization_sq_general h hh, div_eq_inv_mul]

/-- General-`h` spin-singlet ground-to-ground amplitudes (`eq:ch21-pair-general-sign`):
for ALL `0 < h` and `x : Fin (2 * h)`, `singletOrderSC` yields `(-1)^(h + 1) / (2 * h)` on the
channel-1 ground ket `Ω_{T_B}` and `-(-1)^(h + 1) / (2 * h)` on the mutually orthogonal
channel-2 ground ket `Ω_{T_A}`. -/
theorem singlet_pair_general_sign (h : ℕ) (hh : 0 < h) (x : Fin (2 * h)) :
    inner ℂ (A05.groundKet h (Ch20.scTarget singletBranchesB (fun _ => 0)))
      (singletOrderSC h (fun _ => Ch06Ext.periodicTwist (2 * h)) (x.val : ℤ)
        (A05.groundKet h (fun _ => 0))) = (-1 : ℂ) ^ (h + 1) / (2 * (h : ℂ)) ∧
    inner ℂ (A05.groundKet h (Ch20.scTarget singletBranchesA (fun _ => 0)))
      (singletOrderSC h (fun _ => Ch06Ext.periodicTwist (2 * h)) (x.val : ℤ)
        (A05.groundKet h (fun _ => 0))) = -((-1 : ℂ) ^ (h + 1) / (2 * (h : ℂ))) ∧
    inner ℂ (A05.groundKet h (Ch20.scTarget singletBranchesB (fun _ => 0)))
      (A05.groundKet h (Ch20.scTarget singletBranchesA (fun _ => 0))) = 0 := by
  let b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h) := fun _ => Ch06Ext.periodicTwist (2 * h)
  have h0sec : A05.groundKet h (fun _ => 0) ∈ chargeSector h (fun _ => 0) :=
    jointBudget_le_chargeSector h (fun _ => 0) 0
      (A05.ground_mem_budget h hh (fun _ => 0) (zeroCharge_admissible h) 0)
  have hTB_adm : A05.admissible h (Ch20.scTarget singletBranchesB (fun _ => 0)) := by
    intro ν; fin_cases ν <;>
      simp [Ch07.admissible, Ch20.scTarget_apply, Ch20.scShift, singletBranchesB, brLDown, brRUp] <;>
      omega
  have hTA_adm : A05.admissible h (Ch20.scTarget singletBranchesA (fun _ => 0)) := by
    intro ν; fin_cases ν <;>
      simp [Ch07.admissible, Ch20.scTarget_apply, Ch20.scShift, singletBranchesA, brLUp, brRDown] <;>
      omega
  have hTB_sec : A05.groundKet h (Ch20.scTarget singletBranchesB (fun _ => 0)) ∈
      chargeSector h (Ch20.scTarget singletBranchesB (fun _ => 0)) :=
    jointBudget_le_chargeSector h _ 0 (A05.ground_mem_budget h hh _ hTB_adm 0)
  have hTA_sec : A05.groundKet h (Ch20.scTarget singletBranchesA (fun _ => 0)) ∈
      chargeSector h (Ch20.scTarget singletBranchesA (fun _ => 0)) :=
    jointBudget_le_chargeSector h _ 0 (A05.ground_mem_budget h hh _ hTA_adm 0)
  have hcross1 : inner ℂ (A05.groundKet h (Ch20.scTarget singletBranchesB (fun _ => 0)))
      (Ch20.orderSC h b singletBranchesA (x.val : ℤ) (A05.groundKet h (fun _ => 0))) = 0 :=
    distinct_charge_sectors_orthogonal h _ _ (singlet_targets_distinct (fun _ => 0)).symm
      _ hTB_sec _ (orderSC_maps_sector_local h b singletBranchesA (x.val : ℤ) (fun _ => 0) _ h0sec)
  have hcross2 : inner ℂ (A05.groundKet h (Ch20.scTarget singletBranchesA (fun _ => 0)))
      (Ch20.orderSC h b singletBranchesB (x.val : ℤ) (A05.groundKet h (fun _ => 0))) = 0 :=
    distinct_charge_sectors_orthogonal h _ _ (singlet_targets_distinct (fun _ => 0))
      _ hTA_sec _ (orderSC_maps_sector_local h b singletBranchesB (x.val : ℤ) (fun _ => 0) _ h0sec)
  have horth : inner ℂ (A05.groundKet h (Ch20.scTarget singletBranchesB (fun _ => 0)))
      (A05.groundKet h (Ch20.scTarget singletBranchesA (fun _ => 0))) = 0 :=
    distinct_charge_sectors_orthogonal h _ _ (singlet_targets_distinct (fun _ => 0)).symm
      _ hTB_sec _ hTA_sec
  refine ⟨?_, ?_, horth⟩
  · change inner ℂ (A05.groundKet h (Ch20.scTarget singletBranchesB (fun _ => 0)))
      (singletOrderSC h b (x.val : ℤ) (A05.groundKet h (fun _ => 0))) = _
    simp only [singletOrderSC, LinearMap.sub_apply, inner_sub_right, hcross1, sub_zero]
    exact singlet_klein_sign_channel1 h hh (x.val : ℤ)
  · change inner ℂ (A05.groundKet h (Ch20.scTarget singletBranchesA (fun _ => 0)))
      (singletOrderSC h b (x.val : ℤ) (A05.groundKet h (fun _ => 0))) = _
    simp only [singletOrderSC, LinearMap.sub_apply, inner_sub_right, hcross2, zero_sub]
    rw [singlet_klein_sign_channel2 h hh (x.val : ℤ)]

/-- Clean `h = 2` specialization of `singlet_pair_general_sign` for every lattice site `x : Fin 4`:
`∓ 1/4` on the two mutually orthogonal ground targets. -/
theorem singlet_pair_general_sign_h2 (x : Fin (2 * 2)) :
    inner ℂ (A05.groundKet 2 (Ch20.scTarget singletBranchesB (fun _ => 0)))
      (singletOrderSC 2 (fun _ => Ch06Ext.periodicTwist (2 * 2)) (x.val : ℤ)
        (A05.groundKet 2 (fun _ => 0))) = -(1 / 4 : ℂ) ∧
    inner ℂ (A05.groundKet 2 (Ch20.scTarget singletBranchesA (fun _ => 0)))
      (singletOrderSC 2 (fun _ => Ch06Ext.periodicTwist (2 * 2)) (x.val : ℤ)
        (A05.groundKet 2 (fun _ => 0))) = (1 / 4 : ℂ) := by
  have h := singlet_pair_general_sign 2 (by decide) x
  refine ⟨?_, ?_⟩
  · rw [h.1]; norm_num
  · rw [h.2.1]; norm_num

/-! ## 3. Explicit Sum-Over-States Formula for `W^(2)` (`prop:ch21-sw-intermediate`) & `Ch21 → A10` Block Bridge -/

section MatrixSWIntermediate

/-- Low-subspace diagonal projector `P` selecting indices `i` with `inLow i = true`. -/
def swLowProjMatrix {ι : Type*} [DecidableEq ι] (inLow : ι → Bool) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => if inLow i then 1 else 0)

/-- High-subspace diagonal projector `Q = 1 - P` selecting indices `i` with `inLow i = false`. -/
def swHighProjMatrix {ι : Type*} [DecidableEq ι] (inLow : ι → Bool) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => if inLow i then 0 else 1)

/-- Off-diagonal perturbation matrix `V_off = P V Q + Q V P`. -/
def swOffDiagMatrix {ι : Type*} [DecidableEq ι] (inLow : ι → Bool) (V : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  fun i j => if inLow i ≠ inLow j then V i j else 0

/-- Second-order Schrieffer-Wolff effective correction matrix `W^(2) = (1/2) P [S₁, V] P`. -/
noncomputable def swSecondOrderMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (inLow : ι → Bool) (E : ι → ℝ) (V : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  let P := swLowProjMatrix inLow
  let S1 := A10.swGeneratorMatrix inLow E (swOffDiagMatrix inLow V)
  ((2 : ℂ)⁻¹) • (P * (S1 * V - V * S1) * P)

lemma swLowProjMatrix_comm_diagEnergy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (inLow : ι → Bool) (E : ι → ℝ) :
    swLowProjMatrix inLow * A10.diagEnergyMatrix E -
      A10.diagEnergyMatrix E * swLowProjMatrix inLow = 0 := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.zero_apply, swLowProjMatrix, A10.diagEnergyMatrix,
    Matrix.diagonal_mul_diagonal]
  by_cases hij : i = j
  · subst hij; simp [mul_comm]
  · simp [hij]

lemma swOffDiagMatrix_eq_block {ι : Type*} [Fintype ι] [DecidableEq ι]
    (inLow : ι → Bool) (V : Matrix ι ι ℂ) :
    swOffDiagMatrix inLow V =
      swLowProjMatrix inLow * V * swHighProjMatrix inLow +
        swHighProjMatrix inLow * V * swLowProjMatrix inLow := by
  ext i j
  simp only [swOffDiagMatrix, Matrix.add_apply, swLowProjMatrix, swHighProjMatrix,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  cases hi : inLow i <;> cases hj : inLow j <;> simp

lemma swOffDiagMatrix_conjTranspose {ι : Type*} [DecidableEq ι]
    (inLow : ι → Bool) (V : Matrix ι ι ℂ) (hHerm : Matrix.conjTranspose V = V) :
    Matrix.conjTranspose (swOffDiagMatrix inLow V) = swOffDiagMatrix inLow V := by
  ext i j
  have hs : star (V j i) = V i j := congrFun (congrFun hHerm i) j
  change star (swOffDiagMatrix inLow V j i) = swOffDiagMatrix inLow V i j
  unfold swOffDiagMatrix
  by_cases h : inLow i ≠ inLow j
  · simp [h, h.symm, hs]
  · have he : inLow j = inLow i := (not_ne_iff.mp h).symm
    simp [he]

lemma sw_generator_matrix_commutator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (inLow : ι → Bool) (E : ι → ℝ) (V : Matrix ι ι ℂ)
    (hNonRes : A10.nonResonant inLow E (swOffDiagMatrix inLow V)) :
    A10.swGeneratorMatrix inLow E (swOffDiagMatrix inLow V) * A10.diagEnergyMatrix E -
      A10.diagEnergyMatrix E * A10.swGeneratorMatrix inLow E (swOffDiagMatrix inLow V) =
      -swOffDiagMatrix inLow V :=
  A10.sw_generator_commutator_eq inLow E (swOffDiagMatrix inLow V)
    (fun i j hij => by simp [swOffDiagMatrix, hij]) hNonRes

lemma sw_generator_matrix_skew_hermitian {ι : Type*} [DecidableEq ι]
    (inLow : ι → Bool) (E : ι → ℝ) (V : Matrix ι ι ℂ)
    (hHerm : Matrix.conjTranspose V = V) :
    Matrix.conjTranspose (A10.swGeneratorMatrix inLow E (swOffDiagMatrix inLow V)) =
      -A10.swGeneratorMatrix inLow E (swOffDiagMatrix inLow V) :=
  A10.sw_generator_skew_hermitian inLow E (swOffDiagMatrix inLow V)
    (swOffDiagMatrix_conjTranspose inLow V hHerm)

/-- Proposition `prop:ch21-sw-intermediate` (`eq:ch21-sw-intermediate-sum`):
explicit sum-over-`I_Q` matrix-entry formula for `W^(2) = (1/2) P [S₁, V] P` on `l, l' ∈ I_P`,
with every denominator strictly nonzero under `A10.nonResonant`. -/
theorem sw_second_order_intermediate_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (inLow : ι → Bool) (E : ι → ℝ) (V : Matrix ι ι ℂ)
    (hNonRes : A10.nonResonant inLow E (swOffDiagMatrix inLow V))
    (l l' : ι) (hl : inLow l = true) (hl' : inLow l' = true) :
    swSecondOrderMatrix inLow E V l l' =
      ((2 : ℂ)⁻¹) *
        ∑ μ ∈ Finset.univ.filter (fun μ => inLow μ = false ∧ V l μ * V μ l' ≠ 0),
          V l μ * V μ l' *
            ((((E l - E μ : ℝ) : ℂ))⁻¹ + (((E l' - E μ : ℝ) : ℂ))⁻¹) ∧
    (∀ μ ∈ Finset.univ.filter (fun μ => inLow μ = false ∧ V l μ * V μ l' ≠ 0),
      E l ≠ E μ ∧ E l' ≠ E μ) := by
  have hden : ∀ μ ∈ Finset.univ.filter (fun μ => inLow μ = false ∧ V l μ * V μ l' ≠ 0),
      E l ≠ E μ ∧ E l' ≠ E μ := by
    intro μ hμ
    rcases (Finset.mem_filter.mp hμ).2 with ⟨hQ, hprod⟩
    have h1 : V l μ ≠ 0 := left_ne_zero_of_mul hprod
    have h2 : V μ l' ≠ 0 := right_ne_zero_of_mul hprod
    have hne1 : inLow l ≠ inLow μ := by rw [hl, hQ]; decide
    have hne2 : inLow μ ≠ inLow l' := by rw [hQ, hl']; decide
    exact ⟨hNonRes l μ hne1 (by simp [swOffDiagMatrix, hne1, h1]),
      (hNonRes μ l' hne2 (by simp [swOffDiagMatrix, hne2, h2])).symm⟩
  refine ⟨?_, hden⟩
  dsimp only [swSecondOrderMatrix]
  rw [Matrix.smul_apply, smul_eq_mul]
  congr 1
  rw [swLowProjMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [hl, hl', ↓reduceIte, one_mul, mul_one, Matrix.sub_apply, Matrix.mul_apply,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro μ _
  by_cases hQ : inLow μ = false
  · have hne1 : inLow l ≠ inLow μ := by rw [hl, hQ]; decide
    have hne2 : inLow μ ≠ inLow l' := by rw [hQ, hl']; decide
    by_cases hprod : V l μ * V μ l' ≠ 0
    · have h1 : V l μ ≠ 0 := left_ne_zero_of_mul hprod
      have h2 : V μ l' ≠ 0 := right_ne_zero_of_mul hprod
      rw [ite_eq_left ⟨hQ, hprod⟩]
      have hS1 : A10.swGeneratorMatrix inLow E (swOffDiagMatrix inLow V) l μ =
          V l μ / ((E l - E μ : ℝ) : ℂ) := by
        simp [A10.swGeneratorMatrix, swOffDiagMatrix, hne1, h1]
      have hS2 : A10.swGeneratorMatrix inLow E (swOffDiagMatrix inLow V) μ l' =
          -(V μ l' / ((E l' - E μ : ℝ) : ℂ)) := by
        have hsub : ((E μ - E l' : ℝ) : ℂ) = -((E l' - E μ : ℝ) : ℂ) := by push_cast; ring
        simp only [A10.swGeneratorMatrix, swOffDiagMatrix, hne2, h2, ne_eq, not_false_eq_true,
          and_self, ↓reduceIte]
        rw [hsub, div_neg]
      rw [hS1, hS2]
      ring
    · rw [ite_eq_right (fun h => hprod h.2)]
      rcases mul_eq_zero.mp (not_ne_iff.mp hprod) with h1 | h2
      · simp [A10.swGeneratorMatrix, swOffDiagMatrix, h1]
      · simp [A10.swGeneratorMatrix, swOffDiagMatrix, h2]
  · have hT : inLow μ = true := by cases h : inLow μ <;> simp_all
    rw [ite_eq_right (fun h => hQ h.1)]
    have he1 : inLow l = inLow μ := by rw [hl, hT]
    have he2 : inLow μ = inLow l' := by rw [hT, hl']
    simp [A10.swGeneratorMatrix, he1, he2]

/-- Proposition `prop:ch21-sw-intermediate` (`eq:ch21-sw-diagonal-shift`):
for Hermitian `V`, the diagonal second-order energy shift on `l ∈ I_P` is
`⟨l | W^(2) | l⟩ = ∑_{μ ∈ I_Q, V_{lμ} ≠ 0} ‖V_{lμ}‖² / (E_l - E_μ)`. -/
theorem sw_second_order_diagonal_shift {ι : Type*} [Fintype ι] [DecidableEq ι]
    (inLow : ι → Bool) (E : ι → ℝ) (V : Matrix ι ι ℂ)
    (hHerm : Matrix.conjTranspose V = V)
    (hNonRes : A10.nonResonant inLow E (swOffDiagMatrix inLow V))
    (l : ι) (hl : inLow l = true) :
    swSecondOrderMatrix inLow E V l l =
      ∑ μ ∈ Finset.univ.filter (fun μ => inLow μ = false ∧ V l μ ≠ 0),
        ((‖V l μ‖ ^ 2 : ℝ) : ℂ) / ((E l - E μ : ℝ) : ℂ) := by
  have hsum := (sw_second_order_intermediate_sum inLow E V hNonRes l l hl hl).1
  rw [hsum, Finset.mul_sum]
  have hVadj (μ : ι) : V μ l = star (V l μ) := by
    have hs : star (V μ l) = V l μ := congrFun (congrFun hHerm l) μ
    simpa only [star_star] using congrArg star hs
  have hfilt :
      Finset.univ.filter (fun μ => inLow μ = false ∧ V l μ * V μ l ≠ 0) =
        Finset.univ.filter (fun μ => inLow μ = false ∧ V l μ ≠ 0) := by
    ext μ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hVadj μ, ne_eq, mul_eq_zero,
      star_eq_zero, or_self]
  rw [hfilt]
  apply Finset.sum_congr rfl
  intro μ _
  rw [hVadj μ]
  have hnorm : V l μ * star (V l μ) = ((‖V l μ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hnorm]
  ring

/-- Strictly ordered baseline spectrum (`E_l < E_μ` on every coupled `μ ∈ I_Q`) implies
that the diagonal second-order shift is real and nonpositive (`21.4.tex` L397–399). -/
theorem sw_second_order_diagonal_nonpos_of_ordered {ι : Type*} [Fintype ι] [DecidableEq ι]
    (inLow : ι → Bool) (E : ι → ℝ) (V : Matrix ι ι ℂ)
    (hHerm : Matrix.conjTranspose V = V)
    (hNonRes : A10.nonResonant inLow E (swOffDiagMatrix inLow V))
    (l : ι) (hl : inLow l = true)
    (hOrd : ∀ μ : ι, inLow μ = false → V l μ ≠ 0 → E l < E μ) :
    (swSecondOrderMatrix inLow E V l l).re ≤ 0 ∧
    (swSecondOrderMatrix inLow E V l l).im = 0 := by
  rw [sw_second_order_diagonal_shift inLow E V hHerm hNonRes l hl]
  have hcast :
      (∑ μ ∈ Finset.univ.filter (fun μ => inLow μ = false ∧ V l μ ≠ 0),
          ((‖V l μ‖ ^ 2 : ℝ) : ℂ) / ((E l - E μ : ℝ) : ℂ)) =
        (((∑ μ ∈ Finset.univ.filter (fun μ => inLow μ = false ∧ V l μ ≠ 0),
            ‖V l μ‖ ^ 2 / (E l - E μ) : ℝ) : ℂ)) := by
    push_cast
    rfl
  rw [hcast, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, rfl⟩
  apply Finset.sum_nonpos
  intro μ hμ
  rcases (Finset.mem_filter.mp hμ).2 with ⟨hQ, hne⟩
  have hlt : E l - E μ < 0 := sub_neg.mpr (hOrd μ hQ hne)
  exact div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hlt.le

end MatrixSWIntermediate

/-! ### 3.1 Concrete `Ch21 → A10` Spinful Umklapp Block Bridge (`h > 0` and `h = 2`) -/

/-- Spinful total relative-energy free-fermion Hamiltonian `H₀ = ∑_ν (H_ν - E_{sea})`
on `A05.FockSpace SpinBranch h`. -/
noncomputable def spinfulFreeHamiltonian (h : ℕ) : A05.Operators SpinBranch h :=
  @A03.diagonal (A05.Mode SpinBranch h) _ instDecidableEqProd
    (fun S => ((∑ ν : SpinBranch, Ch07.relativeEnergy h (Ch07.speciesConfiguration h S ν) : ℤ) : ℂ))

lemma spinfulFreeHamiltonian_self_adjoint (h : ℕ) :
    LinearMap.adjoint (spinfulFreeHamiltonian h) = spinfulFreeHamiltonian h := by
  unfold spinfulFreeHamiltonian
  rw [@A03.diagonal_adjoint (A05.Mode SpinBranch h) _ instDecidableEqProd]
  congr 1
  funext S
  simp

lemma spinfulFreeHamiltonian_ground_zero (h : ℕ) (hh : 0 < h) :
    spinfulFreeHamiltonian h (A05.groundKet h (fun _ => 0)) = 0 := by
  have h0adm : Ch07.admissible h 0 := by unfold Ch07.admissible; omega
  rw [A05.groundKet, ← ket_prod_eq_local, spinfulFreeHamiltonian,
    @A03.diagonal_ket (A05.Mode SpinBranch h) _ instDecidableEqProd]
  have hsum : (∑ ν : SpinBranch,
      Ch07.relativeEnergy h (Ch07.speciesConfiguration h (A05.groundConfiguration h (fun _ => 0)) ν)) = 0 := by
    apply Finset.sum_eq_zero
    intro ν _
    rw [A05.groundConfiguration,
      A05.species_joint_configuration h (fun _ => Ch07.groundConfiguration h 0) ν,
      Ch07.ground_configuration_energy h hh 0 h0adm]
    simp [Ch07.groundEnergy]
  rw [hsum]
  simp

private lemma umklappTargetSpeciesConfig_rel_and_exc (h : ℕ) (hh : 0 < h) (ν : SpinBranch) :
    (Ch07.relativeEnergy h (umklappTargetSpeciesConfig h hh ν) =
      if ν = brLUp ∨ ν = brLDown then 1 else (h : ℤ) - 1) ∧
    (Ch07.excitationEnergy h (umklappTargetSpeciesConfig h hh ν) =
      if ν = brLUp ∨ ν = brLDown then 0 else (h : ℤ) - 1) := by
  have h0adm : Ch07.admissible h 0 := by unfold Ch07.admissible; omega
  have h1adm : Ch07.admissible h 1 := by unfold Ch07.admissible; omega
  by_cases hL : ν = brLUp ∨ ν = brLDown
  · simp only [umklappTargetSpeciesConfig, hL, ↓reduceIte]
    refine ⟨?_, Ch07.ground_configuration_excitation h hh 1 h1adm⟩
    rw [Ch07.ground_configuration_energy h hh 1 h1adm]
    simp [Ch07.groundEnergy]
  · simp only [umklappTargetSpeciesConfig, hL, ↓reduceIte]
    have hmem := witnessLowerMode_mem_ground_zero h hh
    have hchg0 := Ch07.ground_configuration_charge h hh 0 h0adm
    have hexc0 := Ch07.ground_configuration_excitation h hh 0 h0adm
    have hexc : Ch07.excitationEnergy h ((Ch07.groundConfiguration h 0).erase (witnessLowerMode h hh)) =
        (h : ℤ) - 1 := by
      rw [Ch07.excitation_erase h _ _ hmem, hexc0, hchg0]
      dsimp [witnessLowerMode]
      ring
    have hchg : Ch07.relativeCharge h ((Ch07.groundConfiguration h 0).erase (witnessLowerMode h hh)) = -1 := by
      rw [Ch07.charge_erase h _ _ hmem, hchg0]; ring
    refine ⟨?_, hexc⟩
    have hg : Ch07.groundEnergy (-1) = 0 := by simp [Ch07.groundEnergy]
    unfold Ch07.excitationEnergy at hexc
    rw [hchg, hg, sub_zero] at hexc
    exact hexc

/-- The Umklapp target witness `|Ψ_target⟩` lies in `A05.jointBudget h (+1,+1,-1,-1) (2 * (h - 1))`. -/
lemma umklappZeroChargeWitness_mem_budget (h : ℕ) (hh : 0 < h) :
    umklappZeroChargeWitness h hh ∈
      A05.jointBudget h (umklappForwardTarget (fun _ => 0)) (2 * (h - 1)) := by
  rw [umklappZeroChargeWitness, A05.jointBudget, Ch07.species_budget_ket]
  have hspec (ν : SpinBranch) :
      Ch07.speciesConfiguration h (umklappTargetConfig h hh) ν =
        umklappTargetSpeciesConfig h hh ν :=
    A05.species_joint_configuration h (umklappTargetSpeciesConfig h hh) ν
  refine ⟨fun ν => by rw [hspec ν]; exact umklappTargetSpeciesConfig_charge h hh ν, ?_⟩
  unfold Ch07.totalExcitation
  rw [Fin.sum_univ_four]
  change Ch07.excitationEnergy h (Ch07.speciesConfiguration h (umklappTargetConfig h hh) brLUp) +
      Ch07.excitationEnergy h (Ch07.speciesConfiguration h (umklappTargetConfig h hh) brLDown) +
      Ch07.excitationEnergy h (Ch07.speciesConfiguration h (umklappTargetConfig h hh) brRUp) +
      Ch07.excitationEnergy h (Ch07.speciesConfiguration h (umklappTargetConfig h hh) brRDown) ≤ _
  rw [hspec brLUp, hspec brLDown, hspec brRUp, hspec brRDown,
    (umklappTargetSpeciesConfig_rel_and_exc h hh brLUp).2,
    (umklappTargetSpeciesConfig_rel_and_exc h hh brLDown).2,
    (umklappTargetSpeciesConfig_rel_and_exc h hh brRUp).2,
    (umklappTargetSpeciesConfig_rel_and_exc h hh brRDown).2]
  have h2 : ¬ (brRUp = brLUp ∨ brRUp = brLDown) := by decide
  have h3 : ¬ (brRDown = brLUp ∨ brRDown = brLDown) := by decide
  simp only [true_or, or_true, ↓reduceIte, ite_eq_right h2, ite_eq_right h3]
  omega

/-- Exact free-fermion energy eigenvalue of `umklappZeroChargeWitness h hh`:
`H₀ |Ψ_target⟩ = (2 * h) • |Ψ_target⟩` (at `h = 2`, `E = 4`). -/
lemma spinfulFreeHamiltonian_umklappWitness (h : ℕ) (hh : 0 < h) :
    spinfulFreeHamiltonian h (umklappZeroChargeWitness h hh) =
      (2 * (h : ℂ)) • umklappZeroChargeWitness h hh := by
  rw [umklappZeroChargeWitness, spinfulFreeHamiltonian,
    @A03.diagonal_ket (A05.Mode SpinBranch h) _ instDecidableEqProd]
  have hspec (ν : SpinBranch) :
      Ch07.speciesConfiguration h (umklappTargetConfig h hh) ν =
        umklappTargetSpeciesConfig h hh ν :=
    A05.species_joint_configuration h (umklappTargetSpeciesConfig h hh) ν
  have hsum : (∑ ν : SpinBranch,
      Ch07.relativeEnergy h (Ch07.speciesConfiguration h (umklappTargetConfig h hh) ν)) =
      2 * (h : ℤ) := by
    rw [Fin.sum_univ_four]
    change Ch07.relativeEnergy h (Ch07.speciesConfiguration h (umklappTargetConfig h hh) brLUp) +
        Ch07.relativeEnergy h (Ch07.speciesConfiguration h (umklappTargetConfig h hh) brLDown) +
        Ch07.relativeEnergy h (Ch07.speciesConfiguration h (umklappTargetConfig h hh) brRUp) +
        Ch07.relativeEnergy h (Ch07.speciesConfiguration h (umklappTargetConfig h hh) brRDown) = _
    rw [hspec brLUp, hspec brLDown, hspec brRUp, hspec brRDown,
      (umklappTargetSpeciesConfig_rel_and_exc h hh brLUp).1,
      (umklappTargetSpeciesConfig_rel_and_exc h hh brLDown).1,
      (umklappTargetSpeciesConfig_rel_and_exc h hh brRUp).1,
      (umklappTargetSpeciesConfig_rel_and_exc h hh brRDown).1]
    have h2 : ¬ (brRUp = brLUp ∨ brRUp = brLDown) := by decide
    have h3 : ¬ (brRDown = brLUp ∨ brRDown = brLDown) := by decide
    simp only [true_or, or_true, ↓reduceIte, ite_eq_right h2, ite_eq_right h3]
    ring
  rw [hsum]
  push_cast
  rfl

/-- Two-state spinful Umklapp-coupled orthonormal basis `{|Ω₀⟩, |Ψ_target⟩}` on `FockSpace`. -/
noncomputable def umklappBlockBasis (h : ℕ) (hh : 0 < h) : Fin 2 → A05.FockSpace SpinBranch h
  | ⟨0, _⟩ => A05.groundKet h (fun _ => 0)
  | ⟨1, _⟩ => umklappZeroChargeWitness h hh

/-- Low-space indicator selecting `|Ω₀⟩` (`i = 0`) as `I_P` and `|Ψ_target⟩` (`i = 1`) as `I_Q`. -/
def umklappBlockInLow : Fin 2 → Bool
  | ⟨0, _⟩ => true
  | ⟨1, _⟩ => false

/-- Baseline energies `E(0) = 0`, `E(1) = 2 * h` of the spinful Umklapp-coupled block. -/
def umklappBlockEnergy (h : ℕ) : Fin 2 → ℝ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => (2 * h : ℝ)

/-- Compressed `2×2` matrix of `spinfulFreeHamiltonian h` on `{|Ω₀⟩, |Ψ_target⟩}`. -/
noncomputable def umklappBlockH0Matrix (h : ℕ) (hh : 0 < h) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => inner ℂ (umklappBlockBasis h hh i) (spinfulFreeHamiltonian h (umklappBlockBasis h hh j))

/-- Compressed `2×2` matrix of `periodicUmklappOp h gU` on `{|Ω₀⟩, |Ψ_target⟩}`. -/
noncomputable def umklappBlockVMatrix (h : ℕ) (hh : 0 < h) (gU : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => inner ℂ (umklappBlockBasis h hh i) (periodicUmklappOp h gU (umklappBlockBasis h hh j))

lemma umklappBlock_orthonormal (h : ℕ) (hh : 0 < h) (i j : Fin 2) :
    inner ℂ (umklappBlockBasis h hh i) (umklappBlockBasis h hh j) = if i = j then 1 else 0 := by
  have h01 : inner ℂ (umklappZeroChargeWitness h hh) (A05.groundKet h (fun _ => 0)) = 0 :=
    umklappZeroChargeWitness_orthogonal_zero_budget h hh 0 _
      (A05.ground_mem_budget h hh (fun _ => 0) (zeroCharge_admissible h) 0)
  have h10 : inner ℂ (A05.groundKet h (fun _ => 0)) (umklappZeroChargeWitness h hh) = 0 := by
    rw [← inner_conj_symm, h01, map_zero]
  fin_cases i <;> fin_cases j
  · change inner ℂ (A05.groundKet h (fun _ => 0)) (A05.groundKet h (fun _ => 0)) = 1
    rw [A05.groundKet, A02.ket_inner]; simp
  · simp [umklappBlockBasis, h10]
  · simp [umklappBlockBasis, h01]
  · change inner ℂ (umklappZeroChargeWitness h hh) (umklappZeroChargeWitness h hh) = 1
    rw [umklappZeroChargeWitness,
      @A02.ket_inner (A05.Mode SpinBranch h) _ instDecidableEqProd]; simp

lemma umklappBlockH0Matrix_eq_diag (h : ℕ) (hh : 0 < h) :
    umklappBlockH0Matrix h hh = A10.diagEnergyMatrix (umklappBlockEnergy h) := by
  ext i j
  unfold umklappBlockH0Matrix A10.diagEnergyMatrix
  have h01 := umklappBlock_orthonormal h hh 0 1
  have h11 := umklappBlock_orthonormal h hh 1 1
  simp only [umklappBlockBasis] at h01 h11
  have h01' : inner ℂ (A05.groundKet h (fun _ => 0)) (umklappZeroChargeWitness h hh) = 0 := by
    simpa using h01
  have h11' : inner ℂ (umklappZeroChargeWitness h hh) (umklappZeroChargeWitness h hh) = 1 := by
    simpa using h11
  fin_cases i <;> fin_cases j
  · simp [umklappBlockBasis, umklappBlockEnergy, spinfulFreeHamiltonian_ground_zero h hh]
  · simp [umklappBlockBasis, spinfulFreeHamiltonian_umklappWitness h hh, inner_smul_right, h01']
  · simp [umklappBlockBasis, spinfulFreeHamiltonian_ground_zero h hh]
  · simp only [umklappBlockBasis, umklappBlockEnergy, Matrix.diagonal_apply, ↓reduceIte,
      spinfulFreeHamiltonian_umklappWitness h hh, inner_smul_right, h11', mul_one]
    push_cast; rfl

lemma umklappBlockVMatrix_explicit (h : ℕ) (hh : 0 < h) (gU : ℝ) :
    umklappBlockVMatrix h hh gU =
      !![0, -((gU : ℂ) / ((2 * (h : ℂ)) ^ 2));
         -((gU : ℂ) / ((2 * (h : ℂ)) ^ 2)), 0] := by
  have h00 : inner ℂ (A05.groundKet h (fun _ => 0))
      (periodicUmklappOp h gU (A05.groundKet h (fun _ => 0))) = 0 :=
    umklappOp_charge_diagonal_zero h _ gU (fun _ => 0) 0 0
      _ (A05.ground_mem_budget h hh (fun _ => 0) (zeroCharge_admissible h) 0)
      _ (A05.ground_mem_budget h hh (fun _ => 0) (zeroCharge_admissible h) 0)
  have h11 : inner ℂ (umklappZeroChargeWitness h hh)
      (periodicUmklappOp h gU (umklappZeroChargeWitness h hh)) = 0 :=
    umklappOp_charge_diagonal_zero h _ gU (umklappForwardTarget (fun _ => 0))
      (2 * (h - 1)) (2 * (h - 1))
      _ (umklappZeroChargeWitness_mem_budget h hh)
      _ (umklappZeroChargeWitness_mem_budget h hh)
  have h10 : inner ℂ (umklappZeroChargeWitness h hh)
      (periodicUmklappOp h gU (A05.groundKet h (fun _ => 0))) =
      -((gU : ℂ) / ((2 * (h : ℂ)) ^ 2)) :=
    umklapp_zero_charge_witness_coeff h hh gU
  have h01 : inner ℂ (A05.groundKet h (fun _ => 0))
      (periodicUmklappOp h gU (umklappZeroChargeWitness h hh)) =
      -((gU : ℂ) / ((2 * (h : ℂ)) ^ 2)) := by
    have hadj : inner ℂ (A05.groundKet h (fun _ => 0))
        (periodicUmklappOp h gU (umklappZeroChargeWitness h hh)) =
        inner ℂ (periodicUmklappOp h gU (A05.groundKet h (fun _ => 0)))
          (umklappZeroChargeWitness h hh) := by
      rw [← LinearMap.adjoint_inner_left, periodicUmklappOp, umklappOp_self_adjoint]
    rw [hadj, ← inner_conj_symm, h10]
    simp only [map_neg, map_div₀, map_pow, map_mul, map_ofNat, Complex.conj_ofReal,
      Complex.conj_natCast]
  ext i j
  unfold umklappBlockVMatrix
  fin_cases i <;> fin_cases j <;> simp [umklappBlockBasis, h00, h01, h10, h11]

/-- All `A10` finite-matrix hypotheses (`[P, H₀] = 0`, Hermiticity, pure off-diagonal block,
and `A10.nonResonant`) hold unconditionally on the spinful `Ch21` Umklapp block for every `0 < h`. -/
theorem umklappBlock_a10_hypotheses (h : ℕ) (hh : 0 < h) (gU : ℝ) :
    (swLowProjMatrix umklappBlockInLow * umklappBlockH0Matrix h hh -
      umklappBlockH0Matrix h hh * swLowProjMatrix umklappBlockInLow = 0) ∧
    Matrix.conjTranspose (umklappBlockVMatrix h hh gU) = umklappBlockVMatrix h hh gU ∧
    swOffDiagMatrix umklappBlockInLow (umklappBlockVMatrix h hh gU) = umklappBlockVMatrix h hh gU ∧
    A10.nonResonant umklappBlockInLow (umklappBlockEnergy h)
      (swOffDiagMatrix umklappBlockInLow (umklappBlockVMatrix h hh gU)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [umklappBlockH0Matrix_eq_diag h hh]
    exact swLowProjMatrix_comm_diagEnergy umklappBlockInLow (umklappBlockEnergy h)
  · rw [umklappBlockVMatrix_explicit h hh gU]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · rw [umklappBlockVMatrix_explicit h hh gU]
    ext i j; fin_cases i <;> fin_cases j <;> simp [swOffDiagMatrix, umklappBlockInLow]
  · intro i j hij _
    have hhR : (0 : ℝ) < (h : ℝ) := Nat.cast_pos.mpr hh
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simp [umklappBlockEnergy]; linarith
    · simp [umklappBlockEnergy]; linarith
    · exact absurd rfl hij

/-- Full `A10` generator & second-order energy shift evaluation on the spinful `Ch21` Umklapp block:
`[S₁, H₀] = -V`, `S₁† = -S₁`, and `⟨Ω₀ | W^(2) | Ω₀⟩ = -g_U² / (32 h⁵)`. -/
theorem umklappBlock_sw_generator_and_shift (h : ℕ) (hh : 0 < h) (gU : ℝ) :
    let H0 := umklappBlockH0Matrix h hh
    let V := umklappBlockVMatrix h hh gU
    let S1 := A10.swGeneratorMatrix umklappBlockInLow (umklappBlockEnergy h)
      (swOffDiagMatrix umklappBlockInLow V)
    S1 * H0 - H0 * S1 = -V ∧
    Matrix.conjTranspose S1 = -S1 ∧
    swSecondOrderMatrix umklappBlockInLow (umklappBlockEnergy h) V 0 0 =
      -(((gU : ℂ) ^ 2) / (32 * (h : ℂ) ^ 5)) := by
  dsimp only
  have hhyp := umklappBlock_a10_hypotheses h hh gU
  refine ⟨?_, ?_, ?_⟩
  · have hcomm := sw_generator_matrix_commutator umklappBlockInLow (umklappBlockEnergy h)
      (umklappBlockVMatrix h hh gU) hhyp.2.2.2
    rw [umklappBlockH0Matrix_eq_diag h hh, hcomm, hhyp.2.2.1]
  · exact sw_generator_matrix_skew_hermitian umklappBlockInLow (umklappBlockEnergy h)
      (umklappBlockVMatrix h hh gU) hhyp.2.1
  · rw [sw_second_order_diagonal_shift umklappBlockInLow (umklappBlockEnergy h)
      (umklappBlockVMatrix h hh gU) hhyp.2.1 hhyp.2.2.2 0 rfl]
    have hV01 : umklappBlockVMatrix h hh gU 0 1 = -((gU : ℂ) / ((2 * (h : ℂ)) ^ 2)) := by
      rw [umklappBlockVMatrix_explicit h hh gU]; simp
    have hhC : (h : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hh)
    by_cases hg : gU = 0
    · subst hg
      have hV01z : umklappBlockVMatrix h hh 0 0 1 = 0 := by simp [hV01]
      have hfilt :
          Finset.univ.filter (fun μ : Fin 2 =>
            umklappBlockInLow μ = false ∧ umklappBlockVMatrix h hh 0 0 μ ≠ 0) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro μ _
        fin_cases μ
        · intro ⟨h0, _⟩; exact absurd h0 (by decide)
        · intro ⟨_, h1⟩; exact h1 hV01z
      rw [hfilt, Finset.sum_empty]
      simp
    · have hV01ne : umklappBlockVMatrix h hh gU 0 1 ≠ 0 := by
        rw [hV01]
        exact neg_ne_zero.mpr (div_ne_zero (Complex.ofReal_ne_zero.mpr hg)
          (pow_ne_zero 2 (mul_ne_zero two_ne_zero hhC)))
      have hfilt :
          Finset.univ.filter (fun μ : Fin 2 =>
            umklappBlockInLow μ = false ∧ umklappBlockVMatrix h hh gU 0 μ ≠ 0) = {1} := by
        ext μ
        rw [Finset.mem_filter, Finset.mem_singleton]
        fin_cases μ
        · constructor
          · rintro ⟨_, h0, _⟩; exact absurd h0 (by decide)
          · intro h0; exact absurd h0 (by decide)
        · constructor
          · intro _; rfl
          · intro _; exact ⟨Finset.mem_univ _, rfl, hV01ne⟩
      rw [hfilt, Finset.sum_singleton, hV01]
      have hnorm : ‖-((gU : ℂ) / ((2 * (h : ℂ)) ^ 2))‖ ^ 2 = (gU ^ 2) / ((2 * (h : ℝ)) ^ 4) := by
        rw [norm_neg, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          norm_mul, Complex.norm_ofNat, Complex.norm_natCast, div_pow, sq_abs]
        ring
      rw [hnorm]
      simp only [umklappBlockEnergy]
      push_cast
      field_simp [hhC]
      ring

/-- Concrete `h = 2` specialization of the spinful `Ch21 → A10` Umklapp block bridge:
`E = [0, 4]`, `V_{01} = V_{10} = -g_U / 16`, and `⟨Ω₀ | W^(2) | Ω₀⟩ = -g_U² / 1024`. -/
theorem umklappBlock_sw_h2 (gU : ℝ) :
    umklappBlockH0Matrix 2 (by decide) = !![0, 0; 0, 4] ∧
    umklappBlockVMatrix 2 (by decide) gU =
      !![0, -((gU : ℂ) / 16); -((gU : ℂ) / 16), 0] ∧
    swSecondOrderMatrix umklappBlockInLow (umklappBlockEnergy 2)
      (umklappBlockVMatrix 2 (by decide) gU) 0 0 = -(((gU : ℂ) ^ 2) / 1024) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [umklappBlockH0Matrix_eq_diag 2 (by decide)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A10.diagEnergyMatrix, umklappBlockEnergy]
    norm_num
  · rw [umklappBlockVMatrix_explicit 2 (by decide) gU]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> norm_num
  · rw [(umklappBlock_sw_generator_and_shift 2 (by decide) gU).2.2]
    norm_num

/-! ### 3.2 Operator-Level `A10.sw_compressed_bch_second_order` Instantiation on `A05.Operators SpinBranch h` -/

/-- Orthogonal coordinate projector `Π_block` onto the 2-state spinful Umklapp block `{S₀, S_target}`. -/
noncomputable def umklappBlockProj (h : ℕ) (hh : 0 < h) : A05.Operators SpinBranch h :=
  @A03.coordinateProjection (A05.Mode SpinBranch h) _ instDecidableEqProd
    {A05.groundConfiguration h (fun _ => 0), umklappTargetConfig h hh}

/-- Block-projected spinful Umklapp perturbation `Π_block H_U(g_U) Π_block` on `FockSpace`. -/
noncomputable def umklappBlockVOp (h : ℕ) (hh : 0 < h) (gU : ℝ) : A05.Operators SpinBranch h :=
  umklappBlockProj h hh * periodicUmklappOp h gU * umklappBlockProj h hh

/-- Explicit skew-Hermitian Schrieffer-Wolff generator `S₁` on `A05.Operators SpinBranch h`
for the spinful Umklapp block: `S₁ |Ω₀⟩ = (c / (2h)) |Ψ_target⟩`, `S₁ |Ψ_target⟩ = -(c / (2h)) |Ω₀⟩`,
with `c = -g_U / (2h)²`. -/
noncomputable def umklappBlockS1Op (h : ℕ) (hh : 0 < h) (gU : ℝ) : A05.Operators SpinBranch h :=
  let c : ℂ := -((gU : ℂ) / ((2 * (h : ℂ)) ^ 2))
  let s : ℂ := c / (2 * (h : ℂ))
  @A02.extendBasis (A05.Mode SpinBranch h) _ instDecidableEqProd (fun S =>
    if S = A05.groundConfiguration h (fun _ => 0) then
      s • umklappZeroChargeWitness h hh
    else if S = umklappTargetConfig h hh then
      (-s) • A05.groundKet h (fun _ => 0)
    else 0)

private lemma umklappTargetConfig_ne_ground0 (h : ℕ) (hh : 0 < h) :
    umklappTargetConfig h hh ≠ A05.groundConfiguration h (fun _ : SpinBranch => (0 : ℤ)) := by
  intro heq
  have h1 := umklappZeroChargeWitness_orthogonal_zero_budget h hh 0 _
    (A05.ground_mem_budget h hh (fun _ => 0) (zeroCharge_admissible h) 0)
  rw [umklappZeroChargeWitness, heq, ket_prod_eq_local] at h1
  have hne : A05.groundKet h (fun _ : SpinBranch => (0 : ℤ)) ≠ 0 :=
    A05.ground_ne_zero h (fun _ : SpinBranch => (0 : ℤ))
  exact hne (inner_self_eq_zero.mp h1)

private lemma budgetSet_zero_eq_singleton (h : ℕ) (hh : 0 < h) :
    Ch14.budgetSet h (fun _ : SpinBranch => (0 : ℤ)) 0 =
      {A05.groundConfiguration h (fun _ : SpinBranch => (0 : ℤ))} := by
  ext S
  simp only [Ch14.budgetSet, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hchg, htot⟩
    rw [← A05.joint_species_configuration h S]
    unfold A05.groundConfiguration
    congr 1
    funext ν
    have hle : Ch07.excitationEnergy h (Ch07.speciesConfiguration h S ν) ≤ 0 := by
      have hsingle : Ch07.excitationEnergy h (Ch07.speciesConfiguration h S ν) ≤
          Ch07.totalExcitation h S :=
        Finset.single_le_sum (f := fun η => Ch07.excitationEnergy h (Ch07.speciesConfiguration h S η))
          (fun η _ => Ch07.excitation_nonneg h hh _) (Finset.mem_univ ν)
      exact le_trans hsingle (by simpa using htot)
    have hnn := Ch07.excitation_nonneg h hh (Ch07.speciesConfiguration h S ν)
    have he0 : Ch07.excitationEnergy h (Ch07.speciesConfiguration h S ν) = 0 := by omega
    have hgr := (Ch07.excitation_zero_iff_ground h hh _).mp he0
    rw [hchg ν] at hgr
    exact hgr
  · intro hS
    subst hS
    have h0adm : Ch07.admissible h 0 := by unfold Ch07.admissible; omega
    refine ⟨fun ν => by
      rw [A05.groundConfiguration, A05.species_joint_configuration h _ ν]
      exact Ch07.ground_configuration_charge h hh 0 h0adm, ?_⟩
    unfold Ch07.totalExcitation A05.groundConfiguration
    simp only [A05.species_joint_configuration, Ch07.ground_configuration_excitation h hh 0 h0adm,
      Finset.sum_const_zero, Nat.cast_zero, le_refl]

private lemma umklappBlockVOp_ket (h : ℕ) (hh : 0 < h) (gU : ℝ)
    (S : A05.Occupation SpinBranch h) :
    umklappBlockVOp h hh gU (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S) =
      if S = A05.groundConfiguration h (fun _ => 0) then
        (-((gU : ℂ) / ((2 * (h : ℂ)) ^ 2))) • umklappZeroChargeWitness h hh
      else if S = umklappTargetConfig h hh then
        (-((gU : ℂ) / ((2 * (h : ℂ)) ^ 2))) • A05.groundKet h (fun _ => 0)
      else 0 := by
  let S₀ : A05.Occupation SpinBranch h := A05.groundConfiguration h (fun _ => 0)
  let St := umklappTargetConfig h hh
  have hne : St ≠ S₀ := umklappTargetConfig_ne_ground0 h hh
  have hproj_exp (v : A05.FockSpace SpinBranch h) :
      umklappBlockProj h hh v =
        inner ℂ (A05.groundKet h (fun _ => 0)) v • A05.groundKet h (fun _ => 0) +
        inner ℂ (umklappZeroChargeWitness h hh) v • umklappZeroChargeWitness h hh := by
    apply (@A02.coordinates (A05.Mode SpinBranch h) _ instDecidableEqProd).injective
    funext T
    have hcoord (w : A05.FockSpace SpinBranch h) :
        @A02.coordinates (A05.Mode SpinBranch h) _ instDecidableEqProd w T =
          inner ℂ (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd T) w := by
      rw [@A02.fock_inner (A05.Mode SpinBranch h) _ instDecidableEqProd]
      simp [A02.ket_apply, A02.coordinates]
    rw [hcoord, ← LinearMap.adjoint_inner_left]
    have hadj : LinearMap.adjoint (umklappBlockProj h hh) = umklappBlockProj h hh :=
      @A03.projection_adjoint (A05.Mode SpinBranch h) _ instDecidableEqProd _
    rw [hadj, umklappBlockProj, @A03.projection_ket (A05.Mode SpinBranch h) _ instDecidableEqProd]
    rw [map_add, map_smul, map_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hcoord,
      A05.groundKet, umklappZeroChargeWitness, ← ket_prod_eq_local,
      @A02.ket_inner (A05.Mode SpinBranch h) _ instDecidableEqProd]
    by_cases hT0 : T = S₀
    · subst hT0
      simp [hne.symm, S₀, St]
    · by_cases hTt : T = St
      · subst hTt
        simp [hT0, S₀, St]
      · simp [hT0, hTt, S₀, St]
  have hVmat := umklappBlockVMatrix_explicit h hh gU
  have h00 : inner ℂ (A05.groundKet h (fun _ => 0))
      (periodicUmklappOp h gU (A05.groundKet h (fun _ => 0))) = 0 := by
    have := congrFun (congrFun hVmat 0) 0; simpa [umklappBlockVMatrix, umklappBlockBasis] using this
  have h01 : inner ℂ (A05.groundKet h (fun _ => 0))
      (periodicUmklappOp h gU (umklappZeroChargeWitness h hh)) =
      -((gU : ℂ) / ((2 * (h : ℂ)) ^ 2)) := by
    have := congrFun (congrFun hVmat 0) 1; simpa [umklappBlockVMatrix, umklappBlockBasis] using this
  have h10 : inner ℂ (umklappZeroChargeWitness h hh)
      (periodicUmklappOp h gU (A05.groundKet h (fun _ => 0))) =
      -((gU : ℂ) / ((2 * (h : ℂ)) ^ 2)) := by
    have := congrFun (congrFun hVmat 1) 0; simpa [umklappBlockVMatrix, umklappBlockBasis] using this
  have h11 : inner ℂ (umklappZeroChargeWitness h hh)
      (periodicUmklappOp h gU (umklappZeroChargeWitness h hh)) = 0 := by
    have := congrFun (congrFun hVmat 1) 1; simpa [umklappBlockVMatrix, umklappBlockBasis] using this
  change umklappBlockProj h hh (periodicUmklappOp h gU (umklappBlockProj h hh
      (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S))) = _
  rw [umklappBlockProj, @A03.projection_ket (A05.Mode SpinBranch h) _ instDecidableEqProd]
  by_cases hS0 : S = S₀
  · subst hS0
    simp only [Set.mem_insert_iff, true_or, ↓reduceIte, S₀]
    rw [ket_prod_eq_local, ← A05.groundKet, ← umklappBlockProj, hproj_exp, h00, h10]
    simp
  · by_cases hSt : S = St
    · subst hSt
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true, ↓reduceIte, hS0, S₀, St]
      rw [← umklappZeroChargeWitness, ← umklappBlockProj, hproj_exp, h01, h11]
      simp
    · simp [hS0, hSt, S₀, St]

/-- Full operator-level `Ch21 → A10` bridge (`A10.sw_compressed_bch_second_order`) on
`A05.Operators SpinBranch h`: with `P = Ch14.projection h 0 0` (projector onto `jointBudget h 0 0`),
`Q = 1 - P`, `H₀ = spinfulFreeHamiltonian h`, `V = umklappBlockVOp h hh gU`, and
`S₁ = umklappBlockS1Op h hh gU`, all `A10` BCH compression hypotheses hold on `FockSpace`,
`P * bchSecondOrderPolynomial h H₀ V S₁ t * P = swEffectiveSecondOrder h P H₀ V S₁ t`, and
the effective second-order action on `|Ω₀⟩` is `(-(t² g_U²) / (32 h⁵)) • |Ω₀⟩`. -/
theorem umklappBlock_a10_bch_bridge (h : ℕ) (hh : 0 < h) (gU t : ℝ) :
    let P := Ch14.projection h (fun _ : SpinBranch => (0 : ℤ)) 0
    let Q := (1 : A05.Operators SpinBranch h) - P
    let H0 := spinfulFreeHamiltonian h
    let V := umklappBlockVOp h hh gU
    let S1 := umklappBlockS1Op h hh gU
    A02.commutator P H0 = 0 ∧
    LinearMap.adjoint S1 = -S1 ∧
    A02.commutator S1 H0 = -A10.offDiagPart h P Q V ∧
    P * A10.bchSecondOrderPolynomial h H0 V S1 t * P =
      A10.swEffectiveSecondOrder h P H0 V S1 t ∧
    A10.swEffectiveSecondOrder h P H0 V S1 t (A05.groundKet h (fun _ => 0)) =
      (-((t : ℂ) ^ 2 * (gU : ℂ) ^ 2) / (32 * (h : ℂ) ^ 5)) • A05.groundKet h (fun _ => 0) := by
  dsimp only
  let S₀ : A05.Occupation SpinBranch h := A05.groundConfiguration h (fun _ => 0)
  let St : A05.Occupation SpinBranch h := umklappTargetConfig h hh
  have hne : St ≠ S₀ := umklappTargetConfig_ne_ground0 h hh
  let P := Ch14.projection h (fun _ : SpinBranch => (0 : ℤ)) 0
  let Q := (1 : A05.Operators SpinBranch h) - P
  let H0 := spinfulFreeHamiltonian h
  let V := umklappBlockVOp h hh gU
  let S1 := umklappBlockS1Op h hh gU
  let c : ℂ := -((gU : ℂ) / ((2 * (h : ℂ)) ^ 2))
  let s : ℂ := c / (2 * (h : ℂ))
  let v₀ : A05.FockSpace SpinBranch h := A05.groundKet h (fun _ => 0)
  let vt : A05.FockSpace SpinBranch h := umklappZeroChargeWitness h hh
  have hv₀_eq : v₀ = @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S₀ :=
    (ket_prod_eq_local h S₀).symm
  have hvt_eq : vt = @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd St := rfl
  have hPeq : P = @A03.coordinateProjection (A05.Mode SpinBranch h) _ instDecidableEqProd {S₀} := by
    dsimp only [P]
    rw [ch14_proj_eq_prod_local, budgetSet_zero_eq_singleton h hh]
  have hPket (S : A05.Occupation SpinBranch h) :
      P (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S) =
        if S = S₀ then @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S else 0 := by
    rw [hPeq, @A03.projection_ket (A05.Mode SpinBranch h) _ instDecidableEqProd,
      Set.mem_singleton_iff]
    by_cases hS : S = S₀ <;> simp [hS]
  have hQket (S : A05.Occupation SpinBranch h) :
      Q (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S) =
        if S = S₀ then 0 else @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S := by
    simp only [Q, LinearMap.sub_apply, Module.End.one_apply, hPket]
    split_ifs <;> simp
  have hP0 : P v₀ = v₀ := by rw [hv₀_eq, hPket]; simp
  have hPt : P vt = 0 := by rw [hvt_eq, hPket]; simp [hne]
  have hQ0 : Q v₀ = 0 := by rw [hv₀_eq, hQket]; simp
  have hQt : Q vt = vt := by rw [hvt_eq, hQket]; simp [hne]
  have hP_id : P * P = P := by
    rw [hPeq]; exact @A03.projection_idempotent (A05.Mode SpinBranch h) _ instDecidableEqProd _
  have hPart : P + Q = 1 := by simp [Q]
  have hPQ : P * Q = 0 := by
    dsimp only [Q]; rw [mul_sub, mul_one, hP_id, sub_self]
  have hQP : Q * P = 0 := by
    dsimp only [Q]; rw [sub_mul, one_mul, hP_id, sub_self]
  have hQ_id : Q * Q = Q := by
    dsimp only [Q]; rw [sub_mul, one_mul, mul_sub, mul_one, hP_id, sub_self, sub_zero]
  have hBaseline : A02.commutator P H0 = 0 := by
    apply @A02.end_ext_basis (A05.Mode SpinBranch h) _ instDecidableEqProd
    intro S
    simp only [A02.commutator, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply,
      H0, spinfulFreeHamiltonian, @A03.diagonal_ket (A05.Mode SpinBranch h) _ instDecidableEqProd,
      map_smul, hPket]
    split_ifs <;> simp [@A03.diagonal_ket (A05.Mode SpinBranch h) _ instDecidableEqProd]
  have hVket (S : A05.Occupation SpinBranch h) :
      V (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S) =
        if S = S₀ then c • vt else if S = St then c • v₀ else 0 :=
    umklappBlockVOp_ket h hh gU S
  have hS1ket (S : A05.Occupation SpinBranch h) :
      S1 (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S) =
        if S = S₀ then s • vt else if S = St then (-s) • v₀ else 0 :=
    @A02.extend_basis_ket (A05.Mode SpinBranch h) _ instDecidableEqProd _ S
  have hV0 : V v₀ = c • vt := by rw [hv₀_eq, hVket]; simp
  have hVt : V vt = c • v₀ := by rw [hvt_eq, hVket]; simp [hne]
  have hS1_0 : S1 v₀ = s • vt := by rw [hv₀_eq, hS1ket]; simp
  have hS1_t : S1 vt = (-s) • v₀ := by rw [hvt_eq, hS1ket]; simp [hne]
  have hH0_0 : H0 v₀ = 0 := spinfulFreeHamiltonian_ground_zero h hh
  have hH0_t : H0 vt = (2 * (h : ℂ)) • vt := spinfulFreeHamiltonian_umklappWitness h hh
  have hS1adj : LinearMap.adjoint S1 = -S1 := by
    apply (@A02.adjoint_of_basis_pairing (A05.Mode SpinBranch h) _ instDecidableEqProd _ _ ?_).symm
    intro S T
    have hs_star : star s = s := by
      dsimp only [s, c]
      simp only [map_div₀, map_neg, map_pow, map_mul, map_ofNat, Complex.conj_ofReal,
        Complex.conj_natCast, Complex.star_def]
    simp only [LinearMap.neg_apply, inner_neg_left, hS1ket]
    by_cases hS0 : S = S₀
    · subst hS0
      simp only [↓reduceIte, inner_smul_left, starRingEnd_apply, hs_star]
      by_cases hT0 : T = S₀
      · subst hT0
        simp only [↓reduceIte, inner_smul_right, hvt_eq,
          @A02.ket_inner (A05.Mode SpinBranch h) _ instDecidableEqProd, hne, hne.symm, mul_zero,
          neg_zero]
      · by_cases hTt : T = St
        · subst hTt
          simp only [hT0, ↓reduceIte, inner_smul_right, hv₀_eq, hvt_eq,
            @A02.ket_inner (A05.Mode SpinBranch h) _ instDecidableEqProd, mul_one]
        · simp only [hT0, hTt, ↓reduceIte, inner_zero_right, hvt_eq,
            @A02.ket_inner (A05.Mode SpinBranch h) _ instDecidableEqProd, Ne.symm hTt, mul_zero,
            neg_zero]
    · by_cases hSt : S = St
      · subst hSt
        simp only [hS0, ↓reduceIte, inner_smul_left, starRingEnd_apply, star_neg, hs_star]
        by_cases hT0 : T = S₀
        · subst hT0
          simp only [↓reduceIte, inner_smul_right, hv₀_eq, hvt_eq,
            @A02.ket_inner (A05.Mode SpinBranch h) _ instDecidableEqProd, mul_one, neg_neg]
        · by_cases hTt : T = St
          · subst hTt
            simp only [hT0, ↓reduceIte, inner_smul_right, hv₀_eq,
              @A02.ket_inner (A05.Mode SpinBranch h) _ instDecidableEqProd, hne.symm,
              mul_zero, neg_zero]
          · simp only [hT0, hTt, ↓reduceIte, inner_zero_right, hv₀_eq,
              @A02.ket_inner (A05.Mode SpinBranch h) _ instDecidableEqProd, Ne.symm hT0, mul_zero,
              neg_zero]
      · simp only [hS0, hSt, ↓reduceIte, inner_zero_left, neg_zero]
        by_cases hT0 : T = S₀
        · subst hT0
          simp only [↓reduceIte, inner_smul_right, hvt_eq,
            @A02.ket_inner (A05.Mode SpinBranch h) _ instDecidableEqProd, hSt, mul_zero]
        · by_cases hTt : T = St
          · subst hTt
            simp only [hT0, ↓reduceIte, inner_smul_right, hv₀_eq,
              @A02.ket_inner (A05.Mode SpinBranch h) _ instDecidableEqProd, hS0, mul_zero]
          · simp [hT0, hTt]
  have hSpp : P * S1 * P = 0 := by
    apply @A02.end_ext_basis (A05.Mode SpinBranch h) _ instDecidableEqProd
    intro S
    simp only [Module.End.mul_apply, LinearMap.zero_apply, hPket]
    by_cases hS0 : S = S₀
    · subst hS0
      simp only [↓reduceIte, ← hv₀_eq, hS1_0, map_smul, hPt, smul_zero]
    · simp [hS0]
  have hSqq : Q * S1 * Q = 0 := by
    apply @A02.end_ext_basis (A05.Mode SpinBranch h) _ instDecidableEqProd
    intro S
    simp only [Module.End.mul_apply, LinearMap.zero_apply, hQket]
    by_cases hS0 : S = S₀
    · simp [hS0]
    · by_cases hSt : S = St
      · subst hSt
        simp only [hS0, ↓reduceIte, ← hvt_eq, hS1_t, map_smul, hQ0, smul_zero]
      · simp [hS0, hSt, hS1ket]
  have hOff : A10.offDiagPart h P Q V = V := by
    apply @A02.end_ext_basis (A05.Mode SpinBranch h) _ instDecidableEqProd
    intro S
    simp only [A10.offDiagPart, LinearMap.add_apply, Module.End.mul_apply, hPket, hQket]
    by_cases hS0 : S = S₀
    · subst hS0
      simp only [↓reduceIte, map_zero, zero_add, ← hv₀_eq, hV0, map_smul, hQt]
    · by_cases hSt : S = St
      · subst hSt
        simp only [hS0, ↓reduceIte, map_zero, add_zero, ← hvt_eq, hVt, map_smul, hP0]
      · simp [hS0, hSt, hVket]
  have hGen : A02.commutator S1 H0 = -A10.offDiagPart h P Q V := by
    rw [hOff]
    apply @A02.end_ext_basis (A05.Mode SpinBranch h) _ instDecidableEqProd
    intro S
    simp only [A02.commutator, LinearMap.sub_apply, LinearMap.neg_apply, Module.End.mul_apply]
    have hhC : (h : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hh)
    by_cases hS0 : S = S₀
    · subst hS0
      rw [← hv₀_eq, hH0_0, map_zero, zero_sub, hS1_0, map_smul, hH0_t, smul_smul, hV0, ← neg_smul,
        ← neg_smul]
      congr 1
      dsimp only [s]
      field_simp [hhC]
    · by_cases hSt : S = St
      · subst hSt
        rw [← hvt_eq, hH0_t, map_smul, hS1_t, map_smul, hH0_0, smul_zero, sub_zero, smul_smul,
          hVt, ← neg_smul]
        congr 1
        dsimp only [s]
        field_simp [hhC]
      · have hHS : H0 (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S) =
            ((∑ ν : SpinBranch, Ch07.relativeEnergy h (Ch07.speciesConfiguration h S ν) : ℤ) : ℂ) •
              @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S :=
          @A03.diagonal_ket (A05.Mode SpinBranch h) _ instDecidableEqProd _ S
        rw [hHS, map_smul, hS1ket, hVket]
        simp [hS0, hSt]
  have hbch := A10.sw_compressed_bch_second_order h P Q H0 V S1 t
    hP_id hQ_id hPart hPQ hQP hBaseline hSpp hSqq hGen
  have heff : A10.swEffectiveSecondOrder h P H0 V S1 t v₀ =
      (-((t : ℂ) ^ 2 * (gU : ℂ) ^ 2) / (32 * (h : ℂ) ^ 5)) • v₀ := by
    have hhC : (h : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hh)
    unfold A10.swEffectiveSecondOrder A10.swSecondOrderCorrection
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply, A02.commutator,
      LinearMap.sub_apply]
    rw [hP0, hH0_0, map_zero, zero_add, hV0, map_smul, hPt, smul_zero, smul_zero, zero_add,
      hS1_0, map_smul, map_smul, hS1_t, hVt, map_sub, map_smul, map_smul, map_smul, map_smul,
      hP0, smul_smul, smul_smul, smul_smul, ← sub_smul, smul_smul]
    congr 1
    dsimp only [s, c]
    field_simp [hhC]
    ring
  exact ⟨hBaseline, hS1adj, hGen, hbch, heff⟩

/-- Concrete `h = 2` specialization of the operator-level `A10.sw_compressed_bch_second_order`
bridge on `A05.Operators SpinBranch 2`: effective second-order energy shift `-(t² g_U²) / 1024`. -/
theorem umklappBlock_a10_bch_bridge_h2 (gU t : ℝ) :
    let P := Ch14.projection 2 (fun _ : SpinBranch => (0 : ℤ)) 0
    let H0 := spinfulFreeHamiltonian 2
    let V := umklappBlockVOp 2 (by decide) gU
    let S1 := umklappBlockS1Op 2 (by decide) gU
    P * A10.bchSecondOrderPolynomial 2 H0 V S1 t * P =
      A10.swEffectiveSecondOrder 2 P H0 V S1 t ∧
    A10.swEffectiveSecondOrder 2 P H0 V S1 t (A05.groundKet 2 (fun _ => 0)) =
      (-((t : ℂ) ^ 2 * (gU : ℂ) ^ 2) / 1024) • A05.groundKet 2 (fun _ => 0) := by
  have h := umklappBlock_a10_bch_bridge 2 (by decide) gU t
  refine ⟨h.2.2.2.1, ?_⟩
  rw [h.2.2.2.2]
  congr 1
  norm_num

end Bosonize.Ch21
