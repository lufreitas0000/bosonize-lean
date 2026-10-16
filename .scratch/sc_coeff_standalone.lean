import Bosonize.Core.Ch13KleinFactors
import Bosonize.Core.Ch14Mandelstam
import Bosonize.Core.Ch16FieldHamiltonian
import Bosonize.Core.Ch17LuttingerModels
import Bosonize.Core.Ch18Bogoliubov
import Mathlib.Analysis.Real.Pi.Bounds

set_option linter.style.haveILetI false

namespace Bosonize.Ch20
open scoped BigOperators Classical
variable {σ : Type*} [Fintype σ] [LinearOrder σ]

noncomputable local instance localModeLinearOrder (h : ℕ) :
    LinearOrder (A05.Mode σ h) := A05.speciesOrder h
noncomputable local instance localModeLT (h : ℕ) :
    LT (A05.Mode σ h) := (A05.speciesOrder h).toLT
noncomputable local instance localModeLE (h : ℕ) :
    LE (A05.Mode σ h) := (A05.speciesOrder h).toLE
noncomputable local instance localModeDecidableEq (h : ℕ) :
    DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq

noncomputable def scTarget (branches : A06.Branches σ) (Ns : σ → ℤ) : σ → ℤ :=
  Ch13.lowerCharge (Ch13.lowerCharge Ns branches.leftSpecies) branches.rightSpecies
noncomputable def scShift (branches : A06.Branches σ) (ν : σ) : ℤ :=
  -(if ν = branches.rightSpecies then (1 : ℤ) else 0) -
    (if ν = branches.leftSpecies then (1 : ℤ) else 0)

omit [Fintype σ] in
lemma scTarget_apply (branches : A06.Branches σ) (Ns : σ → ℤ) (ν : σ) :
    scTarget branches Ns ν = Ns ν + scShift branches ν := by
  unfold scTarget scShift Ch13.lowerCharge
  by_cases hR : ν = branches.rightSpecies <;>
    by_cases hL : ν = branches.leftSpecies
  · exact False.elim (branches.distinct (hR.symm.trans hL))
  · have hRL : branches.rightSpecies ≠ branches.leftSpecies := by
      intro he
      exact hL (hR.trans he)
    subst ν
    simp [Function.update, hRL]
    ring
  · have hLR : branches.leftSpecies ≠ branches.rightSpecies := branches.distinct.symm
    subst ν
    simp [Function.update, hLR]
    ring
  · simp [Function.update, hR, hL]
noncomputable def fieldOf (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (ν : σ) (x : ℤ) : A05.Operators σ h := A05.liftedAnnihilation h b ν x
noncomputable def orderSC (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (branches : A06.Branches σ) (x : ℤ) : A05.Operators σ h :=
  fieldOf h b branches.rightSpecies x * fieldOf h b branches.leftSpecies x
noncomputable def scChargeCoeff (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (x : ℤ) : ℂ :=
  A01.integerCharacter (A01.canonicalRoot (2*h))
      (Ns branches.rightSpecies + Ns branches.leftSpecies) x *
    (Ch13.kleinPhase h Ns branches.leftSpecies *
      Ch13.kleinPhase h (Ch13.lowerCharge Ns branches.leftSpecies)
        branches.rightSpecies)

lemma ground_memX (h : ℕ) (Ns : σ → ℤ) (ν : σ)
    (k : Ch01.Band (2*h)) :
    (ν,k) ∈ A05.groundConfiguration h Ns ↔ k.val ≤ Ns ν := by
  simp only [A05.groundConfiguration, A05.jointConfiguration,
    Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Ch07.groundConfiguration, Finset.mem_filter]
  aesop

lemma sc_pair_forwardX (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (k p : Ch01.Band (2*h))
    (heq : ((A05.groundConfiguration h Ns).erase
        (branches.leftSpecies,k)).erase (branches.rightSpecies,p) =
      A05.groundConfiguration h (scTarget branches Ns))
    (hk : (branches.leftSpecies,k) ∈ A05.groundConfiguration h Ns)
    (hp : (branches.rightSpecies,p) ∈ A05.groundConfiguration h Ns) :
    k.val = Ns branches.leftSpecies ∧ p.val = Ns branches.rightSpecies := by
  have hLnot : (branches.leftSpecies,k) ∉
      A05.groundConfiguration h (scTarget branches Ns) := by
    rw [← heq]
    simp
  have hRnot : (branches.rightSpecies,p) ∉
      A05.groundConfiguration h (scTarget branches Ns) := by
    rw [← heq]
    simp
  have hLlo := (ground_memX h Ns branches.leftSpecies k).mp hk
  have hLhi := (ground_memX h (scTarget branches Ns)
      branches.leftSpecies k).not.mp hLnot
  have hRlo := (ground_memX h Ns branches.rightSpecies p).mp hp
  have hRhi := (ground_memX h (scTarget branches Ns)
      branches.rightSpecies p).not.mp hRnot
  rw [scTarget_apply] at hLhi hRhi
  have hne : branches.leftSpecies ≠ branches.rightSpecies :=
    branches.distinct.symm
  simp [scShift, hne, branches.distinct] at hLhi hRhi
  omega

lemma sc_pair_reverseX (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (k p : Ch01.Band (2*h))
    (hkval : k.val = Ns branches.leftSpecies)
    (hpval : p.val = Ns branches.rightSpecies) :
    ((A05.groundConfiguration h Ns).erase
        (branches.leftSpecies,k)).erase (branches.rightSpecies,p) =
      A05.groundConfiguration h (scTarget branches Ns) := by
  ext z
  obtain ⟨η,l⟩ := z
  have hne : branches.leftSpecies ≠ branches.rightSpecies :=
    branches.distinct.symm
  rw [Finset.mem_erase, Finset.mem_erase]
  rw [ground_memX h Ns η l, ground_memX h (scTarget branches Ns) η l]
  rw [scTarget_apply]
  by_cases hL : η = branches.leftSpecies
  · subst η
    have hkEq : l = k ↔ l.val = Ns branches.leftSpecies := by
      constructor
      · intro e
        rw [e, hkval]
      · intro e
        apply Subtype.ext
        exact e.trans hkval.symm
    simp [scShift, hne, hkEq]
    omega
  · by_cases hR : η = branches.rightSpecies
    · subst η
      have hpEq : l = p ↔ l.val = Ns branches.rightSpecies := by
        constructor
        · intro e
          rw [e, hpval]
        · intro e
          apply Subtype.ext
          exact e.trans hpval.symm
      simp [scShift, branches.distinct, hpEq]
      omega
    · simp [scShift, hL, hR]

lemma sc_pair_support_iffX (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (k p : Ch01.Band (2*h))
    (hk : (branches.leftSpecies,k) ∈ A05.groundConfiguration h Ns)
    (hp : (branches.rightSpecies,p) ∈ A05.groundConfiguration h Ns) :
    ((A05.groundConfiguration h Ns).erase
        (branches.leftSpecies,k)).erase (branches.rightSpecies,p) =
      A05.groundConfiguration h (scTarget branches Ns) ↔
        k.val = Ns branches.leftSpecies ∧
          p.val = Ns branches.rightSpecies := by
  constructor
  · intro heq
    exact sc_pair_forwardX h branches Ns k p heq hk hp
  · rintro ⟨hkval,hpval⟩
    exact sc_pair_reverseX h branches Ns k p hkval hpval

lemma sc_ground_pair_cond_iffX (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (k p : Ch01.Band (2*h))
    (hk : (branches.leftSpecies,k) ∈ A05.groundConfiguration h Ns)
    (hp : (branches.rightSpecies,p) ∈ A05.groundConfiguration h Ns) :
    ((branches.rightSpecies,p) ∈ A05.groundConfiguration h Ns ∧
      (branches.leftSpecies,k) ∈ A05.groundConfiguration h Ns ∧
      (branches.rightSpecies = branches.leftSpecies → p ≠ k) ∧
      A05.groundConfiguration h (scTarget branches Ns) =
        Finset.erase (Finset.erase (A05.groundConfiguration h Ns)
          (branches.leftSpecies,k)) (branches.rightSpecies,p)) ↔
      k.val = Ns branches.leftSpecies ∧ p.val = Ns branches.rightSpecies := by
  constructor
  · rintro ⟨_,_,_,heq⟩
    exact (sc_pair_support_iffX h branches Ns k p hk hp).mp heq.symm
  · rintro ⟨hkval,hpval⟩
    refine ⟨hp,hk,?_,?_⟩
    · intro heq
      exact (branches.distinct heq).elim
    · have heq := (sc_pair_support_iffX h branches Ns k p hk hp).mpr
        ⟨hkval,hpval⟩
      exact heq.symm


lemma fieldKetX (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (S : A05.Occupation σ h) (ν : σ) (x : ℤ) :
    A05.liftedAnnihilation h b ν x (A02.ket S) =
      (A01.normalization (2*h) : ℂ) •
        ∑ k : Ch01.Band (2*h),
          if (ν,k) ∈ S then
            (Ch06Ext.twistedCharacter (2*h) (b ν) k x *
              Ch04.fermionSign (ν,k) S) • A02.ket (S.erase (ν,k))
          else 0 := by
  simp only [A05.liftedAnnihilation, LinearMap.smul_apply,
    LinearMap.sum_apply, A05.annihilation, Ch04.annihilation_ket]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with hk
  · simp only [smul_smul]
  · simp


lemma scalar_top_pair_sc (h : ℕ) (hh : 0 < h) (Ns T : σ → ℤ)
    (l r : σ) (x : ℤ) (hT : T r = Ns r) :
    ((A01.normalization (2*h) : ℂ) * Ch13.kleinPhase h T r *
      A01.integerCharacter (A01.canonicalRoot (2*h)) (T r) x) *
      ((A01.normalization (2*h) : ℂ) * Ch13.kleinPhase h Ns l *
      A01.integerCharacter (A01.canonicalRoot (2*h)) (Ns l) x) =
      (((2*h : ℕ) : ℂ)⁻¹) *
        (A01.integerCharacter (A01.canonicalRoot (2*h)) (Ns r + Ns l) x *
          (Ch13.kleinPhase h Ns l * Ch13.kleinPhase h T r)) := by
  letI : NeZero (2*h) := ⟨by omega⟩
  have hnorm := A01.normalization_square_complex (2*h)
  have hroot := A01.canonical_root_primitive (2*h)
  simp_rw [hT]
  simp only [A01.integerCharacter]
  let z := A01.canonicalRoot (2*h)
  have hpow : z ^ (Ns r * x) * z ^ (Ns l * x) = z ^ ((Ns r + Ns l) * x) := by
    rw [← zpow_add₀ (A01.root_ne_zero (2*h) z hroot)]
    congr 1
    ring
  have hprod :
      (A01.normalization (2*h) : ℂ) * Ch13.kleinPhase h T r * z ^ (Ns r * x) *
        ((A01.normalization (2*h) : ℂ) * Ch13.kleinPhase h Ns l * z ^ (Ns l * x)) =
      (A01.normalization (2*h) : ℂ)^2 *
        (Ch13.kleinPhase h Ns l * Ch13.kleinPhase h T r) *
        (z ^ (Ns r * x) * z ^ (Ns l * x)) := by ring
  rw [hprod, hpow]
  have hn : (A01.normalization (2*h) : ℂ)^2 = ((2*h : ℕ) : ℂ)⁻¹ :=
    eq_inv_of_mul_eq_one_right hnorm
  rw [hn]
  ring

lemma sc_pair_sign_kleinX (h : ℕ) (hh : 0 < h)
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hR : -(h : ℤ) < Ns branches.rightSpecies)
    (hL : -(h : ℤ) < Ns branches.leftSpecies)
    (k p : Ch01.Band (2*h)) (hk : k.val = Ns branches.leftSpecies)
    (hp : p.val = Ns branches.rightSpecies) :
    Ch04.fermionSign (branches.rightSpecies,p)
      ((A05.groundConfiguration h Ns).erase (branches.leftSpecies,k)) *
      Ch04.fermionSign (branches.leftSpecies,k)
        (A05.groundConfiguration h Ns) =
      Ch13.kleinPhase h Ns branches.leftSpecies *
        Ch13.kleinPhase h (Ch13.lowerCharge Ns branches.leftSpecies)
          branches.rightSpecies := by
  have hNsL := hN branches.leftSpecies
  have hNsR := hN branches.rightSpecies
  have hNsLlow : -(h : ℤ) + 1 ≤ Ns branches.leftSpecies := by omega
  have hNsRlow : -(h : ℤ) + 1 ≤ Ns branches.rightSpecies := by omega
  have hNlower : A05.admissible h (Ch13.lowerCharge Ns branches.leftSpecies) := by
    intro η
    by_cases he : η = branches.leftSpecies
    · subst η
      simp only [Ch13.lowerCharge, Function.update_self]
      constructor
      · have hlo := hL
        omega
      · have hu := hNsL.2
        omega
    · have hη := hN η
      simp only [Ch13.lowerCharge, Function.update_of_ne he]
      exact hη
  have hRlower : -(h : ℤ) + 1 ≤
      Ch13.lowerCharge Ns branches.leftSpecies branches.rightSpecies := by
    rw [Ch13.lowerCharge, Function.update_of_ne branches.distinct]
    exact hNsRlow
  have hleft := Ch13.ground_top_annihilation h hh Ns hN
    branches.leftSpecies hNsLlow k hk
  have hright := Ch13.ground_top_annihilation h hh
    (Ch13.lowerCharge Ns branches.leftSpecies) hNlower
    branches.rightSpecies hRlower p (by
      rw [Ch13.lowerCharge, Function.update_of_ne branches.distinct]
      exact hp)
  have hkmem : (branches.leftSpecies,k) ∈ A05.groundConfiguration h Ns :=
    (ground_memX h Ns branches.leftSpecies k).mpr (le_of_eq hk)
  have hpmem : (branches.rightSpecies,p) ∈ A05.groundConfiguration h Ns :=
    (ground_memX h Ns branches.rightSpecies p).mpr (le_of_eq hp)
  have hpairne : (branches.rightSpecies,p) ≠ (branches.leftSpecies,k) := by
    intro he
    have hs := congrArg Prod.fst he
    exact branches.distinct hs
  have hpErase : (branches.rightSpecies,p) ∈
      (A05.groundConfiguration h Ns).erase (branches.leftSpecies,k) :=
    Finset.mem_erase.mpr ⟨hpairne, hpmem⟩
  have hcfg := sc_pair_reverseX h branches Ns k p hk hp
  have hraw : A05.annihilation h branches.rightSpecies p
      (A05.annihilation h branches.leftSpecies k (A05.groundKet h Ns)) =
      (Ch04.fermionSign (branches.rightSpecies,p)
        ((A05.groundConfiguration h Ns).erase (branches.leftSpecies,k)) *
       Ch04.fermionSign (branches.leftSpecies,k)
        (A05.groundConfiguration h Ns)) •
        A05.groundKet h (Ch13.lowerCharge
          (Ch13.lowerCharge Ns branches.leftSpecies) branches.rightSpecies) := by
    unfold A05.annihilation A05.groundKet
    rw [Ch04.annihilation_ket, ite_eq_left hkmem, map_smul,
      Ch04.annihilation_ket, ite_eq_left hpErase]
    rw [hcfg]
    simp [smul_smul, scTarget, Ch13.lowerCharge, mul_comm]
  have htop : A05.annihilation h branches.rightSpecies p
      (A05.annihilation h branches.leftSpecies k (A05.groundKet h Ns)) =
      (Ch13.kleinPhase h Ns branches.leftSpecies *
        Ch13.kleinPhase h (Ch13.lowerCharge Ns branches.leftSpecies)
          branches.rightSpecies) •
        A05.groundKet h (Ch13.lowerCharge
          (Ch13.lowerCharge Ns branches.leftSpecies) branches.rightSpecies) := by
    rw [hleft, map_smul, hright]
    simp [smul_smul]
  have hs := congrArg (fun v => inner ℂ
      (A05.groundKet h (Ch13.lowerCharge
        (Ch13.lowerCharge Ns branches.leftSpecies) branches.rightSpecies)) v)
      (hraw.symm.trans htop)
  have hnorm : inner ℂ
      (A05.groundKet h (Ch13.lowerCharge
        (Ch13.lowerCharge Ns branches.leftSpecies) branches.rightSpecies))
      (A05.groundKet h (Ch13.lowerCharge
        (Ch13.lowerCharge Ns branches.leftSpecies) branches.rightSpecies)) = 1 := by
    simp [A05.groundKet, A02.ket_norm]
  simp only [inner_smul_right, hnorm, mul_one] at hs
  exact hs


lemma map_if_zeroX {V W : Type*} [AddCommMonoid V] [AddCommMonoid W]
    [Module ℂ V] [Module ℂ W] (f : V →ₗ[ℂ] W) (p : Prop) [Decidable p] (v : V) :
    f (if p then v else 0) = if p then f v else 0 := by
  split_ifs <;> simp

lemma orderSC_expandX (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (br : A06.Branches σ) (x : ℤ) (S : A05.Occupation σ h) :
    orderSC h b br x (A02.ket S) =
      ((A01.normalization (2*h) : ℂ)^2) •
        ∑ k : Ch01.Band (2*h), ∑ p : Ch01.Band (2*h),
          if (br.leftSpecies,k) ∈ S ∧
             (br.rightSpecies,p) ∈ S.erase (br.leftSpecies,k) then
            ((Ch06Ext.twistedCharacter (2*h) (b br.rightSpecies) p x *
               Ch04.fermionSign (br.rightSpecies,p) (S.erase (br.leftSpecies,k))) *
             (Ch06Ext.twistedCharacter (2*h) (b br.leftSpecies) k x *
               Ch04.fermionSign (br.leftSpecies,k) S)) •
              A02.ket ((S.erase (br.leftSpecies,k)).erase (br.rightSpecies,p))
          else 0 := by
  unfold orderSC
  simp only [Module.End.mul_apply, fieldOf]
  rw [fieldKetX h b S br.leftSpecies x]
  simp only [map_smul, map_sum]
  simp_rw [map_if_zeroX, map_smul, fieldKetX]
  simp_rw [smul_smul, Finset.smul_sum]
  congr 1
  funext k
  by_cases hk : (br.leftSpecies,k) ∈ S
  · simp only [ite_eq_left hk]
    rw [Finset.smul_sum]
    congr 1
    funext p
    by_cases hp : (br.rightSpecies,p) ∈ S.erase (br.leftSpecies,k)
    · rw [ite_eq_left hp, ite_eq_left ⟨hk,hp⟩]
      simp only [smul_smul]
      congr 1
      ring
    · rw [ite_eq_right hp, ite_eq_right (by simp [hk,hp])]
      simp
  · simp [hk]


lemma inner_fsumX {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ι : Type*} [Fintype ι]
    (f : ι → E) (x : E) :
    inner ℂ x (∑ i, f i) = ∑ i, inner ℂ x (f i) := by
  rw [← innerₛₗ_apply_apply]
  rw [map_sum]
  simp only [innerₛₗ_apply_apply]

lemma inner_if_zeroX {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] (x v : E) (p : Prop) [Decidable p] :
    inner ℂ x (if p then v else 0) = if p then inner ℂ x v else 0 := by
  split_ifs <;> simp

lemma sum_single_pairX {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [LinearOrder ι] [LinearOrder κ]
    (a : ι) (b : κ) (f : ι → κ → ℂ)
    (g : ι → κ → Prop) [DecidableRel g]
    (ha : ∀ i j, g i j → i = a ∧ j = b)
    (hab : g a b) :
    (∑ i, ∑ j, if g i j then f i j else 0) = f a b := by
  classical
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp [hab]
    · intro j _ hj
      have : ¬ g a j := by
        intro h
        exact hj ((ha a j h).2)
      simp [this]
    · simp
  · intro i _ hi
    have hzero : ∀ j, ¬ g i j := by
      intro j h
      exact hi ((ha i j h).1)
    simp [hzero]
  · simp


lemma orderSC_inner_expandX (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (br : A06.Branches σ) (x : ℤ) (S T : A05.Occupation σ h) :
    inner ℂ (A02.ket T) (orderSC h b br x (A02.ket S)) =
      ((A01.normalization (2*h) : ℂ)^2) *
        ∑ k : Ch01.Band (2*h), ∑ p : Ch01.Band (2*h),
          if (br.rightSpecies,p) ∈ S ∧ (br.leftSpecies,k) ∈ S ∧
             (br.rightSpecies = br.leftSpecies → p ≠ k) ∧
             T = (S.erase (br.leftSpecies,k)).erase (br.rightSpecies,p) then
            Ch04.fermionSign (br.rightSpecies,p) (S.erase (br.leftSpecies,k)) *
              (Ch04.fermionSign (br.leftSpecies,k) S *
                (Ch06Ext.twistedCharacter (2*h) (b br.rightSpecies) p x *
                  Ch06Ext.twistedCharacter (2*h) (b br.leftSpecies) k x))
          else 0 := by
  rw [orderSC_expandX]
  rw [inner_smul_right]
  rw [inner_fsumX]
  simp_rw [inner_fsumX]
  simp_rw [inner_if_zeroX, inner_smul_right, A02.ket_inner]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro p _
  by_cases hR : (br.rightSpecies,p) ∈ S <;>
    by_cases hL : (br.leftSpecies,k) ∈ S <;>
    by_cases hD : br.rightSpecies = br.leftSpecies → p ≠ k <;>
    by_cases hE : T = (S.erase (br.leftSpecies,k)).erase (br.rightSpecies,p) <;>
    simp [hR,hL,hD,hE, Finset.mem_erase,
      mul_assoc, mul_comm, mul_left_comm]

lemma orderSC_ground_coeffX (h : ℕ) (hh : 0 < h)
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hR : -(h : ℤ) < Ns branches.rightSpecies)
    (hL : -(h : ℤ) < Ns branches.leftSpecies) (x : ℤ) :
    inner ℂ (A05.groundKet h (scTarget branches Ns))
      (orderSC h (fun _ => Ch06Ext.periodicTwist (2*h)) branches x
        (A05.groundKet h Ns)) =
      (((2*h : ℕ) : ℂ)⁻¹) * scChargeCoeff h branches Ns x := by
  let k0 : Ch01.Band (2*h) := ⟨Ns branches.leftSpecies, by
    unfold Ch01.inBandPredicate
    obtain ⟨_,hu⟩ := hN branches.leftSpecies
    push_cast
    constructor <;> omega⟩
  let p0 : Ch01.Band (2*h) := ⟨Ns branches.rightSpecies, by
    unfold Ch01.inBandPredicate
    obtain ⟨_,hu⟩ := hN branches.rightSpecies
    push_cast
    constructor <;> omega⟩
  have hk0 : k0.val = Ns branches.leftSpecies := rfl
  have hp0 : p0.val = Ns branches.rightSpecies := rfl
  have hkmem : (branches.leftSpecies,k0) ∈ A05.groundConfiguration h Ns :=
    (ground_memX h Ns branches.leftSpecies k0).mpr (le_of_eq hk0)
  have hpmem : (branches.rightSpecies,p0) ∈ A05.groundConfiguration h Ns :=
    (ground_memX h Ns branches.rightSpecies p0).mpr (le_of_eq hp0)
  let g (k : Ch01.Band (2*h)) (p : Ch01.Band (2*h)) : Prop :=
    (branches.rightSpecies,p) ∈ A05.groundConfiguration h Ns ∧
      (branches.leftSpecies,k) ∈ A05.groundConfiguration h Ns ∧
      (branches.rightSpecies = branches.leftSpecies → p ≠ k) ∧
      A05.groundConfiguration h (scTarget branches Ns) =
        Finset.erase (Finset.erase (A05.groundConfiguration h Ns)
          (branches.leftSpecies,k)) (branches.rightSpecies,p)
  let f (k : Ch01.Band (2*h)) (p : Ch01.Band (2*h)) : ℂ :=
    Ch04.fermionSign (branches.rightSpecies,p)
        ((A05.groundConfiguration h Ns).erase (branches.leftSpecies,k)) *
      (Ch04.fermionSign (branches.leftSpecies,k)
        (A05.groundConfiguration h Ns) *
        (Ch06Ext.twistedCharacter (2*h)
          (Ch06Ext.periodicTwist (2*h)) p x *
         Ch06Ext.twistedCharacter (2*h)
          (Ch06Ext.periodicTwist (2*h)) k x))
  have hsupport : g k0 p0 := by
    apply (sc_ground_pair_cond_iffX h branches Ns k0 p0 hkmem hpmem).2
    exact ⟨hk0,hp0⟩
  have huniq : ∀ k p, g k p → k = k0 ∧ p = p0 := by
    intro k p hg
    have hv := (sc_ground_pair_cond_iffX h branches Ns k p
      hg.2.1 hg.1).mp hg
    constructor
    · apply Subtype.ext
      exact hv.1.trans hk0.symm
    · apply Subtype.ext
      exact hv.2.trans hp0.symm
  rw [A05.groundKet, A05.groundKet, orderSC_inner_expandX]
  change ((A01.normalization (2*h) : ℂ)^2) *
      (∑ k : Ch01.Band (2*h), ∑ p : Ch01.Band (2*h),
        if g k p then f k p else 0) = _
  rw [sum_single_pairX k0 p0 f g huniq hsupport]
  dsimp [f]
  have hsign := sc_pair_sign_kleinX h hh branches Ns hN hR hL k0 p0 hk0 hp0
  have hcharR : Ch06Ext.twistedCharacter (2*h)
      (Ch06Ext.periodicTwist (2*h)) p0 x =
      A01.integerCharacter (A01.canonicalRoot (2*h)) (Ns branches.rightSpecies) x := by
    simp [Ch06Ext.twistedCharacter, Ch06Ext.liftPhase, Ch06Ext.periodicTwist, hp0]
  have hcharL : Ch06Ext.twistedCharacter (2*h)
      (Ch06Ext.periodicTwist (2*h)) k0 x =
      A01.integerCharacter (A01.canonicalRoot (2*h)) (Ns branches.leftSpecies) x := by
    simp [Ch06Ext.twistedCharacter, Ch06Ext.liftPhase, Ch06Ext.periodicTwist, hk0]
  have hT : Ch13.lowerCharge Ns branches.leftSpecies branches.rightSpecies =
      Ns branches.rightSpecies := by
    simp [Ch13.lowerCharge, branches.distinct]
  calc
    _ = ((A01.normalization (2*h) : ℂ)^2) *
        ((Ch04.fermionSign (branches.rightSpecies,p0)
            ((A05.groundConfiguration h Ns).erase (branches.leftSpecies,k0)) *
          Ch04.fermionSign (branches.leftSpecies,k0)
            (A05.groundConfiguration h Ns)) *
         (A01.integerCharacter (A01.canonicalRoot (2*h))
            (Ns branches.rightSpecies) x *
          A01.integerCharacter (A01.canonicalRoot (2*h))
            (Ns branches.leftSpecies) x)) := by
      rw [hcharR, hcharL]
      ring
    _ = ((A01.normalization (2*h) : ℂ)^2) *
        ((Ch13.kleinPhase h Ns branches.leftSpecies *
          Ch13.kleinPhase h (Ch13.lowerCharge Ns branches.leftSpecies)
            branches.rightSpecies) *
         (A01.integerCharacter (A01.canonicalRoot (2*h))
            (Ns branches.rightSpecies) x *
          A01.integerCharacter (A01.canonicalRoot (2*h))
            (Ns branches.leftSpecies) x)) := by
      rw [hsign]
    _ = ((A01.normalization (2*h) : ℂ) *
          Ch13.kleinPhase h (Ch13.lowerCharge Ns branches.leftSpecies)
            branches.rightSpecies *
          A01.integerCharacter (A01.canonicalRoot (2*h))
            (Ns branches.rightSpecies) x) *
        ((A01.normalization (2*h) : ℂ) *
          Ch13.kleinPhase h Ns branches.leftSpecies *
          A01.integerCharacter (A01.canonicalRoot (2*h))
            (Ns branches.leftSpecies) x) := by ring
    _ = (((2*h : ℕ) : ℂ)⁻¹) * scChargeCoeff h branches Ns x := by
      simpa [scChargeCoeff, hT] using
        scalar_top_pair_sc h hh Ns (Ch13.lowerCharge Ns branches.leftSpecies)
          branches.leftSpecies branches.rightSpecies x hT


end Bosonize.Ch20
