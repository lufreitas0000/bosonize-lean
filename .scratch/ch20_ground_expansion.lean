import Bosonize.Core.Ch14Mandelstam
import Bosonize.Core.Ch16FieldHamiltonian
import Bosonize.Core.Ch17LuttingerModels
import Bosonize.Core.Ch18Bogoliubov
import BosonizeStubs.Ch20CDW
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

lemma cdw_config_forwardX (h : ℕ) (branches : A06.Branches σ) (Ns : σ → ℤ)
    (k p : Ch01.Band (2*h))
    (heq : insert (branches.rightSpecies,p)
        ((A05.groundConfiguration h Ns).erase (branches.leftSpecies,k)) =
          A05.groundConfiguration h (cdwTarget branches Ns))
    (hk : (branches.leftSpecies,k) ∈ A05.groundConfiguration h Ns)
    (hp : (branches.rightSpecies,p) ∉
        (A05.groundConfiguration h Ns).erase (branches.leftSpecies,k)) :
    k.val = Ns branches.leftSpecies ∧ p.val = Ns branches.rightSpecies + 1 := by
  have hleft_not : (branches.leftSpecies,k) ∉
      A05.groundConfiguration h (cdwTarget branches Ns) := by
    rw [← heq]
    simp only [Finset.mem_insert, Prod.mk.injEq]
    have hne : branches.leftSpecies ≠ branches.rightSpecies := branches.distinct.symm
    simp [hne, Finset.mem_erase, hk]
  have hleft := (ground_memX h (cdwTarget branches Ns) branches.leftSpecies k).not.mp hleft_not
  rw [cdwTarget_apply] at hleft
  simp [cdwShift] at hleft
  have hkval := (ground_memX h Ns branches.leftSpecies k).mp hk
  have hpleft : (branches.rightSpecies,p) ∈
      A05.groundConfiguration h (cdwTarget branches Ns) := by
    rw [← heq]
    simp
  have hpval := (ground_memX h (cdwTarget branches Ns) branches.rightSpecies p).mp hpleft
  rw [cdwTarget_apply] at hpval
  simp [cdwShift] at hpval
  have hnotSrc : (branches.rightSpecies,p) ∉ A05.groundConfiguration h Ns := by
    intro hpSrc
    apply hp
    simp [Finset.mem_erase, hpSrc, branches.distinct]
  have hpgt : Ns branches.rightSpecies < p.val := by
    have hnr := (ground_memX h Ns branches.rightSpecies p).not.mp hnotSrc
    omega
  omega

lemma cdw_config_reverseX (h : ℕ) (branches : A06.Branches σ) (Ns : σ → ℤ)
    (k p : Ch01.Band (2*h))
    (hkval : k.val = Ns branches.leftSpecies) (hpval : p.val = Ns branches.rightSpecies + 1) :
    insert (branches.rightSpecies,p)
        ((A05.groundConfiguration h Ns).erase (branches.leftSpecies,k)) =
          A05.groundConfiguration h (cdwTarget branches Ns) := by
  ext z
  obtain ⟨η,l⟩ := z
  have hne : branches.leftSpecies ≠ branches.rightSpecies := branches.distinct.symm
  have htL : cdwTarget branches Ns branches.leftSpecies = Ns branches.leftSpecies - 1 := by
    rw [cdwTarget_apply]; simp [cdwShift, hne]; ring
  have htR : cdwTarget branches Ns branches.rightSpecies = Ns branches.rightSpecies + 1 := by
    rw [cdwTarget_apply]; simp [cdwShift, branches.distinct]
  have hmemS : (η,l) ∈ A05.groundConfiguration h Ns ↔ l.val ≤ Ns η := ground_memX h Ns η l
  have hmemT : (η,l) ∈ A05.groundConfiguration h (cdwTarget branches Ns) ↔
      l.val ≤ cdwTarget branches Ns η := ground_memX h _ η l
  rw [Finset.mem_insert, Finset.mem_erase, hmemS, hmemT]
  by_cases hηL : η = branches.leftSpecies
  · subst η
    rw [htL]
    have hneq : l ≠ k ↔ l.val ≠ Ns branches.leftSpecies := by
      simp [Subtype.ext_iff, hkval]
    simp only [Prod.mk.injEq]
    simp [hneq, hne]
    omega
  · by_cases hηR : η = branches.rightSpecies
    · subst η
      rw [htR]
      have hpEq : l = p ↔ l.val = Ns branches.rightSpecies + 1 := by
        simp [Subtype.ext_iff, hpval]
      simp only [Prod.mk.injEq]
      simp [hpEq, branches.distinct]
      omega
    · have htarget : cdwTarget branches Ns η = Ns η := by
        rw [cdwTarget_apply]; simp [cdwShift, hηL, hηR]
      rw [htarget]
      simp [hηL, hηR]

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

lemma liftedAdjointX (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (ν : σ) (x : ℤ) :
    LinearMap.adjoint (A05.liftedAnnihilation h b ν x) =
      (A01.normalization (2*h) : ℂ) •
        ∑ k : Ch01.Band (2*h),
          star (Ch06Ext.twistedCharacter (2*h) (b ν) k x) •
            A05.creation h ν k := by
  simp only [A05.liftedAnnihilation, map_smulₛₗ, map_sum,
    A05.annihilation]
  simp_rw [← Ch04.creation_eq_adjoint]
  simp [A01.normalization, A05.creation]

lemma hole_pair_innerX {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (S T : A02.Occupation ι) (a b : ℂ) :
    inner ℂ (if i ∈ T then a • A02.ket (T.erase i) else 0)
      (if j ∈ S then b • A02.ket (S.erase j) else 0) =
    if i ∈ T ∧ j ∈ S ∧ T.erase i = S.erase j then
      star a * b else 0 := by
  by_cases hi : i ∈ T
  · by_cases hj : j ∈ S
    · by_cases he : T.erase i = S.erase j
      · simp [hi, hj, he, inner_smul_left, inner_smul_right,
          A02.ket_norm]
        ring
      · simp [hi, hj, he, inner_smul_left, inner_smul_right,
          A02.ket_inner]
    · simp [hi, hj]
  · simp [hi]

lemma inner_sum_leftX {ι E : Type*} [Fintype ι]
    [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] (f : ι → E) (y : E) :
    inner ℂ (∑ i, f i) y = ∑ i, inner ℂ (f i) y := by
  rw [← inner_conj_symm]
  rw [inner_sum]
  change star (∑ i, inner ℂ y (f i)) = ∑ i, inner ℂ (f i) y
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact inner_conj_symm (f i) y

lemma scalar_top_pair (h : ℕ) (hh : 0 < h) (Ns T : σ → ℤ)
    (l r : σ) (x : ℤ) (hT : T r = Ns r + 1) :
    star ((A01.normalization (2*h) : ℂ) * Ch13.kleinPhase h T r *
      A01.integerCharacter (A01.canonicalRoot (2*h)) (T r) x) *
      ((A01.normalization (2*h) : ℂ) * Ch13.kleinPhase h Ns l *
      A01.integerCharacter (A01.canonicalRoot (2*h)) (Ns l) x) =
      (((2*h : ℕ) : ℂ)⁻¹) *
        (A01.integerCharacter (A01.canonicalRoot (2*h)) (Ns l - Ns r - 1) x *
          (Ch13.kleinPhase h Ns l * Ch13.kleinPhase h T r)) := by
  letI : NeZero (2*h) := ⟨by omega⟩
  have hnorm := A01.normalization_square_complex (2*h)
  have hroot := A01.canonical_root_primitive (2*h)
  simp only [star_mul, A01.normalization_conj]
  rw [show star (Ch13.kleinPhase h T r) = Ch13.kleinPhase h T r by simp [Ch13.kleinPhase]]
  rw [A01.complex_character_conj (2*h) (A01.canonicalRoot (2*h)) hroot (T r) x]
  simp_rw [hT]
  simp only [A01.integerCharacter]
  let z := A01.canonicalRoot (2*h)
  have hpow : z ^ (-(Ns r + 1) * x) * z ^ (Ns l * x) =
      z ^ ((Ns l - Ns r - 1) * x) := by
    rw [← zpow_add₀ (A01.root_ne_zero (2*h) z hroot)]
    congr 1
    ring
  have hprod :
      z ^ (-(Ns r + 1) * x) * (Ch13.kleinPhase h T r * (A01.normalization (2*h) : ℂ)) *
        ((A01.normalization (2*h) : ℂ) * Ch13.kleinPhase h Ns l * z ^ (Ns l * x)) =
      (A01.normalization (2*h) : ℂ)^2 *
        (Ch13.kleinPhase h Ns l * Ch13.kleinPhase h T r) *
        (z ^ (-(Ns r + 1) * x) * z ^ (Ns l * x)) := by ring
  rw [hprod, hpow]
  have hn : (A01.normalization (2*h) : ℂ)^2 = ((2*h : ℕ) : ℂ)⁻¹ :=
    eq_inv_of_mul_eq_one_right hnorm
  rw [hn]
  ring

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

lemma one_sub_projection_ketX {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Set (A02.Occupation ι)) (c : ℂ) (S : A02.Occupation ι) :
    (1 - A03.coordinateProjection U) (c • A02.ket S) =
      if S ∈ U then 0 else c • A02.ket S := by
  rw [LinearMap.sub_apply, Module.End.one_apply, map_smul,
    A03.projection_ket]
  by_cases hS : S ∈ U <;> simp [hS]

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

lemma orderSC_inner_expandX (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (br : A06.Branches σ) (x : ℤ) (S T : A05.Occupation σ h) :
    inner ℂ (A02.ket T) (orderSC h b br x (A02.ket S)) =
      ((A01.normalization (2*h) : ℂ)^2) *
        ∑ k : Ch01.Band (2*h), ∑ p : Ch01.Band (2*h),
          if (br.leftSpecies,k) ∈ S ∧
             (br.rightSpecies,p) ∈ S.erase (br.leftSpecies,k) ∧
             (S.erase (br.leftSpecies,k)).erase (br.rightSpecies,p) = T then
            (Ch06Ext.twistedCharacter (2*h) (b br.rightSpecies) p x *
               Ch04.fermionSign (br.rightSpecies,p) (S.erase (br.leftSpecies,k))) *
             (Ch06Ext.twistedCharacter (2*h) (b br.leftSpecies) k x *
               Ch04.fermionSign (br.leftSpecies,k) S)
          else 0 := by
  rw [orderSC_expandX]
  rw [inner_smul_right]
  simp_rw [inner_fsumX, inner_smul_right, A02.ket_inner]
  simp [mul_assoc, mul_comm, mul_left_comm]

end Bosonize.Ch20
