import Bosonize.Core.Ch14Mandelstam
import Bosonize.Core.Ch16FieldHamiltonian
import Bosonize.Core.Ch17LuttingerModels
import Bosonize.Core.Ch18Bogoliubov
import BosonizeStubs.Ch20CDW

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Bosonize.Ch20
open scoped BigOperators Classical
variable {σ : Type*} [Fintype σ] [LinearOrder σ]

lemma sum_single_pair {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [AddCommMonoid R]
    (a₀ : α) (b₀ : β) (f : α → β → R) :
    ∑ b : β, ∑ a : α, (if (a = a₀ ∧ b = b₀) then f a b else 0) = f a₀ b₀ := by
  classical
  rw [Finset.sum_eq_single b₀]
  · rw [Finset.sum_eq_single a₀]
    · simp
    · intro a ha hne
      simp [hne]
    · intro hnot
      exact (hnot (Finset.mem_univ a₀)).elim
  · intro b hb hne
    apply Finset.sum_eq_zero
    intro a ha
    simp [hne]
  · intro hnot
    exact (hnot (Finset.mem_univ b₀)).elim

attribute [local instance] A05.localModeLinearOrder A05.localModeLT
  A05.localModeLE A05.localModeDecidableEq

lemma ground_memX (h : ℕ) (Ns : σ → ℤ) (ν : σ) (k : Ch01.Band (2*h)) :
    (ν,k) ∈ A05.groundConfiguration h Ns ↔ k.val ≤ Ns ν := by
  simp only [A05.groundConfiguration, A05.jointConfiguration,
    Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Ch07.groundConfiguration, Finset.mem_filter]
  aesop

lemma cdw_config_forwardX (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (k p : Ch01.Band (2*h))
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
  have hleft := (ground_memX h (cdwTarget branches Ns)
      branches.leftSpecies k).not.mp hleft_not
  rw [cdwTarget_apply] at hleft
  simp [cdwShift] at hleft
  have hkval := (ground_memX h Ns branches.leftSpecies k).mp hk
  have hpleft : (branches.rightSpecies,p) ∈
      A05.groundConfiguration h (cdwTarget branches Ns) := by
    rw [← heq]
    simp
  have hpval := (ground_memX h (cdwTarget branches Ns)
      branches.rightSpecies p).mp hpleft
  rw [cdwTarget_apply] at hpval
  simp [cdwShift] at hpval
  have hnotSrc : (branches.rightSpecies,p) ∉
      A05.groundConfiguration h Ns := by
    intro hpSrc
    apply hp
    simp [Finset.mem_erase, hpSrc, branches.distinct]
  have hpgt : Ns branches.rightSpecies < p.val := by
    have hnr := (ground_memX h Ns branches.rightSpecies p).not.mp hnotSrc
    omega
  omega

lemma cdw_config_reverseX (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (k p : Ch01.Band (2*h))
    (hkval : k.val = Ns branches.leftSpecies)
    (hpval : p.val = Ns branches.rightSpecies + 1) :
    insert (branches.rightSpecies,p)
      ((A05.groundConfiguration h Ns).erase (branches.leftSpecies,k)) =
        A05.groundConfiguration h (cdwTarget branches Ns) := by
  ext z
  obtain ⟨η,l⟩ := z
  have hne : branches.leftSpecies ≠ branches.rightSpecies := branches.distinct.symm
  have htL : cdwTarget branches Ns branches.leftSpecies =
      Ns branches.leftSpecies - 1 := by
    rw [cdwTarget_apply]; simp [cdwShift, hne]; ring
  have htR : cdwTarget branches Ns branches.rightSpecies =
      Ns branches.rightSpecies + 1 := by
    rw [cdwTarget_apply]; simp [cdwShift, branches.distinct]
  have hmemS : (η,l) ∈ A05.groundConfiguration h Ns ↔ l.val ≤ Ns η :=
    ground_memX h Ns η l
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

lemma cdw_pair_support_iffX (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (k p : Ch01.Band (2*h))
    (hk : (branches.leftSpecies,k) ∈ A05.groundConfiguration h Ns)
    (hp : (branches.rightSpecies,p) ∈ A05.groundConfiguration h
      (cdwTarget branches Ns)) :
    (A05.groundConfiguration h (cdwTarget branches Ns)).erase
        (branches.rightSpecies,p) =
      (A05.groundConfiguration h Ns).erase (branches.leftSpecies,k) ↔
        k.val = Ns branches.leftSpecies ∧
          p.val = Ns branches.rightSpecies + 1 := by
  constructor
  · intro he
    have hpErase : (branches.rightSpecies,p) ∉
        (A05.groundConfiguration h Ns).erase (branches.leftSpecies,k) := by
      rw [← he]
      simp
    have heq : insert (branches.rightSpecies,p)
        ((A05.groundConfiguration h Ns).erase (branches.leftSpecies,k)) =
        A05.groundConfiguration h (cdwTarget branches Ns) := by
      rw [← he]
      exact Finset.insert_erase hp
    exact cdw_config_forwardX h branches Ns k p heq hk hpErase
  · rintro ⟨hkval,hpval⟩
    have heq := cdw_config_reverseX h branches Ns k p hkval hpval
    have hpErase : (branches.rightSpecies,p) ∉
        (A05.groundConfiguration h Ns).erase (branches.leftSpecies,k) := by
      have hpSrc : (branches.rightSpecies,p) ∉ A05.groundConfiguration h Ns := by
        intro hpSrc
        have hpvalSrc := (ground_memX h Ns branches.rightSpecies p).mp hpSrc
        have hpvalT := (ground_memX h (cdwTarget branches Ns)
          branches.rightSpecies p).mp hp
        rw [cdwTarget_apply] at hpvalT
        simp [cdwShift, branches.distinct] at hpvalT
        omega
      exact fun hmem => hpSrc (Finset.mem_of_mem_erase hmem)
    have hErase : (A05.groundConfiguration h (cdwTarget branches Ns)).erase
        (branches.rightSpecies,p) =
        ((insert (branches.rightSpecies,p)
          ((A05.groundConfiguration h Ns).erase (branches.leftSpecies,k))).erase
            (branches.rightSpecies,p)) := by rw [heq]
    rw [hErase]
    simp [hpErase]

lemma cdwTopWitnessX (h : ℕ) (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns) (hR : Ns branches.rightSpecies < (h : ℤ))
    (hL : -(h : ℤ) < Ns branches.leftSpecies) :
    ∃ k p : Ch01.Band (2*h),
      k.val = Ns branches.leftSpecies ∧
      p.val = Ns branches.rightSpecies + 1 ∧
      (branches.leftSpecies,k) ∈ A05.groundConfiguration h Ns ∧
      (branches.rightSpecies,p) ∈
        A05.groundConfiguration h (cdwTarget branches Ns) := by
  obtain ⟨hllo,hlu⟩ := hN branches.leftSpecies
  obtain ⟨hrlo,hru⟩ := hN branches.rightSpecies
  let k : Ch01.Band (2*h) := ⟨Ns branches.leftSpecies, by
    unfold Ch01.inBandPredicate
    push_cast
    constructor <;> omega⟩
  let p : Ch01.Band (2*h) := ⟨Ns branches.rightSpecies + 1, by
    unfold Ch01.inBandPredicate
    push_cast
    constructor <;> omega⟩
  refine ⟨k,p,rfl,rfl,?_,?_⟩
  · apply (ground_memX h Ns branches.leftSpecies k).2
    dsimp [k]
    omega
  · apply (ground_memX h (cdwTarget branches Ns) branches.rightSpecies p).2
    rw [cdwTarget_apply]
    simp [cdwShift, branches.distinct]
    dsimp [p]
    omega

lemma ground_top_signX (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns) (ν : σ)
    (hν : -(h : ℤ)+1 ≤ Ns ν) (k : Ch01.Band (2*h))
    (hk : k.val = Ns ν) :
    Ch04.fermionSign (ν,k) (A05.groundConfiguration h Ns) =
      Ch13.kleinPhase h Ns ν := by
  have hlow : Ch07.admissible h (Ns ν-1) := by
    obtain ⟨hl, hu⟩ := hN ν
    constructor <;> omega
  have hcomp (η : σ) :
      Ch07.speciesConfiguration h (A05.groundConfiguration h Ns) η =
        Ch07.groundConfiguration h (Ns η) :=
    A05.species_joint_configuration h _ η
  have ht : (Ch07.groundConfiguration h (Ns ν)).filter (· < k) =
      Ch07.groundConfiguration h (Ns ν-1) := by
    ext l
    simp only [Ch07.groundConfiguration, Finset.mem_filter, Finset.mem_univ, true_and]
    change (l.val ≤ Ns ν ∧ l.val < k.val) ↔ l.val ≤ Ns ν-1
    rw [hk]
    omega
  have hc : ((Ch04.precedingCount (ν,k) (A05.groundConfiguration h Ns) : ℕ) : ℤ) =
      Ch13.phaseExponent h Ns ν := by
    rw [A05.preceding_count_split]
    simp only [hcomp, Nat.cast_add, Nat.cast_sum]
    simp_rw [Ch07.ground_configuration_card h hh _ (hN _)]
    unfold Ch04.precedingCount
    rw [ht, Ch07.ground_configuration_card h hh _ hlow]
    simp only [Ch13.phaseExponent]
    ring
  unfold Ch04.fermionSign Ch13.kleinPhase
  rw [← zpow_natCast, hc]

lemma cdw_pair_condition_iffX (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (k₀ p₀ k p : Ch01.Band (2*h))
    (hk₀ : (branches.leftSpecies,k₀) ∈ A05.groundConfiguration h Ns)
    (hp₀ : (branches.rightSpecies,p₀) ∈
      A05.groundConfiguration h (cdwTarget branches Ns))
    (hkval : k₀.val = Ns branches.leftSpecies)
    (hpval : p₀.val = Ns branches.rightSpecies + 1) :
    ((branches.rightSpecies,p) ∈ A05.groundConfiguration h
        (cdwTarget branches Ns) ∧
      (branches.leftSpecies,k) ∈ A05.groundConfiguration h Ns ∧
      (A05.groundConfiguration h (cdwTarget branches Ns)).erase
        (branches.rightSpecies,p) =
        (A05.groundConfiguration h Ns).erase (branches.leftSpecies,k)) ↔
      k = k₀ ∧ p = p₀ := by
  constructor
  · rintro ⟨hp,hk,he⟩
    have hval := (cdw_pair_support_iffX h branches Ns k p hk hp).mp he
    constructor
    · apply Subtype.ext
      exact hval.1.trans hkval.symm
    · apply Subtype.ext
      exact hval.2.trans hpval.symm
  · intro heq
    rcases heq with ⟨hkEq,hpEq⟩
    rw [hkEq,hpEq]
    exact ⟨hp₀,hk₀,(cdw_pair_support_iffX h branches Ns k₀ p₀ hk₀ hp₀).mpr
      ⟨hkval,hpval⟩⟩

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

lemma hole_pair_innerX {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (S T : A02.Occupation ι) (a b : ℂ) :
    inner ℂ (if i ∈ T then a • A02.ket (T.erase i) else 0)
      (if j ∈ S then b • A02.ket (S.erase j) else 0) =
    if i ∈ T ∧ j ∈ S ∧ T.erase i = S.erase j then
      star a * b else 0 := by
  by_cases hi : i ∈ T
  · by_cases hj : j ∈ S
    · by_cases he : T.erase i = S.erase j
      · simp [hi, hj, he, inner_smul_left, inner_smul_right, A02.ket_norm]
        ring
      · simp [hi, hj, he, inner_smul_left, inner_smul_right, A02.ket_inner]
    · simp [hi, hj]
  · simp [hi]

lemma inner_sum_rightX {ι E : Type*} [Fintype ι]
    [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (y : E) (f : ι → E) :
    inner ℂ y (∑ i, f i) = ∑ i, inner ℂ y (f i) := by
  rw [inner_sum (s := Finset.univ)]

lemma inner_sum_leftX {ι E : Type*} [Fintype ι]
    [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : ι → E) (y : E) :
    inner ℂ (∑ i, f i) y = ∑ i, inner ℂ (f i) y := by
  rw [← inner_conj_symm]
  rw [inner_sum (s := Finset.univ)]
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
  rw [show star (Ch13.kleinPhase h T r) = Ch13.kleinPhase h T r by
    simp [Ch13.kleinPhase]]
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
      z ^ (-(Ns r + 1) * x) * (Ch13.kleinPhase h T r *
        (A01.normalization (2*h) : ℂ)) *
        ((A01.normalization (2*h) : ℂ) * Ch13.kleinPhase h Ns l *
          z ^ (Ns l * x)) =
      (A01.normalization (2*h) : ℂ)^2 *
        (Ch13.kleinPhase h Ns l * Ch13.kleinPhase h T r) *
        (z ^ (-(Ns r + 1) * x) * z ^ (Ns l * x)) := by ring
  rw [hprod, hpow]
  have hn : (A01.normalization (2*h) : ℂ)^2 = ((2*h : ℕ) : ℂ)⁻¹ :=
    eq_inv_of_mul_eq_one_right hnorm
  rw [hn]
  ring

lemma cdw_admissibleX (h : ℕ) (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns) (hR : Ns branches.rightSpecies < (h : ℤ))
    (hL : -(h : ℤ) < Ns branches.leftSpecies) :
    A05.admissible h (cdwTarget branches Ns) := by
  intro ν
  rw [cdwTarget_apply]
  by_cases hνR : ν = branches.rightSpecies
  · subst ν
    obtain ⟨hlo,hhi⟩ := hN branches.rightSpecies
    have hne : branches.rightSpecies ≠ branches.leftSpecies := branches.distinct
    simp [cdwShift, hne]
    constructor <;> omega
  · by_cases hνL : ν = branches.leftSpecies
    · subst ν
      obtain ⟨hlo,hhi⟩ := hN branches.leftSpecies
      have hne : branches.leftSpecies ≠ branches.rightSpecies := branches.distinct.symm
      simp [cdwShift, hne]
      constructor <;> omega
    · obtain ⟨hlo,hhi⟩ := hN ν
      simp [cdwShift, hνR, hνL]
      constructor <;> omega

lemma orderCDW_ground_coeffX (h : ℕ) (hh : 0 < h)
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hR : Ns branches.rightSpecies < (h : ℤ))
    (hL : -(h : ℤ) < Ns branches.leftSpecies) (x : ℤ) :
    inner ℂ (A05.groundKet h (cdwTarget branches Ns))
      (orderCDW h (fun _ => Ch06Ext.periodicTwist (2 * h)) branches x
        (A05.groundKet h Ns)) =
      (((2 * h : ℕ) : ℂ)⁻¹) * cdwChargeCoeff h branches Ns x := by
  let T := cdwTarget branches Ns
  let b : σ → Ch06Ext.BoundaryTwist (2*h) := fun _ => Ch06Ext.periodicTwist (2*h)
  have hNT : A05.admissible h T := by
    exact cdw_admissibleX h branches Ns hN hR hL
  obtain ⟨k₀,p₀,hkval,hpval,hk₀,hp₀⟩ := cdwTopWitnessX h branches Ns hN hR hL
  have hLtop : -(h : ℤ)+1 ≤ Ns branches.leftSpecies := by omega
  have hTtop : T branches.rightSpecies = Ns branches.rightSpecies + 1 := by
    dsimp [T]
    rw [cdwTarget_apply]
    simp [cdwShift, branches.distinct]
  have hRtop : -(h : ℤ)+1 ≤ T branches.rightSpecies := by
    rw [hTtop]
    obtain ⟨hl,hu⟩ := hN branches.rightSpecies
    omega
  have hsignS := ground_top_signX h hh Ns hN branches.leftSpecies hLtop k₀ hkval
  have hsignT := ground_top_signX h hh T hNT branches.rightSpecies hRtop p₀
    (hpval.trans hTtop.symm)
  change inner ℂ (A05.groundKet h T)
    ((LinearMap.adjoint (A05.liftedAnnihilation h b branches.rightSpecies x))
      (A05.liftedAnnihilation h b branches.leftSpecies x (A05.groundKet h Ns))) = _
  rw [LinearMap.adjoint_inner_right (𝕜 := ℂ)]
  change inner ℂ
    (A05.liftedAnnihilation h b branches.rightSpecies x (A02.ket (A05.groundConfiguration h T)))
    (A05.liftedAnnihilation h b branches.leftSpecies x (A02.ket (A05.groundConfiguration h Ns))) = _
  rw [fieldKetX h b (A05.groundConfiguration h T) branches.rightSpecies x,
    fieldKetX h b (A05.groundConfiguration h Ns) branches.leftSpecies x]
  rw [inner_smul_left, inner_smul_right]
  simp_rw [inner_sum_leftX]
  simp_rw [inner_sum_rightX]
  simp_rw [hole_pair_innerX (ι := A05.Mode σ h)]
  dsimp only [T]
  simp_rw [cdw_pair_condition_iffX h branches Ns k₀ p₀ _ _ hk₀ hp₀ hkval hpval]
  rw [sum_single_pair k₀ p₀ (fun k p =>
    star (Ch06Ext.twistedCharacter (2*h) (b branches.rightSpecies) p x *
      Ch04.fermionSign (branches.rightSpecies,p) (A05.groundConfiguration h T)) *
    (Ch06Ext.twistedCharacter (2*h) (b branches.leftSpecies) k x *
      Ch04.fermionSign (branches.leftSpecies,k) (A05.groundConfiguration h Ns)))]
  rw [hsignT, hsignS]
  unfold cdwChargeCoeff
  have hcharT : Ch06Ext.twistedCharacter (2*h) (b branches.rightSpecies) p₀ x =
      A01.integerCharacter (A01.canonicalRoot (2*h)) (T branches.rightSpecies) x := by
    simp [Ch06Ext.twistedCharacter, Ch06Ext.liftPhase, b, Ch06Ext.periodicTwist,
      hpval, hTtop]
  have hcharS : Ch06Ext.twistedCharacter (2*h) (b branches.leftSpecies) k₀ x =
      A01.integerCharacter (A01.canonicalRoot (2*h)) (Ns branches.leftSpecies) x := by
    simp [Ch06Ext.twistedCharacter, Ch06Ext.liftPhase, b, Ch06Ext.periodicTwist,
      hkval]
  rw [hcharT, hcharS, ← scalar_top_pair h hh Ns T branches.leftSpecies
    branches.rightSpecies x hTtop]
  simp only [star_mul]
  rw [show star (Ch13.kleinPhase h T branches.rightSpecies) =
      Ch13.kleinPhase h T branches.rightSpecies by simp [Ch13.kleinPhase]]
  have hnconj1 : star (A01.normalization (2*h) : ℂ) =
      (A01.normalization (2*h) : ℂ) := A01.normalization_conj (2*h)
  have hnconj2 : star (A01.normalization (h*2) : ℂ) =
      (A01.normalization (h*2) : ℂ) := A01.normalization_conj (h*2)
  simp
  ring

end Bosonize.Ch20
