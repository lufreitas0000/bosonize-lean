import Bosonize.Core.A08OscillatorStates
import Bosonize.Core.V1S1PairingCombinatorics

/-!
# V1-S1: ordered Wick theorem for the existing oscillator functional

The carrier is the uncompressed free oscillator algebra;
CCR are used only through the contextual descent facts in A08.
-/

namespace Bosonize.V1S1

open scoped BigOperators

abbrev OscLinearForm (M : ℕ) := Bosonize.A08.OscGen M →₀ ℂ

def linearElement {M : ℕ} (f : OscLinearForm M) : Bosonize.A08.OscAlgebra M :=
  ∑ g ∈ f.support, (f g) • FreeAlgebra.ι ℂ g

noncomputable def formOfGenerator {M : ℕ} (g : Bosonize.A08.OscGen M) : OscLinearForm M :=
  Finsupp.single g 1

def wordElement {M : ℕ} (w : List (OscLinearForm M)) : Bosonize.A08.OscAlgebra M :=
  (w.map linearElement).prod

noncomputable def contraction {M : ℕ} (hp : Bosonize.Ch18.HyperbolicPair)
    (f g : OscLinearForm M) : ℂ :=
  Bosonize.A08.omegaP M hp (linearElement f * linearElement g)

def wordForms {M : ℕ} {n : ℕ} (f : Fin n → OscLinearForm M) :
    List (OscLinearForm M) := List.ofFn f

/-- Canonical ordered perfect matching: each edge is written with its
smaller endpoint first and each position has exactly one partner. -/
abbrev Pairing (n : ℕ) := Finset (Fin n × Fin n)

def IsPairing {n : ℕ} (P : Pairing n) : Prop :=
  (∀ e ∈ P, e.1 < e.2) ∧
  (∀ i : Fin n, ∃! j : Fin n, (i, j) ∈ P ∨ (j, i) ∈ P)

theorem pairing_representation_ext {n : ℕ} (P Q : Pairing n)
    (h : ∀ e, e ∈ P ↔ e ∈ Q) : P = Q := by
  exact Finset.ext h

noncomputable def pairingWeight {M n : ℕ} (hp : Bosonize.Ch18.HyperbolicPair)
    (f : Fin n → OscLinearForm M) (P : Pairing n) : ℂ :=
  ∏ e ∈ P, contraction hp (f e.1) (f e.2)

noncomputable def orderedPairingSum {M n : ℕ} (hp : Bosonize.Ch18.HyperbolicPair)
    (f : Fin n → OscLinearForm M) : ℂ := by
  classical
  exact ∑ P : Pairing n, if IsPairing P then pairingWeight hp f P else 0

noncomputable def dressedLinearElement {M : ℕ} (c s : ℝ)
    (f : OscLinearForm M) : Bosonize.A08.OscAlgebra M :=
  ∑ g ∈ f.support, (f g) •
    Bosonize.A08.bogoliubovMap M c s (FreeAlgebra.ι ℂ g)

noncomputable def dressedGeneratorForm {M : ℕ} (c s : ℝ)
    (g : Bosonize.A08.OscGen M) : OscLinearForm M :=
  (c : ℂ) • Finsupp.single g 1 + (s : ℂ) •
    Finsupp.single (!g.1, (Bosonize.A07Interactions.oppositeOrientation g.2.1, g.2.2)) 1

noncomputable def dressedForm {M : ℕ} (c s : ℝ) (f : OscLinearForm M) : OscLinearForm M :=
  ∑ g ∈ f.support, (f g) • dressedGeneratorForm c s g

def deleteFin {M : ℕ} (xs : List (OscLinearForm M)) (i : Fin xs.length) :=
  xs.take i.val ++ xs.drop (i.val + 1)

theorem linearElement_zero (M : ℕ) : linearElement (0 : OscLinearForm M) = 0 := by
  change (0 : OscLinearForm M).sum (fun g c => c • FreeAlgebra.ι ℂ g) = 0
  simp

theorem linearElement_add (M : ℕ) (f g : OscLinearForm M) :
    linearElement (f + g) = linearElement f + linearElement g := by
  classical
  change (f + g).sum (fun g c => c • FreeAlgebra.ι ℂ g) =
    f.sum (fun g c => c • FreeAlgebra.ι ℂ g) + g.sum (fun g c => c • FreeAlgebra.ι ℂ g)
  apply Finsupp.sum_add_index'
  · intro i; simp
  · intro i a b; simp [add_smul]

theorem zero_mode_form_eq_zero (f : OscLinearForm 0) : f = 0 := by
  ext g
  rcases g with ⟨b, ν, i⟩
  exact Fin.elim0 i

theorem linearElement_zero_mode (f : OscLinearForm 0) : linearElement f = 0 := by
  simpa [zero_mode_form_eq_zero f] using linearElement_zero 0

theorem contraction_bilinear_left (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (a b c : OscLinearForm M) :
    contraction hp (a + b) c = contraction hp a c + contraction hp b c := by
  simp only [contraction, linearElement_add, add_mul, map_add]

theorem contraction_bilinear_right (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (a b c : OscLinearForm M) :
    contraction hp a (b + c) = contraction hp a b + contraction hp a c := by
  simp only [contraction, linearElement_add, mul_add, map_add]

theorem contraction_zero_left (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (f : OscLinearForm M) : contraction hp 0 f = 0 := by
  simp [contraction, linearElement_zero]

theorem contraction_zero_right (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (f : OscLinearForm M) : contraction hp f 0 = 0 := by
  simp [contraction, linearElement_zero]

noncomputable def generatorContractionExpected {M : ℕ} (hp : Bosonize.Ch18.HyperbolicPair)
    (g h : Bosonize.A08.OscGen M) : ℂ := by
  classical
  by_cases hg : g.1 = false
  · by_cases hh : h.1 = false
    · exact if g.2.2 = h.2.2 ∧ h.2.1 = Bosonize.A07Interactions.oppositeOrientation g.2.1
        then -(↑(g.2.2.val + 1) * (hp.c : ℂ) * (hp.s : ℂ)) else 0
    · exact if g.2.2 = h.2.2 ∧ g.2.1 = h.2.1
        then ↑(g.2.2.val + 1) * (hp.c : ℂ) ^ 2 else 0
  · by_cases hh : h.1 = false
    · exact if g.2.2 = h.2.2 ∧ g.2.1 = h.2.1
        then ↑(g.2.2.val + 1) * (hp.s : ℂ) ^ 2 else 0
    · exact if g.2.2 = h.2.2 ∧ h.2.1 = Bosonize.A07Interactions.oppositeOrientation g.2.1
        then -(↑(g.2.2.val + 1) * (hp.c : ℂ) * (hp.s : ℂ)) else 0

theorem generator_contraction (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (g h : Bosonize.A08.OscGen M) :
    contraction hp (formOfGenerator g) (formOfGenerator h) =
      generatorContractionExpected hp g h := by
  classical
  let fp : Bosonize.Ch18.HyperbolicPair := ⟨1, 0, by norm_num⟩
  have hsingle (x : Bosonize.A08.OscGen M) :
      linearElement (formOfGenerator x) = FreeAlgebra.ι ℂ x := by
    simp [formOfGenerator, linearElement]
  have hfree : Bosonize.A08.omegaP M fp = Bosonize.A08.omega0 M := by
    ext a
    simp only [Bosonize.A08.omegaP, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, fp, neg_zero]
    have hb : Bosonize.A08.bogoliubovMap M 1 0 =
        AlgHom.id ℂ (Bosonize.A08.OscAlgebra M) := by
      ext x
      simp [Bosonize.A08.bogoliubovMap]
    rw [hb]
    rfl
  have hid (x : Bosonize.A08.OscGen M) :
      Bosonize.A08.bogoliubovMap M 1 0 (FreeAlgebra.ι ℂ x) = FreeAlgebra.ι ℂ x := by
    simp [Bosonize.A08.bogoliubovMap]
  have hca (p q : Bosonize.A08.OscMode M) :
      Bosonize.A08.omega0 M (FreeAlgebra.ι ℂ (true,p) * FreeAlgebra.ι ℂ (false,q)) = 0 := by
    rw [← hfree, ← hid (true,p)]
    simpa [fp, Bosonize.A08.creatorGen] using
      Bosonize.A08.omegaP_dressed_creator_mul M fp
        (FreeAlgebra.ι ℂ (false,q)) p.1 p.2
  have haa (p q : Bosonize.A08.OscMode M) :
      Bosonize.A08.omega0 M (FreeAlgebra.ι ℂ (false,p) * FreeAlgebra.ι ℂ (false,q)) = 0 := by
    rw [← hfree, ← hid (false,q)]
    simpa [fp, Bosonize.A08.annihilatorGen] using
      Bosonize.A08.omegaP_mul_dressed_annihilator M fp
        (FreeAlgebra.ι ℂ (false,p)) q.1 q.2
  have hcc (p q : Bosonize.A08.OscMode M) :
      Bosonize.A08.omega0 M (FreeAlgebra.ι ℂ (true,p) * FreeAlgebra.ι ℂ (true,q)) = 0 := by
    rw [← hfree, ← hid (true,p)]
    simpa [fp, Bosonize.A08.creatorGen] using
      Bosonize.A08.omegaP_dressed_creator_mul M fp
        (FreeAlgebra.ι ℂ (true,q)) p.1 p.2
  have hac (p q : Bosonize.A08.OscMode M) :
      Bosonize.A08.omega0 M (FreeAlgebra.ι ℂ (false,p) * FreeAlgebra.ι ℂ (true,q)) =
        if p=q then (Bosonize.A08.oscWeight p : ℂ) else 0 := by
    have hdesc := Bosonize.A08.omega0_ccr_descends M 1 1 p q
    simp only [one_mul, mul_one] at hdesc
    rw [map_sub, map_sub, map_smul, Bosonize.A08.omega0_one,
      smul_eq_mul, mul_one, hca q p] at hdesc
    by_cases hpq : p=q
    · simp [hpq] at hdesc ⊢
      linear_combination hdesc
    · simp [hpq] at hdesc ⊢
      linear_combination hdesc
  have hfreepair (x y : Bosonize.A08.OscGen M) :
      Bosonize.A08.omega0 M (FreeAlgebra.ι ℂ x * FreeAlgebra.ι ℂ y) =
        if x.1 = false ∧ y.1 = true ∧ x.2 = y.2 then
          (Bosonize.A08.oscWeight x.2 : ℂ) else 0 := by
    rcases x with ⟨b,p⟩
    rcases y with ⟨d,q⟩
    cases b <;> cases d
    · simpa using haa p q
    · simpa using hac p q
    · simpa using hca p q
    · simpa using hcc p q
  rcases g with ⟨b,p⟩
  rcases h with ⟨d,q⟩
  have hb (b : Bool) (p : Bosonize.A08.OscMode M) :
      Bosonize.A08.bogoliubovMap M hp.c (-hp.s) (FreeAlgebra.ι ℂ (b,p)) =
        (hp.c : ℂ) • FreeAlgebra.ι ℂ (b,p) + (-hp.s : ℂ) •
          FreeAlgebra.ι ℂ (!b, Bosonize.A07Interactions.oppositeOrientation p.1,p.2) := by
    simp [Bosonize.A08.bogoliubovMap]
  rw [contraction, hsingle, hsingle]
  simp only [Bosonize.A08.omegaP, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply]
  rw [map_mul]
  change Bosonize.A08.omega0 M
    (Bosonize.A08.bogoliubovMap M hp.c (-hp.s) (FreeAlgebra.ι ℂ (b,p)) *
      Bosonize.A08.bogoliubovMap M hp.c (-hp.s) (FreeAlgebra.ι ℂ (d,q))) = _
  rw [hb b p, hb d q]
  simp only [map_add, add_mul, mul_add]
  simp_rw [smul_mul_smul_comm]
  simp only [map_smul]
  rcases p with ⟨ν,i⟩
  rcases q with ⟨μ,j⟩
  cases b <;> cases d <;> cases ν <;> cases μ <;>
    simp [hfreepair, generatorContractionExpected,
      Bosonize.A07Interactions.oppositeOrientation, Bosonize.A08.oscWeight] <;> ring

theorem contraction_coeff_formula (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (f g : OscLinearForm M) :
    contraction hp f g =
      ∑ i ∈ f.support, ∑ j ∈ g.support,
        f i * g j * generatorContractionExpected hp i j := by
  classical
  change Bosonize.A08.omegaP M hp
      ((∑ i ∈ f.support, f i • FreeAlgebra.ι ℂ i) *
        ∑ j ∈ g.support, g j • FreeAlgebra.ι ℂ j) = _
  rw [Finset.sum_mul_sum]
  simp only [map_sum, map_smul, smul_mul_smul_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hsingle (x : Bosonize.A08.OscGen M) :
      linearElement (formOfGenerator x) = FreeAlgebra.ι ℂ x := by
    simp [formOfGenerator, linearElement]
  rw [← hsingle i, ← hsingle j]
  simp only [smul_eq_mul]
  change f i * g j * contraction hp (formOfGenerator i) (formOfGenerator j) = _
  rw [generator_contraction]

theorem bare_to_dressed_conversion (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (f : OscLinearForm M) :
    Bosonize.A08.bogoliubovMap M hp.c hp.s (linearElement f) =
      dressedLinearElement hp.c hp.s f := by
  classical
  simp [linearElement, dressedLinearElement, map_sum]

theorem dressed_form_evaluation (M : ℕ) (c s : ℝ) (f : OscLinearForm M) :
    linearElement (dressedForm c s f) = dressedLinearElement c s f := by
  classical
  have hsingle (g : Bosonize.A08.OscGen M) (z : ℂ) :
      linearElement (Finsupp.single g z) = z • FreeAlgebra.ι ℂ g := by
    change (Finsupp.single g z).sum (fun g a => a • FreeAlgebra.ι ℂ g) = _
    rw [Finsupp.sum_single_index (by simp)]
  have hsmul (z : ℂ) (x : OscLinearForm M) :
      linearElement (z • x) = z • linearElement x := by
    change (z • x).sum (fun g a => a • FreeAlgebra.ι ℂ g) =
      z • x.sum (fun g a => a • FreeAlgebra.ι ℂ g)
    rw [Finsupp.sum_smul_index (by intro; simp)]
    simp_rw [mul_smul]
    change (∑ g ∈ x.support, z • x g • FreeAlgebra.ι ℂ g) =
      z • (∑ g ∈ x.support, x g • FreeAlgebra.ι ℂ g)
    rw [← Finset.smul_sum]
  have hsum (u : Bosonize.A08.OscGen M → OscLinearForm M)
      (t : Finset (Bosonize.A08.OscGen M)) :
      linearElement (∑ g ∈ t, u g) = ∑ g ∈ t, linearElement (u g) := by
    induction t using Finset.induction_on with
    | empty => simp [linearElement_zero]
    | @insert a t ha ih => simp [Finset.sum_insert ha, linearElement_add, ih]
  rw [dressedForm]
  change linearElement (∑ g ∈ f.support, f g • dressedGeneratorForm c s g) = _
  rw [hsum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [hsmul]
  have hgen (g : Bosonize.A08.OscGen M) :
      linearElement (dressedGeneratorForm c s g) =
        Bosonize.A08.bogoliubovMap M c s (FreeAlgebra.ι ℂ g) := by
    rcases g with ⟨b, ν, i⟩
    change linearElement ((c : ℂ) • Finsupp.single (b, ν, i) 1 +
      (s : ℂ) • Finsupp.single (!b, Bosonize.A07Interactions.oppositeOrientation ν, i) 1) = _
    rw [linearElement_add, hsmul, hsmul, hsingle, hsingle]
    simp [Bosonize.A08.bogoliubovMap]
  rw [hgen]

theorem bare_in_dressed_coordinates (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (f : OscLinearForm M) :
    Bosonize.A08.bogoliubovMap M hp.c hp.s
      (dressedLinearElement hp.c (-hp.s) f) = linearElement f := by
  rw [← bare_to_dressed_conversion M
    ⟨hp.c, -hp.s, by nlinarith [hp.hyperbolic_id]⟩ f]
  have hinv := congr_arg (fun F => F (linearElement f))
    (Bosonize.A08.bogoliubovMap_inverse M hp.c hp.s hp.hyperbolic_id)
  simpa using hinv

theorem dressed_conversion_preserves_free_expectation (M : ℕ)
    (hp : Bosonize.Ch18.HyperbolicPair) (f g : OscLinearForm M) :
    Bosonize.A08.omegaP M hp
      (dressedLinearElement hp.c hp.s f * dressedLinearElement hp.c hp.s g) =
      Bosonize.A08.omega0 M (linearElement f * linearElement g) := by
  rw [← bare_to_dressed_conversion M hp f, ← bare_to_dressed_conversion M hp g,
    ← map_mul]
  have h := congrArg (fun F : Bosonize.A08.OscAlgebra M →ₗ[ℂ] ℂ =>
      F (linearElement f * linearElement g))
    (Bosonize.A08.omegaP_comp_bogoliubovMap M hp)
  simpa [LinearMap.comp_apply, AlgHom.toLinearMap_apply] using h

theorem omegaP_empty_word (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) :
    Bosonize.A08.omegaP M hp (wordElement ([] : List (OscLinearForm M))) = 1 := by
  simp [wordElement, Bosonize.A08.omegaP_one]

theorem omegaP_pull_through (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (f : OscLinearForm M) (tail : List (OscLinearForm M)) :
    Bosonize.A08.omegaP M hp (wordElement (f :: tail)) =
      ∑ i : Fin tail.length,
        contraction hp f (tail.get i) *
          Bosonize.A08.omegaP M hp (wordElement (deleteFin tail i)) := by
  classical
  have testcomm : ∀ (a b : Bosonize.A08.OscAlgebra M) (p : Bosonize.A08.OscMode M) (g : Bosonize.A08.OscGen M),
      Bosonize.A08.omega0 M (a * FreeAlgebra.ι ℂ (false,p) * FreeAlgebra.ι ℂ g * b) =
      Bosonize.A08.omega0 M (a * FreeAlgebra.ι ℂ g * FreeAlgebra.ι ℂ (false,p) * b) +
        Bosonize.A08.omega0 M (FreeAlgebra.ι ℂ (false,p) * FreeAlgebra.ι ℂ g) * Bosonize.A08.omega0 M (a*b) := by
    let fp : Bosonize.Ch18.HyperbolicPair := ⟨1,0,by norm_num⟩
    have hfree : Bosonize.A08.omegaP M fp = Bosonize.A08.omega0 M := by
      ext a
      simp only [Bosonize.A08.omegaP, LinearMap.comp_apply, AlgHom.toLinearMap_apply, fp, neg_zero]
      have hb : Bosonize.A08.bogoliubovMap M 1 0 = AlgHom.id ℂ (Bosonize.A08.OscAlgebra M) := by
        ext x
        simp [Bosonize.A08.bogoliubovMap]
      rw [hb]
      rfl
    have hA (a : Bosonize.A08.OscAlgebra M) (p : Bosonize.A08.OscMode M) :
        Bosonize.A08.omega0 M (a * FreeAlgebra.ι ℂ (false,p)) = 0 := by
      have h := Bosonize.A08.omegaP_mul_dressed_annihilator M fp a p.1 p.2
      simpa [hfree, fp, Bosonize.A08.annihilatorGen, Bosonize.A08.bogoliubovMap] using h
    intro a b p g
    rcases g with ⟨d,q⟩
    cases d
    · have h := Bosonize.A08.omega0_ccr_descends_aa M a b p q
      have hq := hA (FreeAlgebra.ι ℂ (false,p)) q
      simp only [mul_sub, sub_mul, map_sub, ← mul_assoc] at h
      rw [hq, zero_mul, add_zero]
      exact sub_eq_zero.mp h
    · have h := Bosonize.A08.omega0_ccr_descends M a b p q
      have hq := Bosonize.A08.omega0_ccr_descends M 1 1 p q
      simp only [one_mul, mul_one, map_sub, map_smul, Bosonize.A08.omega0_one, smul_eq_mul,
        mul_one, hA] at hq
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
        mul_one, map_sub, map_smul, smul_eq_mul, ← mul_assoc] at h
      linear_combination h - hq * Bosonize.A08.omega0 M (a*b)
  have testlinear (a b : Bosonize.A08.OscAlgebra M) (p : Bosonize.A08.OscMode M) (f : OscLinearForm M) :
      Bosonize.A08.omega0 M (a * FreeAlgebra.ι ℂ (false,p) * linearElement f * b) =
      Bosonize.A08.omega0 M (a * linearElement f * FreeAlgebra.ι ℂ (false,p) * b) +
        Bosonize.A08.omega0 M (FreeAlgebra.ι ℂ (false,p) * linearElement f) * Bosonize.A08.omega0 M (a*b) := by
    classical
    simp only [linearElement, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
      smul_mul_assoc, map_sum, map_smul, smul_eq_mul]
    simp_rw [testcomm]
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro g hg
    ring
  have testcross (p : Bosonize.A08.OscMode M) (tail : List (OscLinearForm M)) :
      ∀ a : Bosonize.A08.OscAlgebra M,
      Bosonize.A08.omega0 M (a * FreeAlgebra.ι ℂ (false,p) * wordElement tail) =
        (∑ i : Fin tail.length, Bosonize.A08.omega0 M (FreeAlgebra.ι ℂ (false,p) * linearElement (tail.get i)) *
          Bosonize.A08.omega0 M (a * wordElement (deleteFin tail i))) +
        Bosonize.A08.omega0 M (a * wordElement tail * FreeAlgebra.ι ℂ (false,p)) := by
    classical
    induction tail with
    | nil => intro a; simp [wordElement]
    | cons f tail ih =>
      intro a
      have hword (f : OscLinearForm M) (t : List (OscLinearForm M)) :
          wordElement (f::t) = linearElement f * wordElement t := rfl
      have hdel (i : Fin tail.length) :
          deleteFin (f::tail) i.succ = f :: deleteFin tail i := by
        simp [deleteFin, List.take_succ_cons, List.drop_succ_cons]
      rw [hword, ← mul_assoc, testlinear, ih]
      simp only [List.length_cons, Fin.sum_univ_succ, List.get_cons_zero,
        hdel, hword]
      simp [deleteFin, mul_assoc]
      ring
  have testfree (f : OscLinearForm M) (tail : List (OscLinearForm M)) :
      Bosonize.A08.omega0 M (wordElement (f::tail)) =
        ∑ i : Fin tail.length, Bosonize.A08.omega0 M (linearElement f * linearElement (tail.get i)) *
          Bosonize.A08.omega0 M (wordElement (deleteFin tail i)) := by
    classical
    let fp : Bosonize.Ch18.HyperbolicPair := ⟨1,0,by norm_num⟩
    have hfree : Bosonize.A08.omegaP M fp = Bosonize.A08.omega0 M := by
      ext a
      simp only [Bosonize.A08.omegaP, LinearMap.comp_apply, AlgHom.toLinearMap_apply, fp, neg_zero]
      have hb : Bosonize.A08.bogoliubovMap M 1 0 = AlgHom.id ℂ (Bosonize.A08.OscAlgebra M) := by
        ext x
        simp [Bosonize.A08.bogoliubovMap]
      rw [hb]
      rfl
    have hA (a : Bosonize.A08.OscAlgebra M) (p : Bosonize.A08.OscMode M) :
        Bosonize.A08.omega0 M (a * FreeAlgebra.ι ℂ (false,p)) = 0 := by
      have h := Bosonize.A08.omegaP_mul_dressed_annihilator M fp a p.1 p.2
      simpa [hfree, fp, Bosonize.A08.annihilatorGen, Bosonize.A08.bogoliubovMap] using h
    have hC (a : Bosonize.A08.OscAlgebra M) (p : Bosonize.A08.OscMode M) :
        Bosonize.A08.omega0 M (FreeAlgebra.ι ℂ (true,p) * a) = 0 := by
      have h := Bosonize.A08.omegaP_dressed_creator_mul M fp a p.1 p.2
      simpa [hfree, fp, Bosonize.A08.creatorGen, Bosonize.A08.bogoliubovMap] using h
    have hg (g : Bosonize.A08.OscGen M) :
        Bosonize.A08.omega0 M (FreeAlgebra.ι ℂ g * wordElement tail) =
          ∑ i : Fin tail.length, Bosonize.A08.omega0 M (FreeAlgebra.ι ℂ g * linearElement (tail.get i)) *
            Bosonize.A08.omega0 M (wordElement (deleteFin tail i)) := by
      rcases g with ⟨d,p⟩
      cases d
      · simpa [hA] using testcross p tail 1
      · simp [hC]
    change Bosonize.A08.omega0 M (linearElement f * wordElement tail) = _
    simp only [linearElement, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
      smul_eq_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro g hgmem
    rw [hg, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [linearElement]
    ring
  classical
  let T : OscLinearForm M → OscLinearForm M := dressedForm hp.c (-hp.s)
  let B := Bosonize.A08.bogoliubovMap M hp.c (-hp.s)
  have hT (g : OscLinearForm M) : linearElement (T g) = B (linearElement g) := by
    rw [show T g = dressedForm hp.c (-hp.s) g from rfl, dressed_form_evaluation]
    simp [B, dressedLinearElement, linearElement, map_sum]
  have hw (w : List (OscLinearForm M)) : wordElement (w.map T) = B (wordElement w) := by
    induction w with
    | nil => simp [wordElement]
    | cons g w ih =>
      change linearElement (T g) * wordElement (w.map T) = B (linearElement g * wordElement w)
      rw [hT, ih, map_mul]
  have ho (w : List (OscLinearForm M)) :
      Bosonize.A08.omega0 M (wordElement (w.map T)) = Bosonize.A08.omegaP M hp (wordElement w) := by
    rw [hw]
    rfl
  have hq (g : OscLinearForm M) :
      Bosonize.A08.omega0 M (linearElement (T f) * linearElement (T g)) = contraction hp f g := by
    rw [hT, hT, ← map_mul]
    rfl
  have h := testfree (T f) (tail.map T)
  change Bosonize.A08.omega0 M (wordElement ((f::tail).map T)) = _ at h
  rw [ho] at h
  simp only [List.get_eq_getElem, List.getElem_map] at h
  convert h using 1
  apply Fintype.sum_equiv (finCongr (List.length_map T).symm)
  intro i
  rw [hq]
  congr 1
  have hd : deleteFin (tail.map T) ((finCongr (List.length_map T).symm) i) = (deleteFin tail i).map T := by
    simp [deleteFin, List.map_append]
  rw [hd, ho]

theorem omegaP_ordered_wick (M n : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (f : Fin n → OscLinearForm M) :
    Bosonize.A08.omegaP M hp (wordElement (wordForms f)) =
      orderedPairingSum hp f := by
  classical
  have good_univ_iff (n : ℕ) (P : Bosonize.V1S1.Pairing n) :
      Pairings.Good Finset.univ P ↔ Bosonize.V1S1.IsPairing P := by
    constructor
    · rintro ⟨hord,h⟩
      refine ⟨hord,?_⟩
      intro i
      obtain ⟨j,hj⟩ := (h i).1.mp (Finset.mem_univ i)
      exact ⟨j,hj, fun k hk => (h i).2 k j hk hj⟩
    · rintro ⟨hord,h⟩
      refine ⟨hord,?_⟩
      intro i
      obtain ⟨j,hj,hu⟩ := h i
      exact ⟨⟨fun _ => ⟨j,hj⟩,fun _ => Finset.mem_univ i⟩,
        fun a b ha hb => (hu a ha).trans (hu b hb).symm⟩
  have label_recurrence (M n : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
      (F : Fin n → OscLinearForm M) (x : Fin n) (L : List (Fin n)) (hn : L.Nodup) :
      Bosonize.A08.omegaP M hp (wordElement ((x::L).map F)) =
        ∑ i : Fin L.length, contraction hp (F x) (F (L.get i)) *
          Bosonize.A08.omegaP M hp (wordElement ((L.erase (L.get i)).map F)) := by
    classical
    have h := omegaP_pull_through M hp (F x) (L.map F)
    change Bosonize.A08.omegaP M hp (wordElement ((x::L).map F)) = _ at h
    convert h using 1
    apply Fintype.sum_equiv (finCongr (List.length_map F).symm)
    intro i
    have hd : deleteFin (L.map F) ((finCongr (List.length_map F).symm) i) =
        (L.erase (L.get i)).map F := by
      rw [hn.erase_get, List.eraseIdx_eq_take_drop_succ]
      simp [deleteFin,List.map_append]
    rw [hd]
    simp [List.get_eq_getElem]
  have wick_list (M n : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
      (F : Fin n → OscLinearForm M) : ∀ k : ℕ, ∀ L : List (Fin n), L.length=k →
      List.Pairwise (·<·) L →
      Bosonize.A08.omegaP M hp (wordElement (L.map F)) =
        Pairings.sumOn (fun i j => contraction hp (F i) (F j)) L.toFinset := by
    classical
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro L hlen hs
      cases L with
      | nil => simp [wordElement,Bosonize.A08.omegaP_one,Pairings.sumOn_empty]
      | cons x L =>
        obtain ⟨hmin,hsL⟩ := List.pairwise_cons.mp hs
        have hn := hsL.nodup
        have hx : x∉L.toFinset := by
          simp only [List.mem_toFinset]
          intro hx
          exact (lt_irrefl x) (hmin x hx)
        rw [label_recurrence M n hp F x L hn, List.toFinset_cons,
          Pairings.sumOn_first _ _ _ hx (by simpa using hmin)]
        let E : Fin L.length ≃ {y // y∈L.toFinset} := Equiv.ofBijective
          (fun i => ⟨L.get i,by simp⟩)
          ⟨fun i j hij => (List.nodup_iff_injective_get.mp hn) (congrArg Subtype.val hij),
            by intro y; obtain ⟨i,hi⟩ := List.get_of_mem (List.mem_toFinset.mp y.property)
               exact ⟨i,Subtype.ext hi⟩⟩
        apply Fintype.sum_equiv E
        intro i
        change contraction hp (F x) (F (L.get i)) * _ =
          contraction hp (F x) (F (L.get i)) * _
        congr 1
        have hl : (L.erase (L.get i)).length < k := by
          have he := List.length_erase_of_mem (List.get_mem L i)
          simp only [List.length_cons] at hlen
          omega
        rw [ih _ hl _ rfl (hsL.sublist List.erase_sublist)]
        congr 1
        ext z
        simp [hn.mem_erase_iff,E]
  classical
  have h := wick_list M n hp f n (List.ofFn (id : Fin n → Fin n))
    (by simp) (List.pairwise_ofFn.mpr (by intro i j hij; exact hij))
  have hv : (List.ofFn (id : Fin n → Fin n)).toFinset = Finset.univ := by
    ext i
    simp
  simpa [List.map_ofFn,wordForms,hv,Pairings.sumOn_as_sum,good_univ_iff,
    orderedPairingSum,pairingWeight] using h

theorem omegaP_odd_word_zero (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (w : List (OscLinearForm M)) (hodd : Odd w.length) :
    Bosonize.A08.omegaP M hp (wordElement w) = 0 := by
  classical
  have aux : ∀ n : ℕ, ∀ v : List (OscLinearForm M), v.length = n → Odd n →
      Bosonize.A08.omegaP M hp (wordElement v) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv ho
      cases v with
      | nil => simp at hv; subst n; norm_num at ho
      | cons f tail =>
        rw [omegaP_pull_through]
        apply Finset.sum_eq_zero
        intro i _
        have hi := i.isLt
        have hd : (deleteFin tail i).length + 2 = n := by
          simp only [deleteFin, List.length_append, List.length_take,
            List.length_drop] at *
          simp only [List.length_cons] at hv
          omega
        have hod : Odd (deleteFin tail i).length := by
          obtain ⟨k, hk⟩ := ho
          exact ⟨k - 1, by omega⟩
        rw [ih (deleteFin tail i).length (by omega) _ rfl hod, mul_zero]
  exact aux w.length w rfl hodd

theorem omegaP_single_odd_moment (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (f : OscLinearForm M) (k : ℕ) :
    Bosonize.A08.omegaP M hp ((linearElement f) ^ (2 * k + 1)) = 0 := by
  have h := omegaP_odd_word_zero M hp (List.replicate (2 * k + 1) f)
    (by simp)
  simpa [wordElement, List.map_replicate, List.prod_replicate] using h

theorem omegaP_single_even_moment (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (f : OscLinearForm M) (k : ℕ) :
    Bosonize.A08.omegaP M hp ((linearElement f) ^ (2 * k)) =
      ((((2 * k).factorial : ℕ) : ℂ) /
        (((2 ^ k) * k.factorial : ℕ) : ℂ)) *
        (contraction hp f f) ^ k := by
  classical
  have hrec (n : ℕ) :
      Bosonize.A08.omegaP M hp (linearElement f ^ (n+2)) =
        (n+1 : ℂ) * contraction hp f f *
          Bosonize.A08.omegaP M hp (linearElement f ^ n) := by
    have hdel (i : Fin (List.replicate (n+1) f).length) :
        deleteFin (List.replicate (n+1) f) i = List.replicate n f := by
      have hi : i.val < n+1 := by simpa using i.isLt
      simp only [deleteFin, List.take_replicate, List.drop_replicate, ← List.replicate_add]
      congr 1
      omega
    have h := omegaP_pull_through M hp f (List.replicate (n+1) f)
    simp only [hdel] at h
    simpa [wordElement, List.map_replicate, List.prod_replicate, pow_succ', mul_assoc,
      Finset.sum_const, Nat.cast_add, Nat.cast_one] using h
  induction k with
  | zero => simp [Bosonize.A08.omegaP_one]
  | succ k ih =>
    rw [show 2 * (k+1) = 2*k+2 by omega, hrec, ih]
    simp only [Nat.factorial_succ, pow_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have ht : (2 : ℂ)^k ≠ 0 := pow_ne_zero _ (by norm_num)
    have hk : (k : ℂ)+1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
    field_simp
    ring

def freePair : Bosonize.Ch18.HyperbolicPair := ⟨1, 0, by norm_num⟩

theorem free_vacuum_order_sensitive (i : Fin 1) :
    Bosonize.A08.omegaP 1 freePair
      (wordElement [formOfGenerator (false, (.right, i)),
        formOfGenerator (true, (.right, i)),
        formOfGenerator (false, (.right, i)),
        formOfGenerator (true, (.right, i))]) = 1 := by
  simp [wordElement, formOfGenerator, linearElement, Bosonize.A08.omegaP,
    Bosonize.A08.omega0, freePair, Bosonize.A08.bogoliubovMap,
    Bosonize.A08.oscRep, Bosonize.A08.oscAnnihilation,
    Bosonize.A08.oscCreation, Bosonize.A08.oscWeight]

noncomputable def squeezedPair : Bosonize.Ch18.HyperbolicPair :=
  ⟨(5 / 3 : ℝ), (4 / 3 : ℝ), by norm_num⟩

noncomputable def squeezedTestForm : OscLinearForm 1 :=
  formOfGenerator (false, (.right, 0)) + formOfGenerator (true, (.right, 0)) +
  formOfGenerator (false, (.left, 0)) + formOfGenerator (true, (.left, 0))

theorem squeezed_test_variance :
    contraction squeezedPair squeezedTestForm squeezedTestForm = (2 / 9 : ℂ) := by
  simp [squeezedTestForm, contraction_bilinear_left, contraction_bilinear_right,
    generator_contraction, generatorContractionExpected, squeezedPair,
    Bosonize.A07Interactions.oppositeOrientation]
  norm_num

theorem squeezed_test_fourth_moment :
    Bosonize.A08.omegaP 1 squeezedPair ((linearElement squeezedTestForm) ^ 4) =
      (4 / 27 : ℂ) := by
  have h := omegaP_single_even_moment 1 squeezedPair squeezedTestForm 2
  norm_num [squeezed_test_variance] at h
  exact h

theorem mixed_bare_dressed_word (i : Fin 1) :
    Bosonize.A08.omegaP 1 squeezedPair
      (wordElement [formOfGenerator (false, (.right, i)),
        dressedForm squeezedPair.c squeezedPair.s
          (formOfGenerator (true, (.right, i)))]) =
      (((i.val + 1 : ℕ) : ℂ) * (squeezedPair.c : ℂ)) := by
  classical
  change Bosonize.A08.omegaP 1 squeezedPair
    (linearElement (formOfGenerator (false, (.right, i))) *
      (linearElement (dressedForm squeezedPair.c squeezedPair.s
        (formOfGenerator (true, (.right, i)))) * 1)) = _
  simp only [mul_one]
  change contraction squeezedPair
    (formOfGenerator (false, (.right, i)))
    (dressedForm squeezedPair.c squeezedPair.s
      (formOfGenerator (true, (.right, i)))) = _
  have hd : dressedForm squeezedPair.c squeezedPair.s
      (formOfGenerator (true, (.right, i))) =
        (squeezedPair.c : ℂ) • formOfGenerator (true, (.right, i)) +
        (squeezedPair.s : ℂ) • formOfGenerator (false, (.left, i)) := by
    simp [dressedForm, dressedGeneratorForm, formOfGenerator,
      Bosonize.A07Interactions.oppositeOrientation]
  rw [hd, contraction_bilinear_right]
  have hscale (z : ℂ) (g : OscLinearForm 1) :
      contraction squeezedPair (formOfGenerator (false, (.right, i))) (z • g) =
        z * contraction squeezedPair (formOfGenerator (false, (.right, i))) g := by
    rw [contraction_coeff_formula, contraction_coeff_formula]
    by_cases hz : z = 0
    · simp [hz]
    · simp [Finsupp.support_smul_eq, hz, Finset.mul_sum,
        mul_left_comm, mul_comm]
  rw [hscale, hscale, generator_contraction, generator_contraction]
  simp [generatorContractionExpected, squeezedPair,
    Bosonize.A07Interactions.oppositeOrientation]
  norm_num

end Bosonize.V1S1
