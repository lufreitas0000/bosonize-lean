import Bosonize.Core.A08OscillatorStates

/-!
# V1-S1: ordered Wick theorem for the existing oscillator functional

Phase A candidate. The carrier is the uncompressed free oscillator algebra;
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
  sorry

theorem linearElement_add (M : ℕ) (f g : OscLinearForm M) :
    linearElement (f + g) = linearElement f + linearElement g := by
  sorry

theorem zero_mode_form_eq_zero (f : OscLinearForm 0) : f = 0 := by
  sorry

theorem linearElement_zero_mode (f : OscLinearForm 0) : linearElement f = 0 := by
  sorry

theorem contraction_bilinear_left (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (a b c : OscLinearForm M) :
    contraction hp (a + b) c = contraction hp a c + contraction hp b c := by
  sorry

theorem contraction_bilinear_right (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (a b c : OscLinearForm M) :
    contraction hp a (b + c) = contraction hp a b + contraction hp a c := by
  sorry

theorem contraction_zero_left (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (f : OscLinearForm M) : contraction hp 0 f = 0 := by
  sorry

theorem contraction_zero_right (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (f : OscLinearForm M) : contraction hp f 0 = 0 := by
  sorry

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
  sorry

theorem contraction_coeff_formula (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (f g : OscLinearForm M) :
    contraction hp f g =
      ∑ i ∈ f.support, ∑ j ∈ g.support,
        f i * g j * generatorContractionExpected hp i j := by
  sorry

theorem bare_to_dressed_conversion (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (f : OscLinearForm M) :
    Bosonize.A08.bogoliubovMap M hp.c hp.s (linearElement f) =
      dressedLinearElement hp.c hp.s f := by
  sorry

theorem dressed_form_evaluation (M : ℕ) (c s : ℝ) (f : OscLinearForm M) :
    linearElement (dressedForm c s f) = dressedLinearElement c s f := by
  sorry

theorem bare_in_dressed_coordinates (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (f : OscLinearForm M) :
    Bosonize.A08.bogoliubovMap M hp.c hp.s
      (dressedLinearElement hp.c (-hp.s) f) = linearElement f := by
  sorry

theorem dressed_conversion_preserves_free_expectation (M : ℕ)
    (hp : Bosonize.Ch18.HyperbolicPair) (f g : OscLinearForm M) :
    Bosonize.A08.omegaP M hp
      (dressedLinearElement hp.c hp.s f * dressedLinearElement hp.c hp.s g) =
      Bosonize.A08.omega0 M (linearElement f * linearElement g) := by
  sorry

theorem omegaP_empty_word (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) :
    Bosonize.A08.omegaP M hp (wordElement ([] : List (OscLinearForm M))) = 1 := by
  sorry

theorem omegaP_pull_through (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (f : OscLinearForm M) (tail : List (OscLinearForm M)) :
    Bosonize.A08.omegaP M hp (wordElement (f :: tail)) =
      ∑ i : Fin tail.length,
        contraction hp f (tail.get i) *
          Bosonize.A08.omegaP M hp (wordElement (deleteFin tail i)) := by
  sorry

theorem omegaP_ordered_wick (M n : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (f : Fin n → OscLinearForm M) :
    Bosonize.A08.omegaP M hp (wordElement (wordForms f)) =
      orderedPairingSum hp f := by
  sorry

theorem omegaP_odd_word_zero (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (w : List (OscLinearForm M)) (hodd : Odd w.length) :
    Bosonize.A08.omegaP M hp (wordElement w) = 0 := by
  sorry

theorem omegaP_single_odd_moment (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (f : OscLinearForm M) (k : ℕ) :
    Bosonize.A08.omegaP M hp ((linearElement f) ^ (2 * k + 1)) = 0 := by
  sorry

theorem omegaP_single_even_moment (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (f : OscLinearForm M) (k : ℕ) :
    Bosonize.A08.omegaP M hp ((linearElement f) ^ (2 * k)) =
      ((((2 * k).factorial : ℕ) : ℂ) /
        (((2 ^ k) * k.factorial : ℕ) : ℂ)) *
        (contraction hp f f) ^ k := by
  sorry

def freePair : Bosonize.Ch18.HyperbolicPair := ⟨1, 0, by norm_num⟩

theorem free_vacuum_order_sensitive (i : Fin 1) :
    Bosonize.A08.omegaP 1 freePair
      (wordElement [formOfGenerator (false, (.right, i)),
        formOfGenerator (true, (.right, i)),
        formOfGenerator (false, (.right, i)),
        formOfGenerator (true, (.right, i))]) = 1 := by
  sorry

noncomputable def squeezedPair : Bosonize.Ch18.HyperbolicPair :=
  ⟨(5 / 3 : ℝ), (4 / 3 : ℝ), by norm_num⟩

noncomputable def squeezedTestForm : OscLinearForm 1 :=
  formOfGenerator (false, (.right, 0)) + formOfGenerator (true, (.right, 0)) +
  formOfGenerator (false, (.left, 0)) + formOfGenerator (true, (.left, 0))

theorem squeezed_test_variance :
    contraction squeezedPair squeezedTestForm squeezedTestForm = (2 / 9 : ℂ) := by
  sorry

theorem squeezed_test_fourth_moment :
    Bosonize.A08.omegaP 1 squeezedPair ((linearElement squeezedTestForm) ^ 4) =
      (4 / 27 : ℂ) := by
  sorry

theorem mixed_bare_dressed_word (i : Fin 1) :
    Bosonize.A08.omegaP 1 squeezedPair
      (wordElement [formOfGenerator (false, (.right, i)),
        dressedForm squeezedPair.c squeezedPair.s
          (formOfGenerator (true, (.right, i)))]) =
      (((i.val + 1 : ℕ) : ℂ) * (squeezedPair.c : ℂ)) := by
  sorry

end Bosonize.V1S1
