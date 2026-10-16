import Bosonize.Core.Ch18Bogoliubov

namespace Bosonize.A08

open scoped BigOperators Matrix

abbrev OscMode (M : ℕ) := Bosonize.A06.Orientation × Fin M

def oscWeight {M : ℕ} (p : OscMode M) : ℕ := p.2.val + 1

abbrev OscPoly (M : ℕ) := MvPolynomial (OscMode M) ℂ

def oscMonomialNorm {M : ℕ} (r : OscMode M →₀ ℕ) : ℕ :=
  r.prod (fun p k => oscWeight p ^ k * k.factorial)

noncomputable def oscPairing (M : ℕ) (p q : OscPoly M) : ℂ :=
  ∑ r ∈ p.support, star (MvPolynomial.lcoeff ℂ r p) * (oscMonomialNorm r : ℂ) * MvPolynomial.lcoeff ℂ r q

noncomputable def oscCreation (M : ℕ) (p : OscMode M) : Module.End ℂ (OscPoly M) :=
  LinearMap.mulLeft ℂ (MvPolynomial.X p)

noncomputable def oscAnnihilation (M : ℕ) (p : OscMode M) : Module.End ℂ (OscPoly M) :=
  (oscWeight p : ℂ) • (MvPolynomial.pderiv p).toLinearMap

abbrev OscGen (M : ℕ) := Bool × OscMode M

abbrev OscAlgebra (M : ℕ) := FreeAlgebra ℂ (OscGen M)

noncomputable def creatorGen (M : ℕ) (ν : Bosonize.A06.Orientation) (i : Fin M) : OscAlgebra M :=
  FreeAlgebra.ι ℂ (true, (ν, i))

noncomputable def annihilatorGen (M : ℕ) (ν : Bosonize.A06.Orientation) (i : Fin M) : OscAlgebra M :=
  FreeAlgebra.ι ℂ (false, (ν, i))

noncomputable def oscRep (M : ℕ) : OscAlgebra M →ₐ[ℂ] Module.End ℂ (OscPoly M) :=
  FreeAlgebra.lift ℂ (fun g => if g.1 then oscCreation M g.2 else oscAnnihilation M g.2)

noncomputable def omega0 (M : ℕ) : OscAlgebra M →ₗ[ℂ] ℂ :=
  (MvPolynomial.lcoeff ℂ 0) ∘ₗ (LinearMap.applyₗ (1 : OscPoly M)) ∘ₗ (oscRep M).toLinearMap

noncomputable def bogoliubovMap (M : ℕ) (c s : ℝ) : OscAlgebra M →ₐ[ℂ] OscAlgebra M :=
  FreeAlgebra.lift ℂ (fun g => (c : ℂ) • FreeAlgebra.ι ℂ g +
    (s : ℂ) • FreeAlgebra.ι ℂ (!g.1, (Bosonize.A07Interactions.oppositeOrientation g.2.1, g.2.2)))

noncomputable def omegaP (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) : OscAlgebra M →ₗ[ℂ] ℂ :=
  omega0 M ∘ₗ (bogoliubovMap M hp.c (-hp.s)).toLinearMap

abbrev OscWord (M : ℕ) := List (OscGen M)

def wordDagger {M : ℕ} (w : OscWord M) : OscWord M :=
  (w.map fun g => (!g.1, g.2)).reverse

noncomputable def wordElement (M : ℕ) (w : OscWord M) : OscAlgebra M :=
  (w.map (FreeAlgebra.ι ℂ)).prod

noncomputable def gramSum (M : ℕ) {n : ℕ} (ω : OscAlgebra M →ₗ[ℂ] ℂ) (w : Fin n → OscWord M) (z : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, star (z i) * z j * ω (wordElement M (wordDagger (w i)) * wordElement M (w j))

theorem oscPairing_monomial (M : ℕ) (r s : OscMode M →₀ ℕ) :
    oscPairing M (MvPolynomial.monomial r 1) (MvPolynomial.monomial s 1) =
      if r = s then (oscMonomialNorm r : ℂ) else 0 := by
  classical
  simp [oscPairing, MvPolynomial.lcoeff_apply, MvPolynomial.coeff_monomial]
  split_ifs <;> simp_all

theorem oscPairing_conj (M : ℕ) (p q : OscPoly M) :
    star (oscPairing M p q) = oscPairing M q p := by
  classical
  have pairing_add_left (p q r : OscPoly M) : oscPairing M (p + q) r = oscPairing M p r + oscPairing M q r := by
    change ((MvPolynomial.basisMonomials (OscMode M) ℂ).repr (p + q)).sum (fun v a => star a * (oscMonomialNorm v : ℂ) * MvPolynomial.lcoeff ℂ v r) = _
    rw [map_add, Finsupp.sum_add_index']
    · rfl
    · intro v; simp
    · intro v a b; simp [add_mul]
  have pairing_smul_left (a : ℂ) (p q : OscPoly M) : oscPairing M (a • p) q = star a * oscPairing M p q := by
    by_cases ha : a = 0
    · subst a; simp [oscPairing]
    · have hs : (a • p).support = p.support := MvPolynomial.support_smul_eq ha p
      simp only [oscPairing, hs, map_smul, smul_eq_mul, star_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
  have pairing_add_right (p q r : OscPoly M) : oscPairing M p (q + r) = oscPairing M p q + oscPairing M p r := by
    simp only [oscPairing, map_add, mul_add, Finset.sum_add_distrib]
  have pairing_smul_right (a : ℂ) (p q : OscPoly M) : oscPairing M p (a • q) = a * oscPairing M p q := by
    simp only [oscPairing, map_smul, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  induction p using MvPolynomial.induction_on' with
  | monomial r a =>
    have he : MvPolynomial.monomial r a = a • MvPolynomial.monomial r 1 := by simp [MvPolynomial.smul_monomial]
    rw [he, pairing_smul_left, pairing_smul_right, star_mul, star_star]
    induction q using MvPolynomial.induction_on' with
    | monomial s b =>
      have hs : MvPolynomial.monomial s b = b • MvPolynomial.monomial s 1 := by simp [MvPolynomial.smul_monomial]
      rw [hs, pairing_smul_right, pairing_smul_left, oscPairing_monomial, oscPairing_monomial]
      by_cases hrs : r = s
      · subst s; simp [star_mul, mul_comm]
      · simp [hrs, Ne.symm hrs]
    | add p q hp hq => simp only [pairing_add_left, pairing_add_right, star_add, mul_add, add_mul] at *; exact congrArg₂ (· + ·) hp hq
  | add p q hp hq => simp [pairing_add_left, pairing_add_right, star_add, hp, hq]

theorem oscPairing_self_nonneg (M : ℕ) (p : OscPoly M) :
    0 ≤ (oscPairing M p p).re := by
  classical
  have term (z : ℂ) (n : ℕ) : (star z * (n : ℂ) * z).re = Complex.normSq z * (n : ℝ) := by
    simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.natCast_re, Complex.natCast_im, Complex.normSq_apply]
    ring
  unfold oscPairing
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro r hr
  rw [term]
  exact mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

theorem oscPairing_self_eq_zero (M : ℕ) (p : OscPoly M) :
    oscPairing M p p = 0 ↔ p = 0 := by
  classical
  have norm_pos (r : OscMode M →₀ ℕ) : 0 < oscMonomialNorm r := by
    unfold oscMonomialNorm Finsupp.prod
    apply Finset.prod_pos
    intro p hp
    exact mul_pos (pow_pos (Nat.succ_pos _) _) (Nat.factorial_pos _)
  have term (z : ℂ) (n : ℕ) : (star z * (n : ℂ) * z).re = Complex.normSq z * (n : ℝ) := by
    simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.natCast_re, Complex.natCast_im, Complex.normSq_apply]
    ring
  constructor
  · intro h
    have hz : ∑ r ∈ p.support, Complex.normSq (MvPolynomial.lcoeff ℂ r p) * (oscMonomialNorm r : ℝ) = 0 := by
      have hh := congrArg Complex.re h
      simpa only [oscPairing, Complex.re_sum, term, Complex.zero_re] using hh
    have each := (Finset.sum_eq_zero_iff_of_nonneg (fun r (_ : r ∈ p.support) => mul_nonneg (Complex.normSq_nonneg (MvPolynomial.lcoeff ℂ r p)) (Nat.cast_nonneg (oscMonomialNorm r)))).mp hz
    apply MvPolynomial.ext
    intro r
    change MvPolynomial.lcoeff ℂ r p = 0
    by_cases hr : r ∈ p.support
    · have hn : (0 : ℝ) < (oscMonomialNorm r : ℝ) := Nat.cast_pos.mpr (norm_pos r)
      exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp (each r hr)).resolve_right (ne_of_gt hn))
    · exact MvPolynomial.notMem_support_iff.mp hr
  · rintro rfl
    simp [oscPairing]

theorem oscCreation_pairing_adjoint (M : ℕ) (p : OscMode M) (x y : OscPoly M) :
    oscPairing M (oscCreation M p x) y = oscPairing M x (oscAnnihilation M p y) := by
  classical
  have _instO : Fintype Bosonize.A06.Orientation := ⟨⟨{.right, .left}, by decide⟩, fun o => by cases o <;> simp⟩
  have pairing_add_left (p q r : OscPoly M) : oscPairing M (p + q) r = oscPairing M p r + oscPairing M q r := by
    change ((MvPolynomial.basisMonomials (OscMode M) ℂ).repr (p + q)).sum (fun v a => star a * (oscMonomialNorm v : ℂ) * MvPolynomial.lcoeff ℂ v r) = _
    rw [map_add, Finsupp.sum_add_index']
    · rfl
    · intro v; simp
    · intro v a b; simp [add_mul]
  have pairing_smul_left (a : ℂ) (p q : OscPoly M) : oscPairing M (a • p) q = star a * oscPairing M p q := by
    by_cases ha : a = 0
    · subst a; simp [oscPairing]
    · have hs : (a • p).support = p.support := MvPolynomial.support_smul_eq ha p
      simp only [oscPairing, hs, map_smul, smul_eq_mul, star_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
  have pairing_add_right (p q r : OscPoly M) : oscPairing M p (q + r) = oscPairing M p q + oscPairing M p r := by
    simp only [oscPairing, map_add, mul_add, Finset.sum_add_distrib]
  have pairing_smul_right (a : ℂ) (p q : OscPoly M) : oscPairing M p (a • q) = a * oscPairing M p q := by
    simp only [oscPairing, map_smul, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have norm_step (r : OscMode M →₀ ℕ) : oscMonomialNorm (r + Finsupp.single p 1) = oscWeight p * (r p + 1) * oscMonomialNorm r := by
    have hprod (s : OscMode M →₀ ℕ) : oscMonomialNorm s = ∏ j : OscMode M, (oscWeight j ^ s j * (s j).factorial) := by
      unfold oscMonomialNorm
      rw [Finsupp.prod_fintype (h := fun _ => by simp)]
    rw [hprod, hprod]
    have ht : (∏ j ∈ Finset.univ.erase p, oscWeight j ^ ((r + Finsupp.single p 1 : OscMode M →₀ ℕ) j) * (((r + Finsupp.single p 1 : OscMode M →₀ ℕ) j)).factorial) =
        ∏ j ∈ Finset.univ.erase p, oscWeight j ^ r j * (r j).factorial := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [Finsupp.add_apply, (Finset.mem_erase.mp hj).1]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p), ← Finset.mul_prod_erase Finset.univ (fun j => oscWeight j ^ r j * (r j).factorial) (Finset.mem_univ p), ht]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, pow_succ, Nat.factorial_succ]
    ring
  have creation_monomial (r : OscMode M →₀ ℕ) :
      oscCreation M p (MvPolynomial.monomial r 1) = MvPolynomial.monomial (r + Finsupp.single p 1) (1 : ℂ) := by
    simp [oscCreation, LinearMap.mulLeft_apply, MvPolynomial.X, MvPolynomial.monomial_mul_monomial, add_comm]
  have annihilation_monomial (s : OscMode M →₀ ℕ) :
      oscAnnihilation M p (MvPolynomial.monomial s 1) = ((oscWeight p * s p : ℕ) : ℂ) • MvPolynomial.monomial (s - Finsupp.single p 1) (1 : ℂ) := by
    simp [oscAnnihilation, MvPolynomial.pderiv_monomial, MvPolynomial.smul_monomial, Nat.cast_mul]
  have on_basis (r s : OscMode M →₀ ℕ) : oscPairing M (oscCreation M p (MvPolynomial.monomial r 1)) (MvPolynomial.monomial s 1) =
      oscPairing M (MvPolynomial.monomial r 1) (oscAnnihilation M p (MvPolynomial.monomial s 1)) := by
    rw [creation_monomial, annihilation_monomial, pairing_smul_right, oscPairing_monomial, oscPairing_monomial]
    by_cases hs : s p = 0
    · have hn : r + Finsupp.single p 1 ≠ s := by
        intro he
        have := congrArg (fun v : OscMode M →₀ ℕ => v p) he
        simp [hs] at this
      simp [hs, hn]
    · have er : s - Finsupp.single p 1 = r ↔ s = r + Finsupp.single p 1 := by
        constructor
        · intro he
          rw [← he]
          ext j
          by_cases hj : j = p
          · subst j; simp; omega
          · simp [hj]
        · intro he; rw [he]; simp
      by_cases he : s = r + Finsupp.single p 1
      · subst s
        simp only [Finsupp.add_apply, Finsupp.single_eq_same, add_tsub_cancel_right, ite_true]
        rw [norm_step]
        push_cast
        ring
      · have hn : r ≠ s - Finsupp.single p 1 := by intro hh; exact he (er.mp hh.symm)
        simp [Ne.symm he, hn]
  induction x using MvPolynomial.induction_on' with
  | monomial r a =>
    have he : MvPolynomial.monomial r a = a • MvPolynomial.monomial r 1 := by simp [MvPolynomial.smul_monomial]
    rw [he, map_smul, pairing_smul_left, pairing_smul_left]
    congr 1
    induction y using MvPolynomial.induction_on' with
    | monomial s b =>
      have hs : MvPolynomial.monomial s b = b • MvPolynomial.monomial s 1 := by simp [MvPolynomial.smul_monomial]
      rw [hs, map_smul, pairing_smul_right, pairing_smul_right, on_basis]
    | add y1 y2 hy1 hy2 => simp [pairing_add_right, hy1, hy2]
  | add x1 x2 hx1 hx2 => simp [pairing_add_left, hx1, hx2]

theorem osc_ccr (M : ℕ) (p q : OscMode M) :
    Bosonize.A02.commutator (oscAnnihilation M p) (oscCreation M q) =
      if p = q then (oscWeight p : ℂ) • (1 : Module.End ℂ (OscPoly M)) else 0 := by
  classical
  ext x
  by_cases h : p = q
  · subst q
    simp [Bosonize.A02.commutator, oscAnnihilation, oscCreation, Module.End.mul_apply, smul_add, smul_eq_mul]
  · simp [Bosonize.A02.commutator, oscAnnihilation, oscCreation, Module.End.mul_apply, MvPolynomial.pderiv_X_of_ne (Ne.symm h), h, smul_eq_mul]

theorem osc_annihilators_commute (M : ℕ) (p q : OscMode M) :
    Bosonize.A02.commutator (oscAnnihilation M p) (oscAnnihilation M q) = 0 := by
  have hc (x : OscPoly M) : MvPolynomial.pderiv p (MvPolynomial.pderiv q x) = MvPolynomial.pderiv q (MvPolynomial.pderiv p x) := by
    induction x using MvPolynomial.induction_on with
    | C a => simp
    | add x y hx hy => simp [hx, hy]
    | mul_X x k hx =>
      by_cases hi : k = p <;> by_cases hj : k = q <;>
        simp_all [MvPolynomial.pderiv_X] <;> ring
  apply LinearMap.ext
  intro x
  change (oscWeight p : ℂ) • MvPolynomial.pderiv p ((oscWeight q : ℂ) • MvPolynomial.pderiv q x) -
    (oscWeight q : ℂ) • MvPolynomial.pderiv q ((oscWeight p : ℂ) • MvPolynomial.pderiv p x) = 0
  simp only [Derivation.map_smul, smul_smul]
  rw [hc]
  simp [mul_comm]

theorem osc_creators_commute (M : ℕ) (p q : OscMode M) :
    Bosonize.A02.commutator (oscCreation M p) (oscCreation M q) = 0 := by
  ext x
  simp [Bosonize.A02.commutator, oscCreation, Module.End.mul_apply, mul_left_comm]

theorem oscAnnihilation_one (M : ℕ) (p : OscMode M) :
    oscAnnihilation M p 1 = 0 := by
  simp [oscAnnihilation]

theorem omega0_eq_pairing (M : ℕ) (a : OscAlgebra M) :
    omega0 M a = oscPairing M 1 (oscRep M a 1) := by
  simp [omega0, oscPairing, oscMonomialNorm]

theorem omega0_one (M : ℕ) :
    omega0 M 1 = 1 := by
  simp [omega0]

theorem omega0_gramSum (M : ℕ) {n : ℕ} (w : Fin n → OscWord M) (z : Fin n → ℂ) :
    (gramSum M (omega0 M) w z).im = 0 ∧ 0 ≤ (gramSum M (omega0 M) w z).re := by
  classical
  have pairing_add_right (p q r : OscPoly M) : oscPairing M p (q + r) = oscPairing M p q + oscPairing M p r := by
    simp only [oscPairing, map_add, mul_add, Finset.sum_add_distrib]
  have pairing_smul_right (a : ℂ) (p q : OscPoly M) : oscPairing M p (a • q) = a * oscPairing M p q := by
    simp only [oscPairing, map_smul, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have pairing_add_left (p q r : OscPoly M) : oscPairing M (p + q) r = oscPairing M p r + oscPairing M q r := by
    rw [← star_star (oscPairing M (p + q) r), oscPairing_conj, pairing_add_right, star_add,
        oscPairing_conj, oscPairing_conj]
  have pairing_smul_left (a : ℂ) (p q : OscPoly M) : oscPairing M (a • p) q = star a * oscPairing M p q := by
    rw [← oscPairing_conj, pairing_smul_right, star_mul, oscPairing_conj, mul_comm]
  have gen_adjoint (g : OscGen M) (x y : OscPoly M) :
      oscPairing M (oscRep M (FreeAlgebra.ι ℂ g) x) y =
        oscPairing M x (oscRep M (FreeAlgebra.ι ℂ (!g.1, g.2)) y) := by
    rcases g with ⟨b, p⟩
    cases b with
    | true =>
      dsimp [oscRep]
      rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
      dsimp
      exact oscCreation_pairing_adjoint M p x y
    | false =>
      dsimp [oscRep]
      rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
      dsimp
      have h1 := oscPairing_conj M (oscAnnihilation M p x) y
      have h2 := oscCreation_pairing_adjoint M p y x
      have h3 := oscPairing_conj M (oscCreation M p y) x
      rw [← star_star (oscPairing M (oscAnnihilation M p x) y), h1, ← h2, h3]
  have wordElement_append (l1 l2 : List (OscGen M)) :
      wordElement M (l1 ++ l2) = wordElement M l1 * wordElement M l2 := by
    dsimp [wordElement]
    rw [List.map_append, List.prod_append]
  have word_adjoint (ws : OscWord M) (x y : OscPoly M) :
      oscPairing M (oscRep M (wordElement M ws) x) y =
        oscPairing M x (oscRep M (wordElement M (wordDagger ws)) y) := by
    induction ws generalizing x y with
    | nil =>
      simp [wordElement, wordDagger]
    | cons g ws ih =>
      have heq : wordElement M (g :: ws) = FreeAlgebra.ι ℂ g * wordElement M ws := by
        simp [wordElement]
      have hdag : wordDagger (g :: ws) = wordDagger ws ++ [(!g.1, g.2)] := by
        simp [wordDagger]
      rw [heq, map_mul, Module.End.mul_apply, gen_adjoint, ih, hdag, wordElement_append]
      simp [wordElement]
  have eval_pair (i j : Fin n) :
      omega0 M (wordElement M (wordDagger (w i)) * wordElement M (w j)) =
        oscPairing M (oscRep M (wordElement M (w i)) 1) (oscRep M (wordElement M (w j)) 1) := by
    rw [omega0_eq_pairing, map_mul, Module.End.mul_apply]
    exact (word_adjoint (w i) 1 (oscRep M (wordElement M (w j)) 1)).symm
  have sum_right (p : OscPoly M) (s : Finset (Fin n)) (f : Fin n → OscPoly M) :
      oscPairing M p (∑ j ∈ s, f j) = ∑ j ∈ s, oscPairing M p (f j) := by
    induction s using Finset.induction with
    | empty => simp [oscPairing]
    | @insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has, pairing_add_right, ih]
  have sum_left (s : Finset (Fin n)) (f : Fin n → OscPoly M) (q : OscPoly M) :
      oscPairing M (∑ i ∈ s, f i) q = ∑ i ∈ s, oscPairing M (f i) q := by
    induction s using Finset.induction with
    | empty => simp [oscPairing]
    | @insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has, pairing_add_left, ih]
  let V (i : Fin n) : OscPoly M := oscRep M (wordElement M (w i)) 1
  let P : OscPoly M := ∑ i, z i • V i
  have hgram : gramSum M (omega0 M) w z = oscPairing M P P := by
    unfold gramSum
    simp_rw [eval_pair]
    change ∑ i, ∑ j, star (z i) * z j * oscPairing M (V i) (V j) = oscPairing M P P
    dsimp [P]
    rw [sum_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [sum_right]
    apply Finset.sum_congr rfl
    intro j _
    rw [pairing_smul_left, pairing_smul_right]
    change star (z i) * z j * oscPairing M (V i) (V j) = star (z i) * (z j * oscPairing M (V i) (V j))
    ring
  rw [hgram]
  have hstar : star (oscPairing M P P) = oscPairing M P P := oscPairing_conj M P P
  have him : (oscPairing M P P).im = 0 := by
    have hcc : (star (oscPairing M P P)).im = - (oscPairing M P P).im := Complex.conj_im (oscPairing M P P)
    rw [hstar] at hcc
    linarith
  exact ⟨him, oscPairing_self_nonneg M P⟩

theorem omega0_ccr_descends (M : ℕ) (a b : OscAlgebra M) (p q : OscMode M) :
    omega0 M (a * (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (true, q) -
      FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (false, p) -
      (if p = q then (oscWeight p : ℂ) else 0) • 1) * b) = 0 := by
  have hR : oscRep M (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (true, q) -
      FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (false, p) -
      (if p = q then (oscWeight p : ℂ) else 0) • 1) = 0 := by
    simp only [map_sub, map_mul, map_smul, map_one]
    have hccr := osc_ccr M p q
    dsimp [Bosonize.A02.commutator] at hccr
    dsimp [oscRep]
    rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
    dsimp
    rw [hccr]
    split_ifs <;> simp
  have hab : oscRep M (a * (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (true, q) -
      FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (false, p) -
      (if p = q then (oscWeight p : ℂ) else 0) • 1) * b) = 0 := by
    rw [map_mul, map_mul, hR, mul_zero, zero_mul]
  change (MvPolynomial.lcoeff ℂ 0) ((oscRep M (a * (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (true, q) -
      FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (false, p) -
      (if p = q then (oscWeight p : ℂ) else 0) • 1) * b)) 1) = 0
  rw [hab]
  simp

theorem omega0_ccr_descends_aa (M : ℕ) (a b : OscAlgebra M) (p q : OscMode M) :
    omega0 M (a * (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (false, q) -
      FreeAlgebra.ι ℂ (false, q) * FreeAlgebra.ι ℂ (false, p)) * b) = 0 := by
  have hR : oscRep M (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (false, q) -
      FreeAlgebra.ι ℂ (false, q) * FreeAlgebra.ι ℂ (false, p)) = 0 := by
    simp only [map_sub, map_mul]
    have hcomm := osc_annihilators_commute M p q
    dsimp [Bosonize.A02.commutator] at hcomm
    dsimp [oscRep]
    simp only [FreeAlgebra.lift_ι_apply]
    dsimp
    exact hcomm
  have hab : oscRep M (a * (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (false, q) -
      FreeAlgebra.ι ℂ (false, q) * FreeAlgebra.ι ℂ (false, p)) * b) = 0 := by
    rw [map_mul, map_mul, hR, mul_zero, zero_mul]
  change (MvPolynomial.lcoeff ℂ 0) ((oscRep M (a * (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (false, q) -
      FreeAlgebra.ι ℂ (false, q) * FreeAlgebra.ι ℂ (false, p)) * b)) 1) = 0
  rw [hab]
  simp

theorem omega0_ccr_descends_cc (M : ℕ) (a b : OscAlgebra M) (p q : OscMode M) :
    omega0 M (a * (FreeAlgebra.ι ℂ (true, p) * FreeAlgebra.ι ℂ (true, q) -
      FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (true, p)) * b) = 0 := by
  have hR : oscRep M (FreeAlgebra.ι ℂ (true, p) * FreeAlgebra.ι ℂ (true, q) -
      FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (true, p)) = 0 := by
    simp only [map_sub, map_mul]
    have hcomm := osc_creators_commute M p q
    dsimp [Bosonize.A02.commutator] at hcomm
    dsimp [oscRep]
    simp only [FreeAlgebra.lift_ι_apply]
    dsimp
    exact hcomm
  have hab : oscRep M (a * (FreeAlgebra.ι ℂ (true, p) * FreeAlgebra.ι ℂ (true, q) -
      FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (true, p)) * b) = 0 := by
    rw [map_mul, map_mul, hR, mul_zero, zero_mul]
  change (MvPolynomial.lcoeff ℂ 0) ((oscRep M (a * (FreeAlgebra.ι ℂ (true, p) * FreeAlgebra.ι ℂ (true, q) -
      FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (true, p)) * b)) 1) = 0
  rw [hab]
  simp

theorem bogoliubovMap_inverse (M : ℕ) (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) :
    (bogoliubovMap M c s).comp (bogoliubovMap M c (-s)) = AlgHom.id ℂ (OscAlgebra M) := by
  have hcsC : (c : ℂ) ^ 2 - (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  apply FreeAlgebra.hom_ext
  ext ⟨b, ν, i⟩
  cases ν <;> cases b
  all_goals {
    simp only [Function.comp_apply, AlgHom.coe_comp, AlgHom.coe_id, id_eq,
      bogoliubovMap, FreeAlgebra.lift_ι_apply, map_add, map_smul,
      Bool.not_false, Bool.not_true, smul_add, smul_smul]
    dsimp [Bosonize.A07Interactions.oppositeOrientation]
    push_cast
    set X := FreeAlgebra.ι ℂ _
    set Y := FreeAlgebra.ι ℂ _
    have hX : ((c : ℂ) * (c : ℂ)) • X + ((-s : ℂ) * (s : ℂ)) • X = X := by
      rw [← add_smul]
      have : (c : ℂ) * (c : ℂ) + (-s : ℂ) * (s : ℂ) = 1 := by
        linear_combination hcsC
      rw [this, one_smul]
    have hY : ((c : ℂ) * (s : ℂ)) • Y + ((-s : ℂ) * (c : ℂ)) • Y = 0 := by
      rw [← add_smul]
      have : (c : ℂ) * (s : ℂ) + (-s : ℂ) * (c : ℂ) = 0 := by ring
      rw [this, zero_smul]
    have h_rearr : ((c : ℂ) * (c : ℂ)) • X + ((c : ℂ) * (s : ℂ)) • Y +
        (((-s : ℂ) * (c : ℂ)) • Y + ((-s : ℂ) * (s : ℂ)) • X) =
        (((c : ℂ) * (c : ℂ)) • X + ((-s : ℂ) * (s : ℂ)) • X) +
        (((c : ℂ) * (s : ℂ)) • Y + ((-s : ℂ) * (c : ℂ)) • Y) := by abel
    rw [h_rearr, hX, hY, add_zero]
  }

theorem bogoliubovMap_inverse_rev (M : ℕ) (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) :
    (bogoliubovMap M c (-s)).comp (bogoliubovMap M c s) = AlgHom.id ℂ (OscAlgebra M) := by
  have h : c ^ 2 - (-s) ^ 2 = 1 := by
    linarith
  have hinv := bogoliubovMap_inverse M c (-s) h
  rw [neg_neg] at hinv
  exact hinv

theorem bogoliubovMap_inverse_iff (M : ℕ) [NeZero M] (c s : ℝ) :
    (bogoliubovMap M c s).comp (bogoliubovMap M c (-s)) = AlgHom.id ℂ (OscAlgebra M) ↔
      c ^ 2 - s ^ 2 = 1 := by
  constructor
  · intro h
    let i0 : Fin M := ⟨0, NeZero.pos M⟩
    let ev : OscAlgebra M →ₐ[ℂ] ℂ :=
      FreeAlgebra.lift ℂ (fun g => if g = (false, A06.Orientation.right, i0) then (1 : ℂ) else 0)
    have heq := congr_arg (fun (F : OscAlgebra M →ₐ[ℂ] OscAlgebra M) =>
      ev (F (FreeAlgebra.ι ℂ (false, A06.Orientation.right, i0)))) h
    simp only [AlgHom.id_apply] at heq
    have hev_g0 : ev (FreeAlgebra.ι ℂ (false, A06.Orientation.right, i0)) = 1 := by
      simp [ev]
    have hev_g1 : ev (FreeAlgebra.ι ℂ (true, A06.Orientation.left, i0)) = 0 := by
      simp [ev]
    simp only [AlgHom.comp_apply, bogoliubovMap, FreeAlgebra.lift_ι_apply, map_add, map_smul] at heq
    dsimp [Bosonize.A07Interactions.oppositeOrientation] at heq
    have hnot1 : (!false) = true := rfl
    have hnot2 : (!true) = false := rfl
    rw [hnot1, hnot2] at heq
    rw [hev_g0, hev_g1] at heq
    simp only [mul_one, mul_zero, add_zero] at heq
    push_cast at heq
    have h_real : ((c ^ 2 - s ^ 2 : ℝ) : ℂ) = (1 : ℂ) := by
      calc ((c ^ 2 - s ^ 2 : ℝ) : ℂ) = (c : ℂ) * (c : ℂ) + (-s : ℂ) * (s : ℂ) := by
            push_cast; ring
      _ = (1 : ℂ) := by linear_combination heq
    exact_mod_cast h_real
  · intro hcs
    exact bogoliubovMap_inverse M c s hcs

theorem bogoliubovMap_word_adjoint (M : ℕ) (c s : ℝ) (w : OscWord M) (x y : OscPoly M) :
    oscPairing M x (oscRep M (bogoliubovMap M c s (wordElement M (wordDagger w))) y) =
      oscPairing M (oscRep M (bogoliubovMap M c s (wordElement M w)) x) y := by
  have pairing_add_right (p q r : OscPoly M) : oscPairing M p (q + r) = oscPairing M p q + oscPairing M p r := by
    simp only [oscPairing, map_add, mul_add, Finset.sum_add_distrib]
  have pairing_smul_right (a : ℂ) (p q : OscPoly M) : oscPairing M p (a • q) = a * oscPairing M p q := by
    simp only [oscPairing, map_smul, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have pairing_add_left (p q r : OscPoly M) : oscPairing M (p + q) r = oscPairing M p r + oscPairing M q r := by
    rw [← star_star (oscPairing M (p + q) r), oscPairing_conj, pairing_add_right, star_add,
        oscPairing_conj, oscPairing_conj]
  have pairing_smul_left (a : ℂ) (p q : OscPoly M) : oscPairing M (a • p) q = star a * oscPairing M p q := by
    rw [← oscPairing_conj, pairing_smul_right, star_mul, oscPairing_conj, mul_comm]
  have gen_adjoint (g : OscGen M) (u v : OscPoly M) :
      oscPairing M (oscRep M (FreeAlgebra.ι ℂ g) u) v =
        oscPairing M u (oscRep M (FreeAlgebra.ι ℂ (!g.1, g.2)) v) := by
    rcases g with ⟨b, p⟩
    cases b with
    | true =>
      dsimp [oscRep]
      rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
      dsimp
      exact oscCreation_pairing_adjoint M p u v
    | false =>
      dsimp [oscRep]
      rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
      dsimp
      have h1 := oscPairing_conj M (oscAnnihilation M p u) v
      have h2 := oscCreation_pairing_adjoint M p v u
      have h3 := oscPairing_conj M (oscCreation M p v) u
      rw [← star_star (oscPairing M (oscAnnihilation M p u) v), h1, ← h2, h3]
  have bogo_gen_adjoint (g : OscGen M) (u v : OscPoly M) :
      oscPairing M (oscRep M (bogoliubovMap M c s (FreeAlgebra.ι ℂ g)) u) v =
        oscPairing M u (oscRep M (bogoliubovMap M c s (FreeAlgebra.ι ℂ (!g.1, g.2))) v) := by
    have hsmul (k : ℂ) (z : OscAlgebra M) : oscRep M (k • z) = k • oscRep M z := map_smul (oscRep M) k z
    have hrep_g (k : OscGen M) :
        oscRep M (bogoliubovMap M c s (FreeAlgebra.ι ℂ k)) =
          (c : ℂ) • oscRep M (FreeAlgebra.ι ℂ k) +
          (s : ℂ) • oscRep M (FreeAlgebra.ι ℂ (!k.1, (Bosonize.A07Interactions.oppositeOrientation k.2.1, k.2.2))) := by
      dsimp [bogoliubovMap]
      rw [FreeAlgebra.lift_ι_apply, ← Complex.coe_smul c, ← Complex.coe_smul s, map_add, hsmul, hsmul]
    rw [hrep_g g]
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
    rw [pairing_add_left, pairing_smul_left, pairing_smul_left]
    have hc_star : star (c : ℂ) = (c : ℂ) := Complex.conj_ofReal c
    have hs_star : star (s : ℂ) = (s : ℂ) := Complex.conj_ofReal s
    rw [hc_star, hs_star]
    have h1 := gen_adjoint g u v
    have h2 := gen_adjoint (!g.1, (Bosonize.A07Interactions.oppositeOrientation g.2.1, g.2.2)) u v
    dsimp at h2
    simp only [Bool.not_not] at h2
    rw [h1, h2]
    rw [hrep_g (!g.1, g.2)]
    simp only [Bool.not_not]
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
    rw [pairing_add_right, pairing_smul_right, pairing_smul_right]
  have wordElement_append (l1 l2 : List (OscGen M)) :
      wordElement M (l1 ++ l2) = wordElement M l1 * wordElement M l2 := by
    dsimp [wordElement]
    rw [List.map_append, List.prod_append]
  induction w generalizing x y with
  | nil =>
    simp [wordElement, wordDagger]
  | cons g ws ih =>
    have heq : wordElement M (g :: ws) = FreeAlgebra.ι ℂ g * wordElement M ws := by
      simp [wordElement]
    have hdag : wordDagger (g :: ws) = wordDagger ws ++ [(!g.1, g.2)] := by
      simp [wordDagger]
    rw [heq, hdag, wordElement_append]
    simp only [map_mul, Module.End.mul_apply]
    have ih_app := ih x (oscRep M (bogoliubovMap M c s (wordElement M [(!g.1, g.2)])) y)
    rw [ih_app]
    have hsingle : wordElement M [(!g.1, g.2)] = FreeAlgebra.ι ℂ (!g.1, g.2) := by
      simp [wordElement]
    rw [hsingle]
    exact (bogo_gen_adjoint g (oscRep M (bogoliubovMap M c s (wordElement M ws)) x) y).symm

theorem omegaP_one (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) :
    omegaP M hp 1 = 1 := by
  simp [omegaP, map_one, omega0_one]

theorem omegaP_gramSum (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) {n : ℕ}
    (w : Fin n → OscWord M) (z : Fin n → ℂ) :
    (gramSum M (omegaP M hp) w z).im = 0 ∧ 0 ≤ (gramSum M (omegaP M hp) w z).re := by
  classical
  have pairing_add_right (p q r : OscPoly M) : oscPairing M p (q + r) = oscPairing M p q + oscPairing M p r := by
    simp only [oscPairing, map_add, mul_add, Finset.sum_add_distrib]
  have pairing_smul_right (a : ℂ) (p q : OscPoly M) : oscPairing M p (a • q) = a * oscPairing M p q := by
    simp only [oscPairing, map_smul, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have pairing_add_left (p q r : OscPoly M) : oscPairing M (p + q) r = oscPairing M p r + oscPairing M q r := by
    rw [← star_star (oscPairing M (p + q) r), oscPairing_conj, pairing_add_right, star_add,
        oscPairing_conj, oscPairing_conj]
  have pairing_smul_left (a : ℂ) (p q : OscPoly M) : oscPairing M (a • p) q = star a * oscPairing M p q := by
    rw [← oscPairing_conj, pairing_smul_right, star_mul, oscPairing_conj, mul_comm]
  have eval_pair (i j : Fin n) :
      omegaP M hp (wordElement M (wordDagger (w i)) * wordElement M (w j)) =
        oscPairing M (oscRep M (bogoliubovMap M hp.c (-hp.s) (wordElement M (w i))) 1)
                     (oscRep M (bogoliubovMap M hp.c (-hp.s) (wordElement M (w j))) 1) := by
    dsimp [omegaP]
    rw [map_mul, omega0_eq_pairing, map_mul, Module.End.mul_apply]
    exact bogoliubovMap_word_adjoint M hp.c (-hp.s) (w i) 1
      (oscRep M (bogoliubovMap M hp.c (-hp.s) (wordElement M (w j))) 1)
  have sum_right (p : OscPoly M) (s : Finset (Fin n)) (f : Fin n → OscPoly M) :
      oscPairing M p (∑ j ∈ s, f j) = ∑ j ∈ s, oscPairing M p (f j) := by
    induction s using Finset.induction with
    | empty => simp [oscPairing]
    | @insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has, pairing_add_right, ih]
  have sum_left (s : Finset (Fin n)) (f : Fin n → OscPoly M) (q : OscPoly M) :
      oscPairing M (∑ i ∈ s, f i) q = ∑ i ∈ s, oscPairing M (f i) q := by
    induction s using Finset.induction with
    | empty => simp [oscPairing]
    | @insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has, pairing_add_left, ih]
  let V (i : Fin n) : OscPoly M := oscRep M (bogoliubovMap M hp.c (-hp.s) (wordElement M (w i))) 1
  let P : OscPoly M := ∑ i, z i • V i
  have hgram : gramSum M (omegaP M hp) w z = oscPairing M P P := by
    unfold gramSum
    simp_rw [eval_pair]
    change ∑ i, ∑ j, star (z i) * z j * oscPairing M (V i) (V j) = oscPairing M P P
    dsimp [P]
    rw [sum_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [sum_right]
    apply Finset.sum_congr rfl
    intro j _
    rw [pairing_smul_left, pairing_smul_right]
    change star (z i) * z j * oscPairing M (V i) (V j) = star (z i) * (z j * oscPairing M (V i) (V j))
    ring
  rw [hgram]
  have hstar : star (oscPairing M P P) = oscPairing M P P := oscPairing_conj M P P
  have him : (oscPairing M P P).im = 0 := by
    have hcc : (star (oscPairing M P P)).im = - (oscPairing M P P).im := Complex.conj_im (oscPairing M P P)
    rw [hstar] at hcc
    linarith
  exact ⟨him, oscPairing_self_nonneg M P⟩

theorem omegaP_ccr_descends (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (a b : OscAlgebra M) (p q : OscMode M) :
    omegaP M hp (a * (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (true, q) -
      FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (false, p) -
      (if p = q then (oscWeight p : ℂ) else 0) • 1) * b) = 0 := by
  have hcsC : (hp.c : ℂ) ^ 2 - (hp.s : ℂ) ^ 2 = 1 := by exact_mod_cast hp.hyperbolic_id
  have hrep_ann (k : OscMode M) :
      oscRep M (bogoliubovMap M hp.c (-hp.s) (FreeAlgebra.ι ℂ (false, k))) =
        (hp.c : ℂ) • oscAnnihilation M k +
        (-hp.s : ℂ) • oscCreation M (Bosonize.A07Interactions.oppositeOrientation k.1, k.2) := by
    dsimp [bogoliubovMap, oscRep]
    rw [FreeAlgebra.lift_ι_apply]
    rw [← Complex.coe_smul hp.c, ← Complex.coe_smul (-hp.s)]
    simp only [map_add, map_smul, FreeAlgebra.lift_ι_apply, Bool.not_false]
    push_cast
    rfl
  have hrep_cre (k : OscMode M) :
      oscRep M (bogoliubovMap M hp.c (-hp.s) (FreeAlgebra.ι ℂ (true, k))) =
        (hp.c : ℂ) • oscCreation M k +
        (-hp.s : ℂ) • oscAnnihilation M (Bosonize.A07Interactions.oppositeOrientation k.1, k.2) := by
    dsimp [bogoliubovMap, oscRep]
    rw [FreeAlgebra.lift_ι_apply, ← Complex.coe_smul hp.c, ← Complex.coe_smul (-hp.s)]
    simp only [map_add, map_smul, FreeAlgebra.lift_ι_apply, Bool.not_true]
    push_cast
    rfl
  have hcomm (A B C D : Module.End ℂ (OscPoly M)) (c s : ℂ) :
      (c • A + s • B) * (c • C + s • D) - (c • C + s • D) * (c • A + s • B) =
        (c * c) • Bosonize.A02.commutator A C +
        (c * s) • Bosonize.A02.commutator A D +
        (s * c) • Bosonize.A02.commutator B C +
        (s * s) • Bosonize.A02.commutator B D := by
    dsimp [Bosonize.A02.commutator]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
    rw [mul_comm s c]
    abel
  have hcomm_BD : Bosonize.A02.commutator
      (oscCreation M (Bosonize.A07Interactions.oppositeOrientation p.1, p.2))
      (oscAnnihilation M (Bosonize.A07Interactions.oppositeOrientation q.1, q.2)) =
      - if p = q then (oscWeight p : ℂ) • (1 : Module.End ℂ (OscPoly M)) else 0 := by
    have hanti : Bosonize.A02.commutator
        (oscCreation M (Bosonize.A07Interactions.oppositeOrientation p.1, p.2))
        (oscAnnihilation M (Bosonize.A07Interactions.oppositeOrientation q.1, q.2)) =
        - Bosonize.A02.commutator
        (oscAnnihilation M (Bosonize.A07Interactions.oppositeOrientation q.1, q.2))
        (oscCreation M (Bosonize.A07Interactions.oppositeOrientation p.1, p.2)) := by
      dsimp [Bosonize.A02.commutator]
      abel
    rw [hanti, osc_ccr]
    by_cases hpq : p = q
    · subst hpq
      dsimp [Bosonize.A07Interactions.oppositeOrientation, oscWeight]
      simp
    · have h_opp : ¬ (Bosonize.A07Interactions.oppositeOrientation q.1, q.2) =
                      (Bosonize.A07Interactions.oppositeOrientation p.1, p.2) := by
        intro h
        have h1 := congrArg (fun x : OscMode M => x.1) h
        have h2 := congrArg (fun x : OscMode M => x.2) h
        dsimp at h1 h2
        have h1' : p.1 = q.1 := by
          cases hp1 : p.1 <;> cases hq1 : q.1
          · rfl
          · exfalso
            have h1_cases := h1
            rw [hp1, hq1] at h1_cases
            dsimp [Bosonize.A07Interactions.oppositeOrientation] at h1_cases
            cases h1_cases
          · exfalso
            have h1_cases := h1
            rw [hp1, hq1] at h1_cases
            dsimp [Bosonize.A07Interactions.oppositeOrientation] at h1_cases
            cases h1_cases
          · rfl
        exact hpq (Prod.ext h1' h2.symm)
      simp [hpq, h_opp]
  have hR : oscRep M (bogoliubovMap M hp.c (-hp.s)
      (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (true, q) -
       FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (false, p) -
       (if p = q then (oscWeight p : ℂ) else 0) • 1)) = 0 := by
    simp only [map_sub, map_mul, map_smul, map_one, hrep_ann, hrep_cre]
    rw [hcomm (oscAnnihilation M p)
              (oscCreation M (Bosonize.A07Interactions.oppositeOrientation p.1, p.2))
              (oscCreation M q)
              (oscAnnihilation M (Bosonize.A07Interactions.oppositeOrientation q.1, q.2))]
    rw [osc_ccr, osc_annihilators_commute, osc_creators_commute, hcomm_BD]
    simp only [smul_zero, add_zero, smul_neg]
    by_cases hpq : p = q
    · subst hpq
      simp only [ite_true]
      rw [← sub_eq_add_neg]
      have : ((hp.c : ℂ) * (hp.c : ℂ)) • ((oscWeight p : ℂ) • (1 : Module.End ℂ (OscPoly M))) -
             ((-hp.s : ℂ) * (-hp.s : ℂ)) • ((oscWeight p : ℂ) • (1 : Module.End ℂ (OscPoly M))) -
             (oscWeight p : ℂ) • (1 : Module.End ℂ (OscPoly M)) = 0 := by
        rw [smul_smul, smul_smul]
        have hring : (hp.c : ℂ) * (hp.c : ℂ) * (oscWeight p : ℂ) -
                     (-hp.s : ℂ) * (-hp.s : ℂ) * (oscWeight p : ℂ) -
                     (oscWeight p : ℂ) = 0 := by
          linear_combination (oscWeight p : ℂ) * hcsC
        rw [← sub_smul, ← sub_smul, hring, zero_smul]
      exact this
    · simp [hpq]
  dsimp [omegaP, omega0]
  have hab : oscRep M (bogoliubovMap M hp.c (-hp.s)
      (a * (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (true, q) -
       FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (false, p) -
       (if p = q then (oscWeight p : ℂ) else 0) • 1) * b)) = 0 := by
    simp only [map_mul, hR, mul_zero, zero_mul]
  change (MvPolynomial.lcoeff ℂ 0) ((oscRep M (bogoliubovMap M hp.c (-hp.s)
      (a * (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (true, q) -
       FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (false, p) -
       (if p = q then (oscWeight p : ℂ) else 0) • 1) * b))) 1) = 0
  rw [hab]
  simp

theorem omegaP_ccr_descends_aa (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (a b : OscAlgebra M) (p q : OscMode M) :
    omegaP M hp (a * (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (false, q) -
      FreeAlgebra.ι ℂ (false, q) * FreeAlgebra.ι ℂ (false, p)) * b) = 0 := by
  have hrep_ann (k : OscMode M) :
      oscRep M (bogoliubovMap M hp.c (-hp.s) (FreeAlgebra.ι ℂ (false, k))) =
        (hp.c : ℂ) • oscAnnihilation M k +
        (-hp.s : ℂ) • oscCreation M (Bosonize.A07Interactions.oppositeOrientation k.1, k.2) := by
    dsimp [bogoliubovMap, oscRep]
    rw [FreeAlgebra.lift_ι_apply]
    rw [← Complex.coe_smul hp.c, ← Complex.coe_smul (-hp.s)]
    simp only [map_add, map_smul, FreeAlgebra.lift_ι_apply, Bool.not_false]
    push_cast
    rfl
  have hcomm (A B C D : Module.End ℂ (OscPoly M)) (c s : ℂ) :
      (c • A + s • B) * (c • C + s • D) - (c • C + s • D) * (c • A + s • B) =
        (c * c) • Bosonize.A02.commutator A C +
        (c * s) • Bosonize.A02.commutator A D +
        (s * c) • Bosonize.A02.commutator B C +
        (s * s) • Bosonize.A02.commutator B D := by
    dsimp [Bosonize.A02.commutator]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
    rw [mul_comm s c]
    abel
  have hanti (A B : Module.End ℂ (OscPoly M)) :
      Bosonize.A02.commutator A B = - Bosonize.A02.commutator B A := by
    dsimp [Bosonize.A02.commutator]
    abel
  have hcomm_BC :
      Bosonize.A02.commutator
        (oscCreation M (Bosonize.A07Interactions.oppositeOrientation p.1, p.2))
        (oscAnnihilation M q) =
      - if p = (Bosonize.A07Interactions.oppositeOrientation q.1, q.2) then
          (oscWeight p : ℂ) • (1 : Module.End ℂ (OscPoly M)) else 0 := by
    rw [hanti, osc_ccr]
    have hopp_opp (x : Bosonize.A06.Orientation) :
        Bosonize.A07Interactions.oppositeOrientation (Bosonize.A07Interactions.oppositeOrientation x) = x := by
      cases x <;> rfl
    rcases q with ⟨q1, q2⟩
    by_cases hpq : p = (Bosonize.A07Interactions.oppositeOrientation q1, q2)
    · subst hpq
      dsimp [oscWeight]
      have h_pair : (Bosonize.A07Interactions.oppositeOrientation
                      (Bosonize.A07Interactions.oppositeOrientation q1), q2) = (q1, q2) := by
        rw [hopp_opp]
      rw [h_pair]
      simp
    · have h_opp_iff :
          ((q1, q2) = (Bosonize.A07Interactions.oppositeOrientation p.1, p.2)) ↔
          (p = (Bosonize.A07Interactions.oppositeOrientation q1, q2)) := by
        rcases p with ⟨p1, p2⟩
        cases p1 <;> cases q1 <;> {
          dsimp [Bosonize.A07Interactions.oppositeOrientation]
          simp [eq_comm]
        }
      have hqp : ¬ (q1, q2) = (Bosonize.A07Interactions.oppositeOrientation p.1, p.2) := by
        intro h
        exact hpq (h_opp_iff.mp h)
      split_ifs with h1
      · exact False.elim (hqp h1)
      · rfl
  have hR : oscRep M (bogoliubovMap M hp.c (-hp.s)
      (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (false, q) -
       FreeAlgebra.ι ℂ (false, q) * FreeAlgebra.ι ℂ (false, p))) = 0 := by
    simp only [map_sub, map_mul, hrep_ann]
    rw [hcomm (oscAnnihilation M p)
              (oscCreation M (Bosonize.A07Interactions.oppositeOrientation p.1, p.2))
              (oscAnnihilation M q)
              (oscCreation M (Bosonize.A07Interactions.oppositeOrientation q.1, q.2))]
    rw [osc_annihilators_commute, osc_creators_commute, osc_ccr, hcomm_BC]
    simp only [smul_zero, zero_add, add_zero, smul_neg]
    by_cases hpq : p = (Bosonize.A07Interactions.oppositeOrientation q.1, q.2)
    · subst hpq
      simp only [ite_true]
      rw [smul_smul, smul_smul, ← sub_eq_add_neg, ← sub_smul]
      have : (hp.c : ℂ) * (-hp.s : ℂ) * (oscWeight (Bosonize.A07Interactions.oppositeOrientation q.1, q.2) : ℂ) -
             ((-hp.s : ℂ) * (hp.c : ℂ) * (oscWeight (Bosonize.A07Interactions.oppositeOrientation q.1, q.2) : ℂ)) = 0 := by ring
      rw [this, zero_smul]
    · simp only [hpq, ite_false, smul_zero, neg_zero, add_zero]
  dsimp [omegaP, omega0]
  have hab : oscRep M (bogoliubovMap M hp.c (-hp.s)
      (a * (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (false, q) -
       FreeAlgebra.ι ℂ (false, q) * FreeAlgebra.ι ℂ (false, p)) * b)) = 0 := by
    simp only [map_mul, hR, mul_zero, zero_mul]
  change (MvPolynomial.lcoeff ℂ 0) ((oscRep M (bogoliubovMap M hp.c (-hp.s)
      (a * (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (false, q) -
       FreeAlgebra.ι ℂ (false, q) * FreeAlgebra.ι ℂ (false, p)) * b))) 1) = 0
  rw [hab]
  simp

theorem omegaP_ccr_descends_cc (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (a b : OscAlgebra M) (p q : OscMode M) :
    omegaP M hp (a * (FreeAlgebra.ι ℂ (true, p) * FreeAlgebra.ι ℂ (true, q) -
      FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (true, p)) * b) = 0 := by
  have hrep_cre (k : OscMode M) :
      oscRep M (bogoliubovMap M hp.c (-hp.s) (FreeAlgebra.ι ℂ (true, k))) =
        (hp.c : ℂ) • oscCreation M k +
        (-hp.s : ℂ) • oscAnnihilation M (Bosonize.A07Interactions.oppositeOrientation k.1, k.2) := by
    dsimp [bogoliubovMap, oscRep]
    rw [FreeAlgebra.lift_ι_apply]
    rw [← Complex.coe_smul hp.c, ← Complex.coe_smul (-hp.s)]
    simp only [map_add, map_smul, FreeAlgebra.lift_ι_apply, Bool.not_true]
    push_cast
    rfl
  have hcomm (A B C D : Module.End ℂ (OscPoly M)) (c s : ℂ) :
      (c • A + s • B) * (c • C + s • D) - (c • C + s • D) * (c • A + s • B) =
        (c * c) • Bosonize.A02.commutator A C +
        (c * s) • Bosonize.A02.commutator A D +
        (s * c) • Bosonize.A02.commutator B C +
        (s * s) • Bosonize.A02.commutator B D := by
    dsimp [Bosonize.A02.commutator]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
    rw [mul_comm s c]
    abel
  have hanti (A B : Module.End ℂ (OscPoly M)) :
      Bosonize.A02.commutator A B = - Bosonize.A02.commutator B A := by
    dsimp [Bosonize.A02.commutator]
    abel
  have h_opp_iff :
      ((Bosonize.A07Interactions.oppositeOrientation q.1, q.2) = p) ↔
      ((Bosonize.A07Interactions.oppositeOrientation p.1, p.2) = q) := by
    rcases p with ⟨p1, p2⟩
    rcases q with ⟨q1, q2⟩
    cases p1 <;> cases q1 <;> {
      dsimp [Bosonize.A07Interactions.oppositeOrientation]
      simp [eq_comm]
    }
  have hcomm_AD :
      Bosonize.A02.commutator
        (oscCreation M p)
        (oscAnnihilation M (Bosonize.A07Interactions.oppositeOrientation q.1, q.2)) =
      - if (Bosonize.A07Interactions.oppositeOrientation p.1, p.2) = q then
          (oscWeight q : ℂ) • (1 : Module.End ℂ (OscPoly M)) else 0 := by
    rw [hanti, osc_ccr]
    by_cases hpq : (Bosonize.A07Interactions.oppositeOrientation p.1, p.2) = q
    · have hqp : (Bosonize.A07Interactions.oppositeOrientation q.1, q.2) = p := h_opp_iff.mpr hpq
      subst hpq
      dsimp [oscWeight]
      have hopp_opp (x : Bosonize.A06.Orientation) :
          Bosonize.A07Interactions.oppositeOrientation (Bosonize.A07Interactions.oppositeOrientation x) = x := by
        cases x <;> rfl
      have h_pair : (Bosonize.A07Interactions.oppositeOrientation
                      (Bosonize.A07Interactions.oppositeOrientation p.1), p.2) = p := by
        ext; exact hopp_opp p.1; rfl
      rw [h_pair]
      simp
    · have hqp : ¬ (Bosonize.A07Interactions.oppositeOrientation q.1, q.2) = p := by
        intro h
        exact hpq (h_opp_iff.mp h)
      split_ifs with h1
      · exact False.elim (hqp h1)
      · rfl
  have hR : oscRep M (bogoliubovMap M hp.c (-hp.s)
      (FreeAlgebra.ι ℂ (true, p) * FreeAlgebra.ι ℂ (true, q) -
       FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (true, p))) = 0 := by
    simp only [map_sub, map_mul, hrep_cre]
    rw [hcomm (oscCreation M p)
              (oscAnnihilation M (Bosonize.A07Interactions.oppositeOrientation p.1, p.2))
              (oscCreation M q)
              (oscAnnihilation M (Bosonize.A07Interactions.oppositeOrientation q.1, q.2))]
    rw [osc_creators_commute, osc_annihilators_commute, osc_ccr, hcomm_AD]
    simp only [smul_zero, zero_add, add_zero, smul_neg]
    by_cases hpq : (Bosonize.A07Interactions.oppositeOrientation p.1, p.2) = q
    · subst hpq
      simp only [ite_true]
      rw [smul_smul, smul_smul, ← neg_smul, ← add_smul]
      have : - ((hp.c : ℂ) * (-hp.s : ℂ) * (oscWeight (Bosonize.A07Interactions.oppositeOrientation p.1, p.2) : ℂ)) +
             ((-hp.s : ℂ) * (hp.c : ℂ) * (oscWeight (Bosonize.A07Interactions.oppositeOrientation p.1, p.2) : ℂ)) = 0 := by ring
      rw [this, zero_smul]
    · simp only [hpq, ite_false, smul_zero, neg_zero, add_zero]
  dsimp [omegaP, omega0]
  have hab : oscRep M (bogoliubovMap M hp.c (-hp.s)
      (a * (FreeAlgebra.ι ℂ (true, p) * FreeAlgebra.ι ℂ (true, q) -
       FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (true, p)) * b)) = 0 := by
    simp only [map_mul, hR, mul_zero, zero_mul]
  change (MvPolynomial.lcoeff ℂ 0) ((oscRep M (bogoliubovMap M hp.c (-hp.s)
      (a * (FreeAlgebra.ι ℂ (true, p) * FreeAlgebra.ι ℂ (true, q) -
       FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (true, p)) * b))) 1) = 0
  rw [hab]
  simp

theorem omegaP_comp_bogoliubovMap (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) :
    (omegaP M hp).comp (bogoliubovMap M hp.c hp.s).toLinearMap = omega0 M := by
  dsimp [omegaP]
  ext a
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  have hinv : bogoliubovMap M hp.c (-hp.s) (bogoliubovMap M hp.c hp.s a) = a := by
    have := congr_arg (fun F => F a) (bogoliubovMap_inverse_rev M hp.c hp.s hp.hyperbolic_id)
    simpa using this
  rw [hinv]

theorem omegaP_mul_dressed_annihilator (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (a : OscAlgebra M) (ν : Bosonize.A06.Orientation) (i : Fin M) :
    omegaP M hp (a * bogoliubovMap M hp.c hp.s (annihilatorGen M ν i)) = 0 := by
  dsimp [omegaP, omega0]
  have hinv : bogoliubovMap M hp.c (-hp.s) (bogoliubovMap M hp.c hp.s (annihilatorGen M ν i)) =
      annihilatorGen M ν i := by
    have := congr_arg (fun F => F (annihilatorGen M ν i))
      (bogoliubovMap_inverse_rev M hp.c hp.s hp.hyperbolic_id)
    simpa using this
  rw [map_mul, hinv]
  have hann : oscRep M (annihilatorGen M ν i) 1 = 0 := by
    simp [annihilatorGen, oscRep, oscAnnihilation_one]
  change (MvPolynomial.lcoeff ℂ 0)
    ((oscRep M (bogoliubovMap M hp.c (-hp.s) a * annihilatorGen M ν i)) 1) = 0
  rw [map_mul, Module.End.mul_apply, hann, map_zero, map_zero]

theorem omegaP_dressed_creator_mul (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (a : OscAlgebra M) (ν : Bosonize.A06.Orientation) (i : Fin M) :
    omegaP M hp (bogoliubovMap M hp.c hp.s (creatorGen M ν i) * a) = 0 := by
  dsimp [omegaP]
  have hinv : bogoliubovMap M hp.c (-hp.s) (bogoliubovMap M hp.c hp.s (creatorGen M ν i)) =
      creatorGen M ν i := by
    have := congr_arg (fun F => F (creatorGen M ν i))
      (bogoliubovMap_inverse_rev M hp.c hp.s hp.hyperbolic_id)
    simpa using this
  rw [map_mul, hinv, omega0_eq_pairing]
  set x := oscRep M (bogoliubovMap M hp.c (-hp.s) a) 1
  have hrep : oscRep M (creatorGen M ν i * bogoliubovMap M hp.c (-hp.s) a) 1 =
      oscCreation M (ν, i) x := by
    simp [creatorGen, oscRep, map_mul, Module.End.mul_apply, x]
  rw [hrep]
  have hpair0 : oscPairing M x 0 = 0 := by
    simp [oscPairing]
  have hconj : star (oscPairing M 1 (oscCreation M (ν, i) x)) = 0 := by
    rw [oscPairing_conj, oscCreation_pairing_adjoint, oscAnnihilation_one, hpair0]
  exact star_eq_zero.mp hconj

theorem omegaP_commutator (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (ν : Bosonize.A06.Orientation) (i : Fin M) :
    omegaP M hp (annihilatorGen M ν i * creatorGen M ν i) -
      omegaP M hp (creatorGen M ν i * annihilatorGen M ν i) =
      ((i.val + 1 : ℕ) : ℂ) := by
  have hdesc := omegaP_ccr_descends M hp 1 1 (ν, i) (ν, i)
  simp only [one_mul, mul_one, ite_true] at hdesc
  dsimp [annihilatorGen, creatorGen, oscWeight] at hdesc ⊢
  rw [map_sub, map_sub, map_smul, omegaP_one M hp, smul_eq_mul, mul_one] at hdesc
  linear_combination hdesc

section Fock

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

noncomputable def vectorState (h : ℕ) (ψ : Bosonize.A05.FockSpace σ h) (X : Bosonize.A05.Operators σ h) : ℂ :=
  inner ℂ ψ (X ψ)

theorem vectorState_ground_one (h : ℕ) (Ns : σ → ℤ) :
    vectorState h (Bosonize.A05.groundKet h Ns) 1 = 1 := by
  simp [vectorState, Bosonize.A05.groundKet, Bosonize.A02.ket_norm]

theorem vectorState_adjoint_mul_self (h : ℕ) (ψ : Bosonize.A05.FockSpace σ h) (X : Bosonize.A05.Operators σ h) :
    vectorState h ψ (LinearMap.adjoint X * X) = ((‖X ψ‖ ^ 2 : ℝ) : ℂ) := by
  dsimp [vectorState]
  rw [LinearMap.adjoint_inner_right (𝕜 := ℂ)]
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  push_cast
  rfl

end Fock

def compressedQR (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of ![![0, (c : ℂ), 0], ![0, 0, 0], ![(s : ℂ), 0, 0]]

def compressedQL (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of ![![0, 0, (c : ℂ)], ![(s : ℂ), 0, 0], ![0, 0, 0]]

noncomputable def noteCompressedPair : Bosonize.Ch18.HyperbolicPair :=
  ⟨5 / 3, 4 / 3, by norm_num⟩

theorem compressed_gram (c s : ℝ) :
    (compressedQR c s)ᴴ * compressedQR c s + (compressedQL c s)ᴴ * compressedQL c s =
      Matrix.diagonal ![2 * (s : ℂ) ^ 2, (c : ℂ) ^ 2, (c : ℂ) ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [compressedQR, compressedQL, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal, Fin.sum_univ_three]
    try ring
  }

theorem compressed_common_kernel_trivial (hp : Bosonize.Ch18.HyperbolicPair) (hs : hp.s ≠ 0)
    (v : Fin 3 → ℂ)
    (hR : (compressedQR hp.c hp.s).mulVec v = 0)
    (hL : (compressedQL hp.c hp.s).mulVec v = 0) :
    v = 0 := by
  have hc : hp.c ≠ 0 := by
    intro hc0
    have hhyp := hp.hyperbolic_id
    rw [hc0] at hhyp
    have : -hp.s ^ 2 = 1 := by linarith
    have : 0 ≤ hp.s ^ 2 := sq_nonneg hp.s
    linarith
  ext i
  fin_cases i
  · have hR2 := congr_fun hR 2
    simp [compressedQR, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hR2
    cases hR2 with
    | inl h => exact False.elim (hs h)
    | inr h => exact h
  · have hR0 := congr_fun hR 0
    simp [compressedQR, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hR0
    cases hR0 with
    | inl h => exact False.elim (hc h)
    | inr h => exact h
  · have hL0 := congr_fun hL 0
    simp [compressedQL, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hL0
    cases hL0 with
    | inl h => exact False.elim (hc h)
    | inr h => exact h

theorem compressed_no_vacuum_density (hp : Bosonize.Ch18.HyperbolicPair) (hs : hp.s ≠ 0) :
    ¬ ∃ ρ : Matrix (Fin 3) (Fin 3) ℂ,
      compressedQR hp.c hp.s * ρ = 0 ∧ compressedQL hp.c hp.s * ρ = 0 ∧ ρ.trace = 1 := by
  intro ⟨ρ, hR, hL, htr⟩
  have hρ : ρ = 0 := by
    ext i j
    have hcol := compressed_common_kernel_trivial hp hs (fun k => ρ k j)
      (by ext r; exact congr_fun (congr_fun hR r) j)
      (by ext r; exact congr_fun (congr_fun hL r) j)
    exact congr_fun hcol i
  subst hρ
  revert htr
  simp [Matrix.trace]

theorem compressed_kernel_of_s_zero (c : ℝ) :
    (compressedQR c 0).mulVec (Pi.single 0 1) = 0 ∧
      (compressedQL c 0).mulVec (Pi.single 0 1) = 0 := by
  constructor
  · ext i
    fin_cases i <;> simp [compressedQR, Matrix.mulVec]
  · ext i
    fin_cases i <;> simp [compressedQL, Matrix.mulVec]

theorem note_compressed_witness :
    (compressedQR noteCompressedPair.c noteCompressedPair.s)ᴴ *
        compressedQR noteCompressedPair.c noteCompressedPair.s +
      (compressedQL noteCompressedPair.c noteCompressedPair.s)ᴴ *
        compressedQL noteCompressedPair.c noteCompressedPair.s =
      Matrix.diagonal ![(32 : ℂ) / 9, (25 : ℂ) / 9, (25 : ℂ) / 9] := by
  rw [compressed_gram]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, noteCompressedPair] <;> norm_num

end Bosonize.A08
