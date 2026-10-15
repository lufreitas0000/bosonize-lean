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
      if r = s then (oscMonomialNorm r : ℂ) else 0 := by sorry

theorem oscPairing_conj (M : ℕ) (p q : OscPoly M) :
    star (oscPairing M p q) = oscPairing M q p := by sorry

theorem oscPairing_self_nonneg (M : ℕ) (p : OscPoly M) :
    0 ≤ (oscPairing M p p).re := by sorry

theorem oscPairing_self_eq_zero (M : ℕ) (p : OscPoly M) :
    oscPairing M p p = 0 ↔ p = 0 := by sorry

theorem oscCreation_pairing_adjoint (M : ℕ) (p : OscMode M) (x y : OscPoly M) :
    oscPairing M (oscCreation M p x) y = oscPairing M x (oscAnnihilation M p y) := by sorry

theorem osc_ccr (M : ℕ) (p q : OscMode M) :
    Bosonize.A02.commutator (oscAnnihilation M p) (oscCreation M q) =
      if p = q then (oscWeight p : ℂ) • (1 : Module.End ℂ (OscPoly M)) else 0 := by sorry

theorem osc_annihilators_commute (M : ℕ) (p q : OscMode M) :
    Bosonize.A02.commutator (oscAnnihilation M p) (oscAnnihilation M q) = 0 := by sorry

theorem osc_creators_commute (M : ℕ) (p q : OscMode M) :
    Bosonize.A02.commutator (oscCreation M p) (oscCreation M q) = 0 := by sorry

theorem oscAnnihilation_one (M : ℕ) (p : OscMode M) :
    oscAnnihilation M p 1 = 0 := by sorry

theorem omega0_eq_pairing (M : ℕ) (a : OscAlgebra M) :
    omega0 M a = oscPairing M 1 (oscRep M a 1) := by sorry

theorem omega0_one (M : ℕ) :
    omega0 M 1 = 1 := by sorry

theorem omega0_gramSum (M : ℕ) {n : ℕ} (w : Fin n → OscWord M) (z : Fin n → ℂ) :
    (gramSum M (omega0 M) w z).im = 0 ∧ 0 ≤ (gramSum M (omega0 M) w z).re := by sorry

theorem omega0_ccr_descends (M : ℕ) (a b : OscAlgebra M) (p q : OscMode M) :
    omega0 M (a * (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (true, q) -
      FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (false, p) -
      (if p = q then (oscWeight p : ℂ) else 0) • 1) * b) = 0 := by sorry

theorem omega0_ccr_descends_aa (M : ℕ) (a b : OscAlgebra M) (p q : OscMode M) :
    omega0 M (a * (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (false, q) -
      FreeAlgebra.ι ℂ (false, q) * FreeAlgebra.ι ℂ (false, p)) * b) = 0 := by sorry

theorem omega0_ccr_descends_cc (M : ℕ) (a b : OscAlgebra M) (p q : OscMode M) :
    omega0 M (a * (FreeAlgebra.ι ℂ (true, p) * FreeAlgebra.ι ℂ (true, q) -
      FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (true, p)) * b) = 0 := by sorry

theorem bogoliubovMap_inverse (M : ℕ) (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) :
    (bogoliubovMap M c s).comp (bogoliubovMap M c (-s)) = AlgHom.id ℂ (OscAlgebra M) := by sorry

theorem bogoliubovMap_inverse_rev (M : ℕ) (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) :
    (bogoliubovMap M c (-s)).comp (bogoliubovMap M c s) = AlgHom.id ℂ (OscAlgebra M) := by sorry

theorem bogoliubovMap_inverse_iff (M : ℕ) [NeZero M] (c s : ℝ) :
    (bogoliubovMap M c s).comp (bogoliubovMap M c (-s)) = AlgHom.id ℂ (OscAlgebra M) ↔
      c ^ 2 - s ^ 2 = 1 := by sorry

theorem bogoliubovMap_word_adjoint (M : ℕ) (c s : ℝ) (w : OscWord M) (x y : OscPoly M) :
    oscPairing M x (oscRep M (bogoliubovMap M c s (wordElement M (wordDagger w))) y) =
      oscPairing M (oscRep M (bogoliubovMap M c s (wordElement M w)) x) y := by sorry

theorem omegaP_one (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) :
    omegaP M hp 1 = 1 := by sorry

theorem omegaP_gramSum (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) {n : ℕ}
    (w : Fin n → OscWord M) (z : Fin n → ℂ) :
    (gramSum M (omegaP M hp) w z).im = 0 ∧ 0 ≤ (gramSum M (omegaP M hp) w z).re := by sorry

theorem omegaP_ccr_descends (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (a b : OscAlgebra M) (p q : OscMode M) :
    omegaP M hp (a * (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (true, q) -
      FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (false, p) -
      (if p = q then (oscWeight p : ℂ) else 0) • 1) * b) = 0 := by sorry

theorem omegaP_ccr_descends_aa (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (a b : OscAlgebra M) (p q : OscMode M) :
    omegaP M hp (a * (FreeAlgebra.ι ℂ (false, p) * FreeAlgebra.ι ℂ (false, q) -
      FreeAlgebra.ι ℂ (false, q) * FreeAlgebra.ι ℂ (false, p)) * b) = 0 := by sorry

theorem omegaP_ccr_descends_cc (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (a b : OscAlgebra M) (p q : OscMode M) :
    omegaP M hp (a * (FreeAlgebra.ι ℂ (true, p) * FreeAlgebra.ι ℂ (true, q) -
      FreeAlgebra.ι ℂ (true, q) * FreeAlgebra.ι ℂ (true, p)) * b) = 0 := by sorry

theorem omegaP_comp_bogoliubovMap (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) :
    (omegaP M hp).comp (bogoliubovMap M hp.c hp.s).toLinearMap = omega0 M := by sorry

theorem omegaP_mul_dressed_annihilator (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (a : OscAlgebra M) (ν : Bosonize.A06.Orientation) (i : Fin M) :
    omegaP M hp (a * bogoliubovMap M hp.c hp.s (annihilatorGen M ν i)) = 0 := by sorry

theorem omegaP_dressed_creator_mul (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (a : OscAlgebra M) (ν : Bosonize.A06.Orientation) (i : Fin M) :
    omegaP M hp (bogoliubovMap M hp.c hp.s (creatorGen M ν i) * a) = 0 := by sorry

theorem omegaP_commutator (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair)
    (ν : Bosonize.A06.Orientation) (i : Fin M) :
    omegaP M hp (annihilatorGen M ν i * creatorGen M ν i) -
      omegaP M hp (creatorGen M ν i * annihilatorGen M ν i) =
      ((i.val + 1 : ℕ) : ℂ) := by sorry

section Fock

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

noncomputable def vectorState (h : ℕ) (ψ : Bosonize.A05.FockSpace σ h) (X : Bosonize.A05.Operators σ h) : ℂ :=
  inner ℂ ψ (X ψ)

theorem vectorState_ground_one (h : ℕ) (Ns : σ → ℤ) :
    vectorState h (Bosonize.A05.groundKet h Ns) 1 = 1 := by sorry

theorem vectorState_adjoint_mul_self (h : ℕ) (ψ : Bosonize.A05.FockSpace σ h) (X : Bosonize.A05.Operators σ h) :
    vectorState h ψ (LinearMap.adjoint X * X) = ((‖X ψ‖ ^ 2 : ℝ) : ℂ) := by sorry

end Fock

def compressedQR (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of ![![0, (c : ℂ), 0], ![0, 0, 0], ![(s : ℂ), 0, 0]]

def compressedQL (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of ![![0, 0, (c : ℂ)], ![(s : ℂ), 0, 0], ![0, 0, 0]]

noncomputable def noteCompressedPair : Bosonize.Ch18.HyperbolicPair :=
  ⟨5 / 3, 4 / 3, by norm_num⟩

theorem compressed_gram (c s : ℝ) :
    (compressedQR c s)ᴴ * compressedQR c s + (compressedQL c s)ᴴ * compressedQL c s =
      Matrix.diagonal ![2 * (s : ℂ) ^ 2, (c : ℂ) ^ 2, (c : ℂ) ^ 2] := by sorry

theorem compressed_common_kernel_trivial (hp : Bosonize.Ch18.HyperbolicPair) (hs : hp.s ≠ 0)
    (v : Fin 3 → ℂ)
    (hR : (compressedQR hp.c hp.s).mulVec v = 0)
    (hL : (compressedQL hp.c hp.s).mulVec v = 0) :
    v = 0 := by sorry

theorem compressed_no_vacuum_density (hp : Bosonize.Ch18.HyperbolicPair) (hs : hp.s ≠ 0) :
    ¬ ∃ ρ : Matrix (Fin 3) (Fin 3) ℂ,
      compressedQR hp.c hp.s * ρ = 0 ∧ compressedQL hp.c hp.s * ρ = 0 ∧ ρ.trace = 1 := by sorry

theorem compressed_kernel_of_s_zero (c : ℝ) :
    (compressedQR c 0).mulVec (Pi.single 0 1) = 0 ∧
      (compressedQL c 0).mulVec (Pi.single 0 1) = 0 := by sorry

theorem note_compressed_witness :
    (compressedQR noteCompressedPair.c noteCompressedPair.s)ᴴ *
        compressedQR noteCompressedPair.c noteCompressedPair.s +
      (compressedQL noteCompressedPair.c noteCompressedPair.s)ᴴ *
        compressedQL noteCompressedPair.c noteCompressedPair.s =
      Matrix.diagonal ![(32 : ℂ) / 9, (25 : ℂ) / 9, (25 : ℂ) / 9] := by sorry

end Bosonize.A08
