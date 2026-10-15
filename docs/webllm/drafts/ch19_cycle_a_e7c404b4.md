## Source map

- Primary specification: `docs/webllm/guidance/ch19_phase_a_sources.md` (sections 0, A, B, C, D) and independent review records (hub `.agentctl/reviews/ch19_phaseA_review1.md`, `ch19_phaseA_review2.md`, `ch19_phaseA_review1_round2.md`; mirrored in `docs/webllm/reviews/ch19_phase_a/`).
- Review trail:
  - Round 1 draft: reviewed by Reviewer 1 (verdict FAIL with one blocking item: missing character constraint $\zeta \neq 0$ on the diagonal theorems; linter items were non-blocking) and adjudicated by Reviewer 2 (verdict CHANGES_REQUIRED).
  - Revision round 2 (this proposal): applies Reviewer 2's adjudication change list:
    1. B1: added $(h\zeta : \zeta \neq 0)$ to `density_kernel_diagonal` and `density_kernel_diagonal_pos`.
    2. N3a–N3d: pruned unused explicit hypotheses from the four Fock ground contractions (`ground_lowering_raising`, `ground_raising_lowering`, `ground_raising_raising`, `ground_lowering_lowering`) to ensure clean compilation under `-DwarningAsError=true`.
    3. N1: added full CCR quotient descent lemmas for creator-creator and annihilator-annihilator pairs (`omega0_ccr_descends_aa`, `omega0_ccr_descends_cc`, `omegaP_ccr_descends_aa`, `omegaP_ccr_descends_cc`).
    4. Anti-vacuity & helper additions: added `bogoliubovMap_inverse_iff` (with `[NeZero M]`) and `omegaP_comp_bogoliubovMap`.
    5. Upstream promotion: `CH18` is now verified in Core (`Bosonize.Core.Ch18Bogoliubov`), so this draft directly uses the genuine Core import `import Bosonize.Core.Ch18Bogoliubov`.
- Pedagogical and mathematical notes:
  - `notes/md/ch19_correlations.md`: quasi-free interacting state functional $\omega_{\tilde{\Omega}} = \omega_P$, exact two-point mode correlators, and real-space spatial density correlators.
  - `notes/appendices/a08_states_and_correlations.md`: two-branch polynomial carrier, positive-definite Gram pairing, word algebra with quotient relations, Bogoliubov automorphism pullback, and the finite compressed common-kernel obstruction.
- Literature anchors (consulted via hub):
  - GIA3 (`giamarchi_2004/03_ch03_luttinger_liquids_pdf084-113.md`): free vacuum mode contractions and non-zero ground fluctuations.
  - GIA22 (`giamarchi_2004/2.2_physical_properties_and_correlation_functions.md`): continuum density correlator analogues and character sums.
  - SEN (`senechal_1999/06_tomonaga_luttinger.md`): Bogoliubov transformation rules and hyperbolic coefficient relations.
  - ML (`mattis_2013/mattis_luttinger_2013_ch01_the_luttinger_model_and_its_solution.md`): vacuum Schwinger anomaly and difference between bare and dressed vacuum states.
  - VDS4 (`von_delft_schoeller_1998/04_bosonic_fock_space.md`), VDS9 (`09_vertex_operators.md`), VDS10 (`10_impurity_in_tll.md`): bosonic Fock representation and cross-branch mode mixing.
- Core dependencies reused without redefinition:
  - `Bosonize.Core.Ch18Bogoliubov`: `HyperbolicPair`, `luttingerG`, `luttingerGInv`, `luttingerG_mul_inv`, `hyperbolic_coeff_eq_luttinger`, `HyperbolicPair.inverse_combination`, `concretePair`, `concreteParams`, `concreteCarrierH`, `concreteCutoff`, `concreteBudget`, `concreteNs`, `concreteBranches`.
  - `Bosonize.Core.A07InteractionsAndBogoliubov`: `oppositeOrientation`, `bogoliubovCreator`, `bogoliubovAnnihilator`, `bogoliubov_creator_adjoint`, `bogoliubov_ccr_on_budget`.
  - `Bosonize.Core.A06ChiralFields`: `Orientation` (`.right`, `.left`), `Branches`, `speciesOf`, `latticeCharacter`, `marginAt`, `branchMargins`.
  - `Bosonize.Core.A05MultiSpecies`: `FockSpace σ h`, `Operators σ h`, `rho`, `groundKet`, `admissible`, `jointBudget`.
  - `Bosonize.Core.A02CARHilbert`: `commutator`.
  - `Bosonize.Core.A01FourierCharacters`: `integerCharacter`, `canonicalRoot`.
  - `Bosonize.Core.Ch16FieldHamiltonian`: `excitedKet`, `standardBranches`.

## Design and scope

- Dual-layer architecture:
  1. Abstract CCR oscillator layer (`Bosonize.A08` and `Bosonize.Ch19` abstract section):
     - Carrier: two-branch multivariable polynomials `OscPoly M = MvPolynomial (Orientation × Fin M) ℂ` with strictly positive mode weights `oscWeight p = p.2.val + 1`.
     - Inner product: positive-definite weighted Gram pairing `oscPairing M` with diagonal norm `oscMonomialNorm r = r.prod (fun p k => oscWeight p ^ k * k.factorial)`.
     - Operators: `oscCreation` (multiplication by $X_p$) and `oscAnnihilation` (weighted derivation $w_p \partial_p$), satisfying adjointness and scalar CCR.
     - Word algebra: `OscAlgebra M = FreeAlgebra ℂ (Bool × OscMode M)`, representing creation (`true`) and annihilation (`false`) words.
     - Vacuum state: $\omega_0(a) = \langle 1, \pi(a) 1 \rangle$, linear, normalized ($\omega_0(1) = 1$), positive on word Gram sums, and vanishing on the full CCR quotient ideal ($[A, C] - m I$, $[A, A]$, $[C, C]$).
     - Bogoliubov automorphism: $\beta_{c,s}$ on `OscAlgebra M`, with inverse $\beta_{c,-s}$ if and only if $c^2 - s^2 = 1$ (for $M \ge 1$).
     - Interacting quasi-free state: $\omega_P = \omega_0 \circ \beta_{c,-s}$ (pullback in the inverse direction). Annihilates dressed lowering modes, is annihilated by dressed raising modes, and satisfies $\omega_P \circ \beta_{c,s} = \omega_0$.
  2. Finite Fock Hilbert layer (`Fock` sections):
     - Carrier: `A05.FockSpace σ h` with inner product `inner ℂ ψ (X ψ)`.
     - Contractions evaluated under explicit minimal hypotheses without unreferenced binders that would trigger linter warnings under `-DwarningAsError=true`.
     - Scalar agreement between Fock ground expectation and free state correlator ($\omega_P$ at $s = 0$) without conflating the representations.
- Compressed vacuum obstruction:
  - Finite $3 \times 3$ slice basis $\{1, X_R, X_L\}$ at mode $m=1$.
  - Explicit matrices `compressedQR` and `compressedQL`.
  - Definiteness theorem: $Q_R^\dagger Q_R + Q_L^\dagger Q_L = \operatorname{diag}(2s^2, c^2, c^2)$, strictly positive for $s \neq 0$, proving common kernel is $\{0\}$ and no normalized density matrix can be annihilated.
  - Necessity of $s \neq 0$: at $s = 0$, vector $(1, 0, 0)^T$ is in the common kernel.
  - Witness at $(c,s) = (5/3, 4/3)$ yielding diagonal $(32/9, 25/9, 25/9)$.
- Exact correlation theorems:
  - Both bare right-branch contractions: $\omega_P(C_{R,i} A_{R,j}) = \delta_{ij} m s^2$ and $\omega_P(A_{R,i} C_{R,j}) = \delta_{ij} m c^2$.
  - Anomalous same-branch $CC$ and $AA$ contractions vanish identically.
  - Cross-branch contractions $\omega_P(C_{R,i} C_{L,j}) = \omega_P(A_{R,i} A_{L,j}) = -\delta_{ij} m c s$, sensitive to the transformation sign.
  - Ordered spatial kernel: $D(x,y) = L^{-2} \sum_{m=1}^M m (s^2 \zeta^{-md} + c^2 \zeta^{md})$ for $d = x.val - y.val$ and $\zeta \neq 0$.
  - Symmetrized observable: $(D(x,y) + D(y,x))/2$ has symmetric prefactor $(g + g^{-1})/4$.
  - Commutator expectation $D(x,y) - D(y,x)$ reproduces the Schwinger kernel with coefficients $1$ and $-1$, independent of $(c,s)$.
  - Explicit non-zero witness `concrete_correlation_witness` verifying both abstract and Fock evaluations with $s \neq 0$.
- Deferred to later chapters:
  - Charge lattice, Klein zero-mode shifts, vertex operators, formal series $A[[t]]$, and CDW/SC exponents (Chapter 20).
  - Continuum scaling limits and power-law asymptotics.

## Lean draft

```lean
import Bosonize.Core.Ch18Bogoliubov

-- BEGIN_MODULE BosonizeStubs/A08OscillatorStates.lean
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
-- END_MODULE BosonizeStubs/A08OscillatorStates.lean

-- BEGIN_MODULE BosonizeStubs/Ch19Correlations.lean
namespace Bosonize.Ch19

open scoped BigOperators

noncomputable def densityKernel (h M : ℕ) (ζ : ℂ) (c2 s2 : ℝ) (d : ℤ) : ℂ :=
  (((2 * h : ℕ) : ℂ)⁻¹) ^ 2 * ∑ m ∈ Finset.Icc 1 M, (m : ℂ) *
    ((s2 : ℂ) * Bosonize.A01.integerCharacter ζ (-(m : ℤ)) d +
     (c2 : ℂ) * Bosonize.A01.integerCharacter ζ (m : ℤ) d)

noncomputable def oscDensityR (h M : ℕ) (ζ : ℂ) (x : ZMod (2 * h)) : Bosonize.A08.OscAlgebra M :=
  (((2 * h : ℕ) : ℂ)⁻¹) • ∑ i : Fin M,
    (Bosonize.A06.latticeCharacter h ζ (-((i.val + 1 : ℕ) : ℤ)) x • Bosonize.A08.creatorGen M .right i +
     Bosonize.A06.latticeCharacter h ζ ((i.val + 1 : ℕ) : ℤ) x • Bosonize.A08.annihilatorGen M .right i)

noncomputable def orderedDensityCorrelation (h M : ℕ) (ζ : ℂ) (hp : Bosonize.Ch18.HyperbolicPair) (x y : ZMod (2 * h)) : ℂ :=
  Bosonize.A08.omegaP M hp (oscDensityR h M ζ x * oscDensityR h M ζ y)

def freePair : Bosonize.Ch18.HyperbolicPair :=
  ⟨1, 0, by norm_num⟩

theorem omegaP_creator_annihilator_right (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.creatorGen M .right i * Bosonize.A08.annihilatorGen M .right j) =
      if i = j then ((i.val + 1 : ℕ) : ℂ) * (hp.s : ℂ) ^ 2 else 0 := by sorry

theorem omegaP_annihilator_creator_right (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.annihilatorGen M .right i * Bosonize.A08.creatorGen M .right j) =
      if i = j then ((i.val + 1 : ℕ) : ℂ) * (hp.c : ℂ) ^ 2 else 0 := by sorry

theorem omegaP_creator_creator_right (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.creatorGen M .right i * Bosonize.A08.creatorGen M .right j) = 0 := by sorry

theorem omegaP_annihilator_annihilator_right (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.annihilatorGen M .right i * Bosonize.A08.annihilatorGen M .right j) = 0 := by sorry

theorem omegaP_cross_creator_creator (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.creatorGen M .right i * Bosonize.A08.creatorGen M .left j) =
      if i = j then -(((i.val + 1 : ℕ) : ℂ) * (hp.c : ℂ) * (hp.s : ℂ)) else 0 := by sorry

theorem omegaP_cross_annihilator_annihilator (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.annihilatorGen M .right i * Bosonize.A08.annihilatorGen M .left j) =
      if i = j then -(((i.val + 1 : ℕ) : ℂ) * (hp.c : ℂ) * (hp.s : ℂ)) else 0 := by sorry

theorem omegaP_cross_creator_annihilator (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.creatorGen M .right i * Bosonize.A08.annihilatorGen M .left j) = 0 := by sorry

theorem ordered_density_kernel (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0)
    (hp : Bosonize.Ch18.HyperbolicPair) (x y : ZMod (2 * h)) :
    orderedDensityCorrelation h M ζ hp x y =
      densityKernel h M ζ (hp.c ^ 2) (hp.s ^ 2) ((x.val : ℤ) - (y.val : ℤ)) := by sorry

theorem ordered_density_kernel_lattice (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 * h)) (hp : Bosonize.Ch18.HyperbolicPair) (x y : ZMod (2 * h)) :
    orderedDensityCorrelation h M ζ hp x y =
      (((2 * h : ℕ) : ℂ)⁻¹) ^ 2 * ∑ m ∈ Finset.Icc 1 M, (m : ℂ) *
        ((hp.s : ℂ) ^ 2 * Bosonize.A06.latticeCharacter h ζ (-(m : ℤ)) (x - y) +
         (hp.c : ℂ) ^ 2 * Bosonize.A06.latticeCharacter h ζ (m : ℤ) (x - y)) := by sorry

theorem density_commutator_expectation (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0)
    (hp : Bosonize.Ch18.HyperbolicPair) (x y : ZMod (2 * h)) :
    orderedDensityCorrelation h M ζ hp x y - orderedDensityCorrelation h M ζ hp y x =
      densityKernel h M ζ 1 (-1) ((x.val : ℤ) - (y.val : ℤ)) := by sorry

theorem symmetrized_density_kernel (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0)
    (hp : Bosonize.Ch18.HyperbolicPair) (x y : ZMod (2 * h)) :
    (orderedDensityCorrelation h M ζ hp x y + orderedDensityCorrelation h M ζ hp y x) / 2 =
      densityKernel h M ζ
        ((Bosonize.Ch18.luttingerG hp + (Bosonize.Ch18.luttingerG hp)⁻¹) / 4)
        ((Bosonize.Ch18.luttingerG hp + (Bosonize.Ch18.luttingerG hp)⁻¹) / 4)
        ((x.val : ℤ) - (y.val : ℤ)) := by sorry

theorem s_sq_eq_luttinger (hp : Bosonize.Ch18.HyperbolicPair) :
    hp.s ^ 2 = (Bosonize.Ch18.luttingerG hp + (Bosonize.Ch18.luttingerG hp)⁻¹ - 2) / 4 := by sorry

theorem c_sq_eq_luttinger (hp : Bosonize.Ch18.HyperbolicPair) :
    hp.c ^ 2 = (Bosonize.Ch18.luttingerG hp + (Bosonize.Ch18.luttingerG hp)⁻¹ + 2) / 4 := by sorry

theorem density_kernel_diagonal (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0)
    (hp : Bosonize.Ch18.HyperbolicPair) (x : ZMod (2 * h)) :
    orderedDensityCorrelation h M ζ hp x x =
      ((((hp.c ^ 2 + hp.s ^ 2) * ((M * (M + 1) : ℝ) / 2) / ((2 * h : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)) := by sorry

theorem density_kernel_diagonal_pos (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0)
    (hp : Bosonize.Ch18.HyperbolicPair) (x : ZMod (2 * h))
    (hh : 0 < h) (hM : 1 ≤ M) :
    0 < (orderedDensityCorrelation h M ζ hp x x).re := by sorry

theorem ordered_density_free (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0)
    (hp : Bosonize.Ch18.HyperbolicPair) (hs : hp.s = 0) (x y : ZMod (2 * h)) :
    orderedDensityCorrelation h M ζ hp x y =
      densityKernel h M ζ 1 0 ((x.val : ℤ) - (y.val : ℤ)) := by sorry

section Fock

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

noncomputable def fockDensityR (h M : ℕ) (ζ : ℂ) (branches : Bosonize.A06.Branches σ) (x : ZMod (2 * h)) :
    Bosonize.A05.Operators σ h :=
  (((2 * h : ℕ) : ℂ)⁻¹) • ∑ m ∈ Finset.Icc 1 M,
    (Bosonize.A06.latticeCharacter h ζ (-(m : ℤ)) x • Bosonize.A05.rho h branches.rightSpecies (m : ℤ) +
     Bosonize.A06.latticeCharacter h ζ (m : ℤ) x • Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)))

theorem ground_lowering_raising (h M : ℕ) (hh : 0 < h) (m n : ℕ)
    (hm : 1 ≤ m) (hmM : m ≤ M) (hnM : n ≤ M)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.marginAt h M 0 Ns branches.rightSpecies) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) *
         Bosonize.A05.rho h branches.rightSpecies (n : ℤ)) =
      if m = n then (m : ℂ) else 0 := by sorry

theorem ground_raising_lowering (h : ℕ) (hh : 0 < h) (m n : ℕ) (hn : 1 ≤ n)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A05.rho h branches.rightSpecies (m : ℤ) *
         Bosonize.A05.rho h branches.rightSpecies (-(n : ℤ))) = 0 := by sorry

theorem ground_raising_raising (h : ℕ) (hh : 0 < h) (m n : ℕ) (hm : 1 ≤ m)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A05.rho h branches.rightSpecies (m : ℤ) *
         Bosonize.A05.rho h branches.rightSpecies (n : ℤ)) = 0 := by sorry

theorem ground_lowering_lowering (h : ℕ) (hh : 0 < h) (m n : ℕ) (hn : 1 ≤ n)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) *
         Bosonize.A05.rho h branches.rightSpecies (-(n : ℤ))) = 0 := by sorry

theorem excited_ket_norm_sq (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hmM : m ≤ M)
    (branches : Bosonize.A06.Branches σ) (η : Bosonize.A06.Orientation) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.marginAt h M 0 Ns (Bosonize.A06.speciesOf branches η)) :
    ‖Bosonize.Ch16.excitedKet h Ns branches η m‖ ^ 2 = (m : ℝ) := by sorry

theorem ground_dressed_number (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hp : Bosonize.Ch18.HyperbolicPair)
    (branches : Bosonize.A06.Branches σ) (η : Bosonize.A06.Orientation) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.branchMargins h M 0 Ns branches) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches η *
         Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches η) =
      (m : ℂ) * (hp.s : ℂ) ^ 2 := by sorry

theorem ground_dressed_reverse (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hp : Bosonize.Ch18.HyperbolicPair)
    (branches : Bosonize.A06.Branches σ) (η : Bosonize.A06.Orientation) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.branchMargins h M 0 Ns branches) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches η *
         Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches η) =
      (m : ℂ) * (hp.c : ℂ) ^ 2 := by sorry

theorem ground_not_dressed_vacuum (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hp : Bosonize.Ch18.HyperbolicPair) (hs : hp.s ≠ 0)
    (branches : Bosonize.A06.Branches σ) (η : Bosonize.A06.Orientation) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.branchMargins h M 0 Ns branches) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches η *
         Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches η) ≠ 0 := by sorry

theorem fock_ground_density_kernel (h M : ℕ) [NeZero (2 * h)] (hh : 0 < h)
    (ζ : ℂ) (hζ : ζ ≠ 0) (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.marginAt h M 0 Ns branches.rightSpecies)
    (x y : ZMod (2 * h)) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (fockDensityR h M ζ branches x * fockDensityR h M ζ branches y) =
      densityKernel h M ζ 1 0 ((x.val : ℤ) - (y.val : ℤ)) := by sorry

/-- The Fock ground expectation matches the abstract free state correlation value.
This is a scalar equality at s = 0 only; it is not an identification of states
or representations. -/
theorem fock_ground_matches_free_state (h M : ℕ) [NeZero (2 * h)] (hh : 0 < h)
    (ζ : ℂ) (hζ : ζ ≠ 0) (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.marginAt h M 0 Ns branches.rightSpecies)
    (x y : ZMod (2 * h)) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (fockDensityR h M ζ branches x * fockDensityR h M ζ branches y) =
      orderedDensityCorrelation h M ζ freePair x y := by sorry

end Fock

theorem concrete_correlation_witness :
    Bosonize.A08.omegaP 2 Bosonize.Ch18.concretePair
        (Bosonize.A08.creatorGen 2 .right (1 : Fin 2) *
         Bosonize.A08.annihilatorGen 2 .right (1 : Fin 2)) = (9 : ℂ) / 8 ∧
      Bosonize.A08.omegaP 2 Bosonize.Ch18.concretePair
        (Bosonize.A08.annihilatorGen 2 .right (1 : Fin 2) *
         Bosonize.A08.creatorGen 2 .right (1 : Fin 2)) = (25 : ℂ) / 8 ∧
      Bosonize.A08.omegaP 2 Bosonize.Ch18.concretePair
        (Bosonize.A08.creatorGen 2 .right (1 : Fin 2) *
         Bosonize.A08.creatorGen 2 .left (1 : Fin 2)) = -(15 : ℂ) / 8 ∧
      orderedDensityCorrelation 8 2 (Bosonize.A01.canonicalRoot (2 * 8))
        Bosonize.Ch18.concretePair 0 0 = (51 : ℂ) / 2048 ∧
      Bosonize.A06.branchMargins 8 2 0 Bosonize.Ch18.concreteNs Bosonize.Ch18.concreteBranches ∧
      Bosonize.A08.vectorState 8 (Bosonize.A05.groundKet 8 Bosonize.Ch18.concreteNs)
        (Bosonize.A05.rho 8 0 (-2) * Bosonize.A05.rho 8 0 2) = 2 ∧
      Bosonize.A08.vectorState 8 (Bosonize.A05.groundKet 8 Bosonize.Ch18.concreteNs)
        (Bosonize.A07Interactions.bogoliubovCreator 8 2
          Bosonize.Ch18.concretePair.c Bosonize.Ch18.concretePair.s
          Bosonize.Ch18.concreteBranches .right *
         Bosonize.A07Interactions.bogoliubovAnnihilator 8 2
          Bosonize.Ch18.concretePair.c Bosonize.Ch18.concretePair.s
          Bosonize.Ch18.concreteBranches .right) = (9 : ℂ) / 8 ∧
      Bosonize.A08.vectorState 8 (Bosonize.A05.groundKet 8 Bosonize.Ch18.concreteNs)
        (Bosonize.A07Interactions.bogoliubovCreator 8 2
          Bosonize.Ch18.concretePair.c Bosonize.Ch18.concretePair.s
          Bosonize.Ch18.concreteBranches .right *
         Bosonize.A07Interactions.bogoliubovAnnihilator 8 2
          Bosonize.Ch18.concretePair.c Bosonize.Ch18.concretePair.s
          Bosonize.Ch18.concreteBranches .right) ≠ 0 ∧
      Bosonize.A08.vectorState 8 (Bosonize.A05.groundKet 8 Bosonize.Ch18.concreteNs)
        (fockDensityR 8 2 (Bosonize.A01.canonicalRoot (2 * 8)) Bosonize.Ch18.concreteBranches 0 *
         fockDensityR 8 2 (Bosonize.A01.canonicalRoot (2 * 8)) Bosonize.Ch18.concreteBranches 0) =
        (3 : ℂ) / 256 := by sorry

end Bosonize.Ch19
-- END_MODULE BosonizeStubs/Ch19Correlations.lean
```

## Companion notebook

- Carrier review tasks:
  - verify polynomial pairing well-foundedness and non-degeneracy (`oscPairing_self_eq_zero`);
  - check that `oscWeight` values are strictly positive ($m = i.val + 1 \ge 1$) so no infinite-dimensional slice is created;
  - confirm adjointness `oscCreation_pairing_adjoint` and commutator $[A, C] = m I$ algebraically on polynomials.
- State and automorphism review tasks:
  - trace $\omega_0$ definition as vacuum state evaluation $\langle 1, \pi(a) 1 \rangle$;
  - verify that $\beta_{c,s}$ satisfies $(c^2 - s^2 = 1) \iff \beta_{c,s} \circ \beta_{c,-s} = \text{id}$ on non-empty mode sets (`bogoliubovMap_inverse_iff`);
  - verify the pullback direction $\omega_P = \omega_0 \circ \beta_{c,-s}$ so that dressed lowering operators annihilate the vacuum, and $\omega_P \circ \beta_{c,s} = \omega_0$ (`omegaP_comp_bogoliubovMap`);
  - confirm full quotient descent on all relation pairs: $[A, C] - m I$, $[A, A]$, and $[C, C]$ for both bare $\omega_0$ and dressed $\omega_P$;
  - confirm that the non-multiplicativity witness $\omega_P(A C) - \omega_P(C A) = m$ holds without assuming states are homomorphisms.
- Contraction review tasks:
  - calculate both same-branch contractions: $m s^2$ for $CA$ and $m c^2$ for $AC$;
  - check that $c^2$ remains non-zero even when $s = 0$ (free vacuum fluctuations);
  - check that cross-branch contractions have the exact $-\delta_{ij} m c s$ sign, sensitive to $\beta$ direction.
- Correlation kernel review tasks:
  - verify that $D(x,y) = L^{-2} \sum m (s^2 \zeta^{-md} + c^2 \zeta^{md})$ preserves the ordered observable and does not collapse into a cosine;
  - verify that the commutator expectation $D(x,y) - D(y,x)$ matches the $(1, -1)$ Schwinger kernel;
  - check diagonal positivity $0 < (D(x,x)).re$ under the required condition $\zeta \neq 0$ for $h > 0$ and $M \ge 1$.
- Compressed vacuum review tasks:
  - confirm $Q_R^\dagger Q_R + Q_L^\dagger Q_L = \operatorname{diag}(2s^2, c^2, c^2)$ matrix identity;
  - confirm that $s \neq 0$ implies strict positivity and trivial common kernel $\{0\}$;
  - confirm that $s = 0$ admits non-trivial kernel $(1, 0, 0)^T$, showing necessity of $s \neq 0$ for obstruction.
- Witness review tasks:
  - verify arithmetic of all conjuncts in `concrete_correlation_witness` via `norm_num`;
  - check that Fock ground state expectation $\langle \Omega, \tilde{C}_R \tilde{A}_R \Omega \rangle = 9/8 \neq 0$ witnesses that the bare Fock vacuum is not the interacting dressed vacuum.

## Review obligations

- Human mathematical review is required before any integration or freezing.
- Reviewers should confirm all of the following without weakening statements:
  - Carrier separation: abstract polynomial/word CCR carrier vs. finite Fock space carrier `A05.FockSpace σ h` are cleanly distinguished;
  - Direction of Bogoliubov pullback: $\omega_P = \omega_0 \circ \beta_{c,-s}$ is used, correctly making $\omega_P(a \tilde{A}) = 0$ and $\omega_P(\tilde{C} a) = 0$;
  - Non-vacuous states: neither states nor CCRs are taken as free variables or hypotheses; states are constructively defined functionals;
  - Non-degeneracy & character conditions: $h\zeta : \zeta \neq 0$ is required for spatial density kernel evaluations and diagonal positivity;
  - Clean linter interfaces: minimal hypotheses in Fock ground contraction lemmas avoiding unused binders;
  - Contraction completeness: both ordered contractions $CA$ ($s^2$) and $AC$ ($c^2$) are proved, and anomalous same-branch contractions vanish;
  - Cross-branch detector: cross contractions equal $-\delta_{ij} m c s$, distinguishing the physical sign of interaction;
  - Spatial kernel: the ordered kernel $D(x,y)$ is preserved rather than replaced by a symmetrized cosine;
  - Fock ground vs. dressed vacuum: no claim is made that the bare Fock ground state $\Omega$ is annihilated by dressed annihilators; the obstruction and nonzero action are witnessed with $s \neq 0$;
  - Standard axioms only: every data declaration depends exclusively on `{propext, Classical.choice, Quot.sound}`.
