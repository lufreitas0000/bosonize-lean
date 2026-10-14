## Source map

| Source section | Mathematical item | Proposed module | Lean declarations |
| :--- | :--- | :--- | :--- |
| `a07_interactions_and_bogoliubov.md` §1, `ch17_LL_Models.md` §17.1–17.2 | Dirac sea occupation indicator $s_k$, sea quasiparticle creators/annihilators $q_k^\dagger, q_k$, sea normal-ordered bilinears $:c_a^\dagger c_b:$, word-level quartic sea-Wick ordering $:c_{k+m}^\dagger c_k c_{p-m}^\dagger c_p:$, exact contraction remainder, and finite diagonal correction $Q_{M,\nu}$ | `BosonizeStubs/A07InteractionsAndBogoliubov.lean` | `seaIndicator`, `creatorToSeaLetter`, `annihilatorToSeaLetter`, `seaInversions`, `bilinearWord`, `quarticWord`, `seaQuasiAnnihilator`, `seaQuasiCreator`, `evalSeaLetter`, `seaWickWord`, `numberOp`, `seaSubtractedNumber`, `seaNormalBilinear`, `seaNormalRho`, `quarticSeaWick`, `quarticContraction`, `seaWickWeight`, `seaWickTerm`, `seaWickCorrection`, `computationalMomentum`, `speciesRawIntra`, `rawIntraBranch`, `speciesCurrentIntra`, `currentIntraBranch`, `sea_normal_bilinear_diag`, `sea_normal_rho_nonzero`, `sea_normal_rho_zero`, `quartic_sea_wick_identity`, `quartic_sea_wick_zero_repeated`, `species_raw_intra_eq_current_sub_correction`, `raw_intra_eq_current_sub_correction`, `sea_wick_correction_ground_zero`, `sea_wick_correction_full_band` |
| `a07_interactions_and_bogoliubov.md` §2–3, `ch17_LL_Models.md` Lemma 17.3 | Raw inter-branch interaction $H_{2,\mathrm{raw}}$, hopping reduction $H_{2,\mathrm{hop}}$ vs. Luttinger pairing model $H_{2,\mathrm{pair}}$, hyperbolic parameter existence under $v_1 > \vert{}v_2\vert{}$, and restricted-action Bogoliubov identity | `BosonizeStubs/A07InteractionsAndBogoliubov.lean` | `rawInterBranch`, `hoppingInterBranch`, `pairingInterBranch`, `hoppingMode`, `pairingMode`, `oppositeOrientation`, `HyperbolicParams`, `bogoliubovCreator`, `bogoliubovAnnihilator`, `dressedModeNumber`, `raw_inter_eq_hopping`, `hopping_mode_kills_ground`, `pairing_mode_ground_nonzero`, `hopping_mode_self_adjoint`, `pairing_mode_self_adjoint`, `hyperbolic_params_exist`, `bogoliubov_creator_adjoint`, `bogoliubov_expansion_on_budget`, `bogoliubov_ccr_on_budget` |
| `a10_discrete_rg_and_schrieffer_wolff.md` §1–4, `ch17_LL_Models.md` Thm 17.6 | Energy-shell partitioning $\mathcal{B}_K = \mathcal{B}_{K-1} \oplus \mathcal{H}_K$, distinction from single-mode decimation on $X_1^2\vert{}\vec{N}\rangle_0$, piecewise non-resonant first-order SW generator $S_1$, explicit degree-two BCH polynomial and its compressed coefficient identity, forward off-block vanishing implication, and $2\times 2$ / $3\times 3$ matrix counterexample witnesses | `BosonizeStubs/A10DiscreteSchriefferWolff.lean` | `exactShellSet`, `lowShellProj`, `highShellProj`, `doubleModeOneKet`, `diagPart`, `offDiagPart`, `swSecondOrderCorrection`, `swEffectiveSecondOrder`, `bchSecondOrderPolynomial`, `sw_compressed_bch_second_order`, `swCounterEigenvector_2x2`, `sw_2x2_exact_eigenpair`, `swGeneratorMatrix`, `diagEnergyMatrix`, `nonResonant`, `swCounterH0_2x2`, `swCounterV_2x2`, `swCounterS1_2x2`, `swCounterP_2x2`, `swCounterH0_3x3`, `swCounterP_3x3`, `swCounterQ_3x3`, `swCounterV_3x3`, `swCounterS1_3x3`, `shell_proj_partition`, `shell_proj_orthogonal`, `shell_proj_self_adjoint`, `energy_shell_discards_double_mode_one`, `sw_generator_commutator_eq`, `sw_generator_skew_hermitian`, `sw_off_zero_implies_effective_exact`, `sw_2x2_truncation_witness`, `sw_3x3_no_iff_witness` |
| `ch17_LL_Models.md` §17.3 (Thm 17.5) | Free multi-species fermionic and Sugawara kinetic operators, chosen current and pairing interaction Hamiltonians, chemical potential shift $\mu = \pi v_F / L$, exact zero-mode energy, bosonized Luttinger Hamiltonian on the joint budget, and concrete non-vacuity witness | `BosonizeStubs/Ch17LuttingerModels.lean` | `v1Velocity`, `v2Velocity`, `canonicalMu`, `sugawaraMargin`, `zeroModeEnergyScalar`, `symmetricZeroModeScalar`, `chemicalPotentialOp`, `freeSugawaraKinetic`, `freeFermionKinetic`, `zeroModeEnergyOp`, `luttingerOscillatorOp`, `luttingerBosonizedHamiltonian`, `luttingerChosenModel`, `luttingerFermionChosenModel`, `zero_mode_scalar_canonical_mu`, `luttinger_chosen_eq_bosonized`, `zero_mode_op_on_budget`, `free_fermion_eq_sugawara_on_budget`, `luttinger_hamiltonian_on_budget`, `luttinger_hamiltonian_canonical_mu_on_budget`, `luttinger_raw_intra_on_budget`, `concrete_luttinger_witness` |

### Source discrepancies and resolution notes
1. **Fermionic Reordering via CAR Anticommutators (§17.4.1 & Appendix A07 §1):** Technical Note 17.4.1 and Appendix A07 warn against treating fermionic reordering as a commutator or attempting to reorder non-commutative endomorphisms via scalar `ring`. Quartic normal ordering is defined constructively on raw words (`quarticSeaWick`) by mapping creators and annihilators to sea quasiparticles $q^\dagger, q$, stable-sorting all $q^\dagger$ left of all $q$ with the inversion sign `(-1) ^ seaInversions w`, and proving the CAR evaluation identity (`quartic_sea_wick_identity`) with explicit contraction remainder `quarticContraction`.
2. **Hopping vs. Pairing Form (Lemma 17.3 & Appendix A07 §2):** With computational creators $C_\nu = \rho_{m,\nu}$ ($m > 0$) on both branches, the raw opposite-transfer inter-branch sum (17.2) evaluates to the number-conserving hopping form $C_R A_L + A_R C_L$ (`hoppingInterBranch`), whose oscillatory terms annihilate the bare ground state (`hopping_mode_kills_ground`). The solvable hyperbolic Luttinger model requires the pairing form $C_R C_L + A_R A_L$ (`pairingInterBranch`), which creates pairs from the bare ground state (`pairing_mode_ground_nonzero`). Both operators are formalized distinctly; Theorem 17.5 uses `pairingInterBranch` and `currentIntraBranch`.
3. **Exact Finite Sea-Wick Correction (Lemma 17.4a):** The raw intra-branch interaction $H_{4,\mathrm{raw}}$ differs from the chosen quadratic current interaction $H_{4,\mathrm{current}}$ by the diagonal one-body correction $-\frac{g_4}{2L}\sum_\nu Q_{M,\nu}$ (`seaWickCorrection`). We formalize `seaWickCorrection` with exact finite-band distance weights $1 + 2\min(M, -k)$ for $k \le 0$ and $1 + 2\min(M, k-1)$ for $k > 0$, state the ambient CAR identity `raw_intra_eq_current_sub_correction`, and connect $Q_{M,\nu}$ at full band ($M \ge h - 1$) to $2\hat{P}_\nu - \hat{N}_\nu$ (`sea_wick_correction_full_band`).
4. **Schrieffer-Wolff Perturbation Theory (Theorem 17.6 & Appendix A10):** The second-order effective Hamiltonian is formalized as an algebraic polynomial in $t$, paired with the $2\times 2$ counterexample (`sw_2x2_truncation_witness`) demonstrating that the second-order truncation $-4/9$ at $t = 2/3$ differs from the explicit eigenvalue $-1/3$, and the $3\times 3$ counterexample (`sw_3x3_no_iff_witness`) demonstrating that $P[S_1, V]P = 0$ does not imply $PVQ = 0$.

## Design and scope

### Carriers and ambient algebras
- **Multi-species CAR carrier:** All fermionic and density operators act on `A05.FockSpace σ h` via the endomorphism algebra `A05.Operators σ h = Module.End ℂ (A05.FockSpace σ h)`. Two-branch models are parameterized by `branches : A06.Branches σ` (`rightSpecies`, `leftSpecies`, `distinct`).
- **Band and non-wrapping transfer domain:** Momentum modes belong to `Ch01.Band (2 * h)` ($L = 2h$). Transfer momenta $m$ are summed over `Finset.Icc (-(M : ℤ)) (M : ℤ)` or positive modes `Finset.Icc 1 M`. Non-wrapping band pairs $(k+m, k)$ are indexed by `A04.validPairs (2 * h) m`, enforcing that both $k$ and $k+m$ remain inside `Ch01.Band (2 * h)` without modular wrap.
- **Sea occupation and normal ordering:** The Dirac sea indicator `seaIndicator h k` equals `1` for `k.val ≤ 0` and `0` for `k.val > 0`. Sea-normal-ordered density modes `seaNormalRho h ν m` coincide with `A05.rho h ν m` for $m \neq 0$ and equal `A05.chargeObservable h ν` at $m = 0$.

### Budgets, margins, and admissibility
- **Admissibility:** `A05.admissible h Ns` requires every species charge $N_\nu$ to lie within the half-band capacity.
- **Current and Bogoliubov margins:** Single-mode Bogoliubov expansion (`bogoliubov_expansion_on_budget`) and CCR preservation (`bogoliubov_ccr_on_budget`) on `A05.jointBudget h Ns K` require `A06.branchMargins h M K Ns branches`, i.e., $2M + K + \vert{}N_\nu\vert{} \le h$ on both branches.
- **Sugawara margin:** The free kinetic Sugawara reduction (`free_fermion_eq_sugawara_on_budget` and `luttinger_hamiltonian_on_budget`) uses `sugawaraMargin h M K Ns branches`, requiring cutoff completeness $K \le M$ and strict half-band interiority $K + \vert{}N_\nu\vert{} < h$ on both branches. This sharper finite-edge claim requires a new Phase B argument: installed `Ch12.sugawara_equivalence` and `sugawara_relative_hamiltonian` supply the sufficient bound $2K+|N_\nu|\le h$, not this sharper contract.
- **Ambient identities:** The sea-Wick reduction (`raw_intra_eq_current_sub_correction`), hopping reduction (`raw_inter_eq_hopping`), and chosen Luttinger rearrangement (`luttinger_chosen_eq_bosonized`) hold as exact operator identities on all of `A05.Operators σ h` with no budget restriction.

### Proof dependencies and module layout
1. `BosonizeStubs/A07InteractionsAndBogoliubov.lean`: Imports `Bosonize`. Defines sea-Wick normal ordering, $Q_{M,\nu}$, $H_{4,\mathrm{raw}}$ vs. $H_{4,\mathrm{current}}$, $H_{2,\mathrm{raw}}$ vs. $H_{2,\mathrm{hop}}$ and $H_{2,\mathrm{pair}}$, `HyperbolicParams`, and single-mode Bogoliubov transformations.
2. `BosonizeStubs/A10DiscreteSchriefferWolff.lean`: Imports `Bosonize` and `A07InteractionsAndBogoliubov`. Defines energy-shell projectors `lowShellProj` and `highShellProj`, the mode-1 vs. shell-2 distinction witness, the non-resonant generator matrix `swGeneratorMatrix`, forward off-block vanishing lemmas, and explicit $2\times 2$ and $3\times 3$ matrix counterexamples.
3. `BosonizeStubs/Ch17LuttingerModels.lean`: Imports `Bosonize`, `A07InteractionsAndBogoliubov`, and `A10DiscreteSchriefferWolff`. Combines the free Sugawara kinetic operator, chosen current and pairing interactions, chemical potential $\mu = \pi v_F / L$, and exact zero-mode energy to establish Theorem 17.5 and its concrete non-vacuity witness.

## Lean draft

```lean
import Bosonize

-- BEGIN_MODULE BosonizeStubs/A07InteractionsAndBogoliubov.lean
namespace Bosonize.A07Interactions

open scoped BigOperators Classical

section ScalarAndSyntax

def seaIndicator (h : ℕ) (k : Ch01.Band (2 * h)) : ℂ :=
  if k.val ≤ 0 then 1 else 0

def creatorToSeaLetter (h : ℕ) (k : Ch01.Band (2 * h)) :
    Bool × Ch01.Band (2 * h) :=
  (decide (0 < k.val), k)

def annihilatorToSeaLetter (h : ℕ) (k : Ch01.Band (2 * h)) :
    Bool × Ch01.Band (2 * h) :=
  (decide (k.val ≤ 0), k)

def seaInversions (h : ℕ) : List (Bool × Ch01.Band (2 * h)) → ℕ
  | [] => 0
  | (true, _) :: rest => seaInversions h rest
  | (false, _) :: rest => (rest.filter (fun l => l.1)).length + seaInversions h rest

def bilinearWord (h : ℕ) (a b : Ch01.Band (2 * h)) :
    List (Bool × Ch01.Band (2 * h)) :=
  [creatorToSeaLetter h a, annihilatorToSeaLetter h b]

def quarticWord (h : ℕ) (a b c d : Ch01.Band (2 * h)) :
    List (Bool × Ch01.Band (2 * h)) :=
  [creatorToSeaLetter h a, annihilatorToSeaLetter h b,
   creatorToSeaLetter h c, annihilatorToSeaLetter h d]

def seaWickWeight (h M : ℕ) (k : Ch01.Band (2 * h)) : ℤ :=
  if k.val ≤ 0 then 1 + 2 * min (M : ℤ) (-k.val)
  else 1 + 2 * min (M : ℤ) (k.val - 1)

def oppositeOrientation : A06.Orientation → A06.Orientation
  | .right => .left
  | .left => .right

structure HyperbolicParams (v1 v2 : ℝ) where
  u : ℝ
  c : ℝ
  s : ℝ
  u_pos : 0 < u
  c_pos : 0 < c
  u_sq : u ^ 2 = v1 ^ 2 - v2 ^ 2
  hyperbolic_id : c ^ 2 - s ^ 2 = 1
  match_v1 : v1 = u * (c ^ 2 + s ^ 2)
  match_v2 : v2 = 2 * u * c * s

theorem hyperbolic_params_exist (v1 v2 : ℝ) (hstab : |v2| < v1) :
    ∃ u c s : ℝ, 0 < u ∧ u ^ 2 = v1 ^ 2 - v2 ^ 2 ∧
      c ^ 2 - s ^ 2 = 1 ∧ v1 = u * (c ^ 2 + s ^ 2) ∧
      v2 = 2 * u * c * s := by sorry

end ScalarAndSyntax

section Operators

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

noncomputable def seaQuasiAnnihilator (h : ℕ) (ν : σ)
    (k : Ch01.Band (2 * h)) : A05.Operators σ h :=
  if k.val ≤ 0 then A05.creation h ν k else A05.annihilation h ν k

noncomputable def seaQuasiCreator (h : ℕ) (ν : σ)
    (k : Ch01.Band (2 * h)) : A05.Operators σ h :=
  if k.val ≤ 0 then A05.annihilation h ν k else A05.creation h ν k

noncomputable def evalSeaLetter (h : ℕ) (ν : σ)
    (l : Bool × Ch01.Band (2 * h)) : A05.Operators σ h :=
  if l.1 then seaQuasiCreator h ν l.2 else seaQuasiAnnihilator h ν l.2

noncomputable def seaWickWord (h : ℕ) (ν : σ)
    (w : List (Bool × Ch01.Band (2 * h))) : A05.Operators σ h :=
  let creators := w.filter (fun l => l.1)
  let annihilators := w.filter (fun l => !l.1)
  ((-1 : ℂ) ^ seaInversions h w) •
    (((creators ++ annihilators).map (evalSeaLetter h ν)).prod)

noncomputable def numberOp (h : ℕ) (ν : σ)
    (k : Ch01.Band (2 * h)) : A05.Operators σ h :=
  A05.creation h ν k * A05.annihilation h ν k

noncomputable def seaSubtractedNumber (h : ℕ) (ν : σ)
    (k : Ch01.Band (2 * h)) : A05.Operators σ h :=
  numberOp h ν k - seaIndicator h k • (1 : A05.Operators σ h)

noncomputable def seaNormalBilinear (h : ℕ) (ν : σ)
    (a b : Ch01.Band (2 * h)) : A05.Operators σ h :=
  A05.creation h ν a * A05.annihilation h ν b -
    (if a = b then seaIndicator h a else 0) • (1 : A05.Operators σ h)

noncomputable def seaNormalRho (h : ℕ) (ν : σ) (m : ℤ) :
    A05.Operators σ h :=
  ∑ z ∈ A04.validPairs (2 * h) m, seaNormalBilinear h ν z.1 z.2

noncomputable def quarticSeaWick (h : ℕ) (ν : σ)
    (a b c d : Ch01.Band (2 * h)) : A05.Operators σ h :=
  seaWickWord h ν (quarticWord h a b c d)

noncomputable def quarticContraction (h : ℕ) (ν : σ)
    (k p : Ch01.Band (2 * h)) : A05.Operators σ h :=
  seaIndicator h p • seaSubtractedNumber h ν k -
    (1 - seaIndicator h k) • seaSubtractedNumber h ν p -
    (seaIndicator h p * (1 - seaIndicator h k)) • (1 : A05.Operators σ h)

noncomputable def seaWickTerm (h M : ℕ) (ν : σ)
    (k : Ch01.Band (2 * h)) : A05.Operators σ h :=
  if k.val ≤ 0 then
    (seaWickWeight h M k : ℂ) • ((1 : A05.Operators σ h) - numberOp h ν k)
  else
    (seaWickWeight h M k : ℂ) • numberOp h ν k

noncomputable def seaWickCorrection (h M : ℕ) (ν : σ) :
    A05.Operators σ h :=
  ∑ k : Ch01.Band (2 * h), seaWickTerm h M ν k

noncomputable def computationalMomentum (h : ℕ) (ν : σ) :
    A05.Operators σ h :=
  ∑ k : Ch01.Band (2 * h), (k.val : ℂ) • seaSubtractedNumber h ν k

noncomputable def speciesRawIntra (h M : ℕ) (ν : σ) :
    A05.Operators σ h :=
  ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
    ∑ z ∈ A04.validPairs (2 * h) m,
      ∑ w ∈ A04.validPairs (2 * h) (-m),
        quarticSeaWick h ν z.1 z.2 w.1 w.2

noncomputable def rawIntraBranch (h M : ℕ) (g4 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  ((g4 : ℂ) / (2 * ((2 * h : ℕ) : ℂ))) •
    (speciesRawIntra h M branches.rightSpecies +
      speciesRawIntra h M branches.leftSpecies)

noncomputable def speciesCurrentIntra (h M : ℕ) (ν : σ) :
    A05.Operators σ h :=
  (2 : ℂ) • (∑ m ∈ Finset.Icc 1 M,
    A05.rho h ν (m : ℤ) * A05.rho h ν (-(m : ℤ))) +
    A05.chargeObservable h ν * A05.chargeObservable h ν

noncomputable def currentIntraBranch (h M : ℕ) (g4 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  ((g4 : ℂ) / (2 * ((2 * h : ℕ) : ℂ))) •
    (speciesCurrentIntra h M branches.rightSpecies +
      speciesCurrentIntra h M branches.leftSpecies)

noncomputable def rawInterBranch (h M : ℕ) (g2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  ((g2 : ℂ) / ((2 * h : ℕ) : ℂ)) •
    ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      seaNormalRho h branches.rightSpecies m *
        seaNormalRho h branches.leftSpecies (-m)

noncomputable def hoppingInterBranch (h M : ℕ) (g2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let r := branches.rightSpecies
  let l := branches.leftSpecies
  ((g2 : ℂ) / ((2 * h : ℕ) : ℂ)) •
    (A05.chargeObservable h r * A05.chargeObservable h l +
      ∑ m ∈ Finset.Icc 1 M,
        (A05.rho h r (m : ℤ) * A05.rho h l (-(m : ℤ)) +
          A05.rho h r (-(m : ℤ)) * A05.rho h l (m : ℤ)))

noncomputable def pairingInterBranch (h M : ℕ) (g2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let r := branches.rightSpecies
  let l := branches.leftSpecies
  ((g2 : ℂ) / ((2 * h : ℕ) : ℂ)) •
    (A05.chargeObservable h r * A05.chargeObservable h l +
      ∑ m ∈ Finset.Icc 1 M,
        (A05.rho h r (m : ℤ) * A05.rho h l (m : ℤ) +
          A05.rho h r (-(m : ℤ)) * A05.rho h l (-(m : ℤ))))

noncomputable def hoppingMode (h m : ℕ) (v1 v2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let r := branches.rightSpecies
  let l := branches.leftSpecies
  (v1 : ℂ) • (A05.rho h r (m : ℤ) * A05.rho h r (-(m : ℤ)) +
    A05.rho h l (m : ℤ) * A05.rho h l (-(m : ℤ))) +
  (v2 : ℂ) • (A05.rho h r (m : ℤ) * A05.rho h l (-(m : ℤ)) +
    A05.rho h l (m : ℤ) * A05.rho h r (-(m : ℤ)))

noncomputable def pairingMode (h m : ℕ) (v1 v2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let r := branches.rightSpecies
  let l := branches.leftSpecies
  (v1 : ℂ) • (A05.rho h r (m : ℤ) * A05.rho h r (-(m : ℤ)) +
    A05.rho h l (m : ℤ) * A05.rho h l (-(m : ℤ))) +
  (v2 : ℂ) • (A05.rho h r (m : ℤ) * A05.rho h l (m : ℤ) +
    A05.rho h r (-(m : ℤ)) * A05.rho h l (-(m : ℤ)))

noncomputable def bogoliubovCreator (h m : ℕ) (c s : ℝ)
    (branches : A06.Branches σ) (η : A06.Orientation) :
    A05.Operators σ h :=
  (c : ℂ) • A05.rho h (A06.speciesOf branches η) (m : ℤ) +
    (s : ℂ) • A05.rho h (A06.speciesOf branches (oppositeOrientation η)) (-(m : ℤ))

noncomputable def bogoliubovAnnihilator (h m : ℕ) (c s : ℝ)
    (branches : A06.Branches σ) (η : A06.Orientation) :
    A05.Operators σ h :=
  (c : ℂ) • A05.rho h (A06.speciesOf branches η) (-(m : ℤ)) +
    (s : ℂ) • A05.rho h (A06.speciesOf branches (oppositeOrientation η)) (m : ℤ)

noncomputable def dressedModeNumber (h m : ℕ) (u c s : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  (u : ℂ) • (bogoliubovCreator h m c s branches .right *
      bogoliubovAnnihilator h m c s branches .right +
    bogoliubovCreator h m c s branches .left *
      bogoliubovAnnihilator h m c s branches .left)

lemma sea_normal_bilinear_diag (h : ℕ) (ν : σ)
    (k : Ch01.Band (2 * h)) :
    seaNormalBilinear h ν k k =
      if k.val ≤ 0 then -(A05.annihilation h ν k * A05.creation h ν k)
      else A05.creation h ν k * A05.annihilation h ν k := by sorry

lemma sea_normal_rho_nonzero (h : ℕ) (ν : σ) (m : ℤ) (hm : m ≠ 0) :
    seaNormalRho h ν m = A05.rho h ν m := by sorry

lemma sea_normal_rho_zero (h : ℕ) (ν : σ) :
    seaNormalRho h ν 0 = A05.chargeObservable h ν := by sorry

lemma quartic_sea_wick_identity (h : ℕ) (ν : σ) (m : ℤ)
    (z w : Ch01.Band (2 * h) × Ch01.Band (2 * h))
    (hz : z ∈ A04.validPairs (2 * h) m)
    (hw : w ∈ A04.validPairs (2 * h) (-m)) :
    quarticSeaWick h ν z.1 z.2 w.1 w.2 =
      seaNormalBilinear h ν z.1 z.2 * seaNormalBilinear h ν w.1 w.2 +
        if w.2 = z.1 then quarticContraction h ν z.2 w.2 else 0 := by sorry

lemma quartic_sea_wick_zero_repeated (h : ℕ) (ν : σ)
    (k : Ch01.Band (2 * h)) :
    quarticSeaWick h ν k k k k = 0 ∧
      seaNormalBilinear h ν k k * seaNormalBilinear h ν k k +
        quarticContraction h ν k k = 0 := by sorry

lemma species_raw_intra_eq_current_sub_correction (h M : ℕ) (ν : σ) :
    speciesRawIntra h M ν =
      speciesCurrentIntra h M ν - seaWickCorrection h M ν := by sorry

theorem raw_intra_eq_current_sub_correction (h M : ℕ) (g4 : ℝ)
    (branches : A06.Branches σ) :
    rawIntraBranch h M g4 branches =
      currentIntraBranch h M g4 branches -
        ((g4 : ℂ) / (2 * ((2 * h : ℕ) : ℂ))) •
          (seaWickCorrection h M branches.rightSpecies +
            seaWickCorrection h M branches.leftSpecies) := by sorry

lemma sea_wick_correction_ground_zero (h M : ℕ) (hh : 0 < h) (ν : σ) :
    seaWickCorrection h M ν (A05.groundKet h (fun _ : σ => 0)) = 0 := by sorry

lemma sea_wick_correction_full_band (h M : ℕ) (hh : 0 < h)
    (hM : h - 1 ≤ M) (ν : σ) :
    seaWickCorrection h M ν =
      (2 : ℂ) • computationalMomentum h ν - A05.chargeObservable h ν := by sorry

theorem raw_inter_eq_hopping (h M : ℕ) (g2 : ℝ)
    (branches : A06.Branches σ) :
    rawInterBranch h M g2 branches =
      hoppingInterBranch h M g2 branches := by sorry

lemma hopping_mode_kills_ground (h m : ℕ) (hh : 0 < h) (hm : 1 ≤ m)
    (Ns : σ → ℤ) (hN : A05.admissible h Ns)
    (branches : A06.Branches σ) :
    (A05.rho h branches.rightSpecies (m : ℤ) *
        A05.rho h branches.leftSpecies (-(m : ℤ)) +
      A05.rho h branches.rightSpecies (-(m : ℤ)) *
        A05.rho h branches.leftSpecies (m : ℤ))
      (A05.groundKet h Ns) = 0 := by sorry

lemma pairing_mode_ground_nonzero (h M m : ℕ) (hh : 0 < h)
    (hm : 1 ≤ m) (hcut : m ≤ M) (Ns : σ → ℤ) (hN : A05.admissible h Ns)
    (branches : A06.Branches σ)
    (hmargin : A06.branchMargins h M m Ns branches) :
    (A05.rho h branches.rightSpecies (m : ℤ) *
        A05.rho h branches.leftSpecies (m : ℤ) +
      A05.rho h branches.rightSpecies (-(m : ℤ)) *
        A05.rho h branches.leftSpecies (-(m : ℤ)))
      (A05.groundKet h Ns) ≠ 0 := by sorry

lemma hopping_mode_self_adjoint (h m : ℕ) (v1 v2 : ℝ)
    (branches : A06.Branches σ) :
    LinearMap.adjoint (hoppingMode h m v1 v2 branches) =
      hoppingMode h m v1 v2 branches := by sorry

lemma pairing_mode_self_adjoint (h m : ℕ) (v1 v2 : ℝ)
    (branches : A06.Branches σ) :
    LinearMap.adjoint (pairingMode h m v1 v2 branches) =
      pairingMode h m v1 v2 branches := by sorry

lemma bogoliubov_creator_adjoint (h m : ℕ) (c s : ℝ)
    (branches : A06.Branches σ) (η : A06.Orientation) :
    LinearMap.adjoint (bogoliubovCreator h m c s branches η) =
      bogoliubovAnnihilator h m c s branches η := by sorry

theorem bogoliubov_expansion_on_budget (h M K m : ℕ) (hh : 0 < h)
    (hm : 1 ≤ m) (hcut : m ≤ M) (v1 v2 : ℝ)
    (hp : HyperbolicParams v1 v2) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    dressedModeNumber h m hp.u hp.c hp.s branches v =
      pairingMode h m v1 v2 branches v +
        ((2 * hp.u * hp.s ^ 2 * (m : ℝ) : ℝ) : ℂ) • v := by sorry

theorem bogoliubov_ccr_on_budget (h M K m : ℕ) (hh : 0 < h)
    (hm : 1 ≤ m) (hcut : m ≤ M) (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1)
    (branches : A06.Branches σ) (η : A06.Orientation)
    (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator
        (bogoliubovAnnihilator h m c s branches η)
        (bogoliubovCreator h m c s branches η) v =
      (m : ℂ) • v := by sorry

end Operators

end Bosonize.A07Interactions
-- END_MODULE BosonizeStubs/A07InteractionsAndBogoliubov.lean

-- BEGIN_MODULE BosonizeStubs/A10DiscreteSchriefferWolff.lean
namespace Bosonize.A10

open scoped BigOperators Classical

section MatrixModels

noncomputable def swGeneratorMatrix {ι : Type*}
    (inLow : ι → Bool) (E : ι → ℝ) (Voff : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  fun i j =>
    if inLow i ≠ inLow j ∧ Voff i j ≠ 0 then
      Voff i j / ((E i - E j : ℝ) : ℂ)
    else 0

noncomputable def diagEnergyMatrix {ι : Type*} [DecidableEq ι]
    (E : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => ((E i : ℝ) : ℂ))

def nonResonant {ι : Type*} (inLow : ι → Bool) (E : ι → ℝ)
    (Voff : Matrix ι ι ℂ) : Prop :=
  ∀ i j : ι, inLow i ≠ inLow j → Voff i j ≠ 0 → E i ≠ E j

def swCounterH0_2x2 : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 1 ∧ j = 1 then 1 else 0

def swCounterV_2x2 : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i ≠ j then 1 else 0

def swCounterS1_2x2 : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 ∧ j = 1 then -1 else if i = 1 ∧ j = 0 then 1 else 0

def swCounterP_2x2 : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

def swCounterH0_3x3 : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j =>
    if i = j then
      if i = 0 then 0 else if i = 1 then -1 else 1
    else 0

def swCounterP_3x3 : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

def swCounterQ_3x3 : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => if i = j ∧ (i = 1 ∨ i = 2) then 1 else 0

def swCounterV_3x3 : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j =>
    if (i = 0 ∧ (j = 1 ∨ j = 2)) ∨ ((i = 1 ∨ i = 2) ∧ j = 0) then 1
    else 0

def swCounterS1_3x3 : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j =>
    if i = 0 ∧ j = 1 then 1
    else if i = 0 ∧ j = 2 then -1
    else if i = 1 ∧ j = 0 then -1
    else if i = 2 ∧ j = 0 then 1
    else 0

theorem sw_generator_commutator_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (inLow : ι → Bool) (E : ι → ℝ) (Voff : Matrix ι ι ℂ)
    (hBlock : ∀ i j : ι, inLow i = inLow j → Voff i j = 0)
    (hNonRes : nonResonant inLow E Voff) :
    swGeneratorMatrix inLow E Voff * diagEnergyMatrix E -
      diagEnergyMatrix E * swGeneratorMatrix inLow E Voff = -Voff := by sorry

theorem sw_generator_skew_hermitian {ι : Type*}
    (inLow : ι → Bool) (E : ι → ℝ) (Voff : Matrix ι ι ℂ)
    (hHerm : Matrix.conjTranspose Voff = Voff) :
    Matrix.conjTranspose (swGeneratorMatrix inLow E Voff) =
      -swGeneratorMatrix inLow E Voff := by sorry

theorem sw_2x2_truncation_witness :
    swCounterS1_2x2 * swCounterH0_2x2 - swCounterH0_2x2 * swCounterS1_2x2 =
      -swCounterV_2x2 ∧
    (swCounterP_2x2 * (swCounterS1_2x2 * swCounterV_2x2 -
      swCounterV_2x2 * swCounterS1_2x2) * swCounterP_2x2) 0 0 = -2 ∧
    ((-((2 : ℚ) / 3) ^ 2 : ℚ) ≠ (-1 / 3 : ℚ)) := by sorry

theorem sw_3x3_no_iff_witness :
    swCounterS1_3x3 * swCounterH0_3x3 - swCounterH0_3x3 * swCounterS1_3x3 =
      -swCounterV_3x3 ∧
    swCounterP_3x3 * swCounterV_3x3 * swCounterQ_3x3 ≠ 0 ∧
    swCounterP_3x3 * (swCounterS1_3x3 * swCounterV_3x3 -
      swCounterV_3x3 * swCounterS1_3x3) * swCounterP_3x3 = 0 := by sorry

def swCounterEigenvector_2x2 : Fin 2 → ℂ :=
  fun i => if i = 0 then -2 else 1

theorem sw_2x2_exact_eigenpair :
    swCounterEigenvector_2x2 ≠ 0 ∧
      (swCounterH0_2x2 + ((2 : ℂ) / 3) • swCounterV_2x2).mulVec
        swCounterEigenvector_2x2 =
      ((-1 : ℂ) / 3) • swCounterEigenvector_2x2 := by sorry

end MatrixModels

section BudgetShells

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

def exactShellSet (h : ℕ) (Ns : σ → ℤ) (K : ℕ) :
    Set (A05.Occupation σ h) :=
  {S | (∀ ν, Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) = Ns ν) ∧
    Ch07.totalExcitation h S = (K : ℤ)}

noncomputable def lowShellProj (h : ℕ) (Ns : σ → ℤ) (K : ℕ) :
    A05.Operators σ h :=
  Ch14.projection h Ns (K - 1)

noncomputable def highShellProj (h : ℕ) (Ns : σ → ℤ) (K : ℕ) :
    A05.Operators σ h :=
  letI : DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq
  A03.coordinateProjection (exactShellSet h Ns K)

noncomputable def doubleModeOneKet (h : ℕ) (Ns : σ → ℤ) (ν : σ) :
    A05.FockSpace σ h :=
  A05.rho h ν 1 (A05.rho h ν 1 (A05.groundKet h Ns))

noncomputable def diagPart (h : ℕ) (P Q V : A05.Operators σ h) :
    A05.Operators σ h :=
  P * V * P + Q * V * Q

noncomputable def offDiagPart (h : ℕ) (P Q V : A05.Operators σ h) :
    A05.Operators σ h :=
  P * V * Q + Q * V * P

noncomputable def swSecondOrderCorrection (h : ℕ)
    (P S1 V : A05.Operators σ h) : A05.Operators σ h :=
  ((2 : ℂ)⁻¹) • (P * A02.commutator S1 V * P)

noncomputable def swEffectiveSecondOrder (h : ℕ)
    (P H0 V S1 : A05.Operators σ h) (t : ℝ) : A05.Operators σ h :=
  P * H0 * P + (t : ℂ) • (P * V * P) +
    ((t : ℂ) ^ 2) • swSecondOrderCorrection h P S1 V

noncomputable def bchSecondOrderPolynomial (h : ℕ)
    (H0 V S1 : A05.Operators σ h) (t : ℝ) : A05.Operators σ h :=
  H0 + (t : ℂ) • (V + A02.commutator S1 H0) +
    ((t : ℂ) ^ 2) • (A02.commutator S1 V +
      ((2 : ℂ)⁻¹) • A02.commutator S1 (A02.commutator S1 H0))

theorem sw_compressed_bch_second_order (h : ℕ)
    (P Q H0 V S1 : A05.Operators σ h) (t : ℝ)
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hPartition : P + Q = 1) (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (hBaseline : A02.commutator P H0 = 0)
    (hSpp : P * S1 * P = 0) (hSqq : Q * S1 * Q = 0)
    (hGenerator : A02.commutator S1 H0 = -offDiagPart h P Q V) :
    P * bchSecondOrderPolynomial h H0 V S1 t * P =
      swEffectiveSecondOrder h P H0 V S1 t := by sorry

lemma shell_proj_partition (h K : ℕ) (hK : 1 ≤ K) (Ns : σ → ℤ) :
    lowShellProj h Ns K + highShellProj h Ns K =
      Ch14.projection h Ns K := by sorry

lemma shell_proj_orthogonal (h K : ℕ) (hK : 1 ≤ K) (Ns : σ → ℤ) :
    lowShellProj h Ns K * highShellProj h Ns K = 0 ∧
      highShellProj h Ns K * lowShellProj h Ns K = 0 := by sorry

lemma shell_proj_self_adjoint (h K : ℕ) (Ns : σ → ℤ) :
    LinearMap.adjoint (lowShellProj h Ns K) = lowShellProj h Ns K ∧
      LinearMap.adjoint (highShellProj h Ns K) = highShellProj h Ns K := by sorry

lemma energy_shell_discards_double_mode_one (h : ℕ) (hh : 2 ≤ h)
    (Ns : σ → ℤ) (hN : A05.admissible h Ns) (ν : σ)
    (hR2 : A05.r2 h 2 Ns) :
    doubleModeOneKet h Ns ν ∈ A05.jointBudget h Ns 2 ∧
      doubleModeOneKet h Ns ν ≠ 0 ∧
      lowShellProj h Ns 2 (doubleModeOneKet h Ns ν) = 0 ∧
      highShellProj h Ns 2 (doubleModeOneKet h Ns ν) =
        doubleModeOneKet h Ns ν := by sorry

theorem sw_off_zero_implies_effective_exact (h : ℕ)
    (P Q H0 V : A05.Operators σ h) (t : ℝ)
    (hPVQ : P * V * Q = 0) (hQVP : Q * V * P = 0) :
    offDiagPart h P Q V = 0 ∧
      swSecondOrderCorrection h P (0 : A05.Operators σ h) V = 0 ∧
      swEffectiveSecondOrder h P H0 V (0 : A05.Operators σ h) t =
        P * H0 * P + (t : ℂ) • (P * V * P) := by sorry

end BudgetShells

end Bosonize.A10
-- END_MODULE BosonizeStubs/A10DiscreteSchriefferWolff.lean

-- BEGIN_MODULE BosonizeStubs/Ch17LuttingerModels.lean
namespace Bosonize.Ch17

open scoped BigOperators Classical

section ScalarParameters

noncomputable def v1Velocity (vF g4 : ℝ) : ℝ :=
  vF + g4 / (2 * Real.pi)

noncomputable def v2Velocity (g2 : ℝ) : ℝ :=
  g2 / (2 * Real.pi)

noncomputable def canonicalMu (h : ℕ) (vF : ℝ) : ℝ :=
  Real.pi * vF / ((2 * h : ℕ) : ℝ)

def sugawaraMargin {σ : Type*} (h M K : ℕ) (Ns : σ → ℤ)
    (branches : A06.Branches σ) : Prop :=
  K ≤ M ∧
    (K : ℤ) + |Ns branches.rightSpecies| < (h : ℤ) ∧
    (K : ℤ) + |Ns branches.leftSpecies| < (h : ℤ)

noncomputable def zeroModeEnergyScalar {σ : Type*} (h : ℕ)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) : ℝ :=
  let L : ℝ := ((2 * h : ℕ) : ℝ)
  let nr : ℝ := (Ns branches.rightSpecies : ℝ)
  let nl : ℝ := (Ns branches.leftSpecies : ℝ)
  (2 * Real.pi * vF / L) * (nr * (nr + 1) / 2 + nl * (nl + 1) / 2) +
    (g4 / (2 * L)) * (nr ^ 2 + nl ^ 2) +
    (g2 / L) * nr * nl -
    mu * (nr + nl)

noncomputable def symmetricZeroModeScalar {σ : Type*} (h : ℕ)
    (vF g4 g2 : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) : ℝ :=
  let L : ℝ := ((2 * h : ℕ) : ℝ)
  let nr : ℝ := (Ns branches.rightSpecies : ℝ)
  let nl : ℝ := (Ns branches.leftSpecies : ℝ)
  (Real.pi * v1Velocity vF g4 / L) * (nr ^ 2 + nl ^ 2) +
    (g2 / L) * nr * nl

lemma zero_mode_scalar_canonical_mu {σ : Type*} (h : ℕ) (vF g4 g2 : ℝ)
    (branches : A06.Branches σ) (Ns : σ → ℤ) :
    zeroModeEnergyScalar h vF g4 g2 (canonicalMu h vF) branches Ns =
      symmetricZeroModeScalar h vF g4 g2 branches Ns := by sorry

end ScalarParameters

section LuttingerHamiltonians

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

noncomputable def chemicalPotentialOp (h : ℕ) (mu : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  (mu : ℂ) • (A05.chargeObservable h branches.rightSpecies +
    A05.chargeObservable h branches.leftSpecies)

noncomputable def freeSugawaraKinetic (h M : ℕ) (vF : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let r := branches.rightSpecies
  let l := branches.leftSpecies
  let prefactor : ℂ := ((2 * Real.pi * vF : ℝ) : ℂ) / ((2 * h : ℕ) : ℂ)
  prefactor • (Ch16.sugawara h M branches +
    ((2 : ℂ)⁻¹) • (A05.chargeObservable h r * (A05.chargeObservable h r + 1) +
      A05.chargeObservable h l * (A05.chargeObservable h l + 1)))

noncomputable def freeFermionKinetic (h : ℕ) (vF : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let prefactor : ℂ := ((2 * Real.pi * vF : ℝ) : ℂ) / ((2 * h : ℕ) : ℂ)
  prefactor •
    (A07Interactions.computationalMomentum h branches.rightSpecies +
      A07Interactions.computationalMomentum h branches.leftSpecies)

noncomputable def zeroModeEnergyOp (h : ℕ) (vF g4 g2 mu : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let L : ℂ := ((2 * h : ℕ) : ℂ)
  let nr := A05.chargeObservable h branches.rightSpecies
  let nl := A05.chargeObservable h branches.leftSpecies
  (((2 * Real.pi * vF : ℝ) : ℂ) / L) •
      (((2 : ℂ)⁻¹) • (nr * (nr + 1) + nl * (nl + 1))) +
    ((g4 : ℂ) / (2 * L)) • (nr * nr + nl * nl) +
    ((g2 : ℂ) / L) • (nr * nl) -
    chemicalPotentialOp h mu branches

noncomputable def luttingerOscillatorOp (h M : ℕ) (vF g4 g2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  (((2 * Real.pi : ℝ) : ℂ) / ((2 * h : ℕ) : ℂ)) •
    ∑ m ∈ Finset.Icc 1 M,
      A07Interactions.pairingMode h m
        (v1Velocity vF g4) (v2Velocity g2) branches

noncomputable def luttingerBosonizedHamiltonian (h M : ℕ)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) :
    A05.Operators σ h :=
  luttingerOscillatorOp h M vF g4 g2 branches +
    zeroModeEnergyOp h vF g4 g2 mu branches

noncomputable def luttingerChosenModel (h M : ℕ)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) :
    A05.Operators σ h :=
  freeSugawaraKinetic h M vF branches +
    A07Interactions.currentIntraBranch h M g4 branches +
    A07Interactions.pairingInterBranch h M g2 branches -
    chemicalPotentialOp h mu branches

noncomputable def luttingerFermionChosenModel (h M : ℕ)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) :
    A05.Operators σ h :=
  freeFermionKinetic h vF branches +
    A07Interactions.currentIntraBranch h M g4 branches +
    A07Interactions.pairingInterBranch h M g2 branches -
    chemicalPotentialOp h mu branches

theorem luttinger_chosen_eq_bosonized (h M : ℕ) (vF g4 g2 mu : ℝ)
    (branches : A06.Branches σ) :
    luttingerChosenModel h M vF g4 g2 mu branches =
      luttingerBosonizedHamiltonian h M vF g4 g2 mu branches := by sorry

lemma zero_mode_op_on_budget (h K : ℕ) (vF g4 g2 mu : ℝ)
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    zeroModeEnergyOp h vF g4 g2 mu branches v =
      (zeroModeEnergyScalar h vF g4 g2 mu branches Ns : ℂ) • v := by sorry

theorem free_fermion_eq_sugawara_on_budget (h M K : ℕ) (hh : 0 < h)
    (vF : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hSug : sugawaraMargin h M K Ns branches)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    freeFermionKinetic h vF branches v =
      freeSugawaraKinetic h M vF branches v := by sorry

theorem luttinger_hamiltonian_on_budget (h M K : ℕ) (hh : 0 < h)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hSug : sugawaraMargin h M K Ns branches)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    luttingerFermionChosenModel h M vF g4 g2 mu branches v =
      luttingerOscillatorOp h M vF g4 g2 branches v +
        (zeroModeEnergyScalar h vF g4 g2 mu branches Ns : ℂ) • v := by sorry

theorem luttinger_hamiltonian_canonical_mu_on_budget (h M K : ℕ) (hh : 0 < h)
    (vF g4 g2 : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hSug : sugawaraMargin h M K Ns branches)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    luttingerFermionChosenModel h M vF g4 g2 (canonicalMu h vF) branches v =
      luttingerOscillatorOp h M vF g4 g2 branches v +
        (symmetricZeroModeScalar h vF g4 g2 branches Ns : ℂ) • v := by sorry

theorem luttinger_raw_intra_on_budget (h M K : ℕ) (hh : 0 < h)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hSug : sugawaraMargin h M K Ns branches)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    (freeFermionKinetic h vF branches +
      A07Interactions.rawIntraBranch h M g4 branches +
      A07Interactions.pairingInterBranch h M g2 branches -
      chemicalPotentialOp h mu branches) v =
      luttingerOscillatorOp h M vF g4 g2 branches v +
        (zeroModeEnergyScalar h vF g4 g2 mu branches Ns : ℂ) • v -
        (((g4 : ℂ) / (2 * ((2 * h : ℕ) : ℂ))) •
          (A07Interactions.seaWickCorrection h M branches.rightSpecies +
            A07Interactions.seaWickCorrection h M branches.leftSpecies)) v := by sorry

theorem concrete_luttinger_witness :
    let Ns : Fin 2 → ℤ := fun _ => 0
    A05.admissible 8 Ns ∧
      A06.branchMargins 8 2 2 Ns Ch16.standardBranches ∧
      sugawaraMargin 8 2 2 Ns Ch16.standardBranches ∧
      A05.groundKet 8 Ns ∈ A05.jointBudget 8 Ns 2 ∧
      A05.groundKet 8 Ns ≠ 0 ∧
      luttingerBosonizedHamiltonian 8 2 1 (6 * Real.pi) (6 * Real.pi)
        (canonicalMu 8 1) Ch16.standardBranches (A05.groundKet 8 Ns) ≠ 0 := by sorry

end LuttingerHamiltonians

end Bosonize.Ch17
-- END_MODULE BosonizeStubs/Ch17LuttingerModels.lean
```

## Companion notebook

### 1. Quartic Sea-Wick Ordering and the Finite Diagonal Correction $Q_{M,\nu}$
On the finite band $\Lambda^* = \mathrm{Band}(2h)$, the Dirac sea is $S_0 = \{k \in \Lambda^* : k \le 0\}$ with indicator $s_k = 1_{k \le 0}$. Defining sea quasiparticle annihilators $q_k = c_k$ ($k > 0$) and $q_k = c_k^\dagger$ ($k \le 0$), every $q_k$ annihilates the Dirac sea ket $\vert{}\Omega\rangle = \vert{}\vec{0}\rangle_0$.

For a 4-fermion word $c_{k+m}^\dagger c_k c_{p-m}^\dagger c_p$ of a single species $\nu$ with both $(k+m, k) \in \mathrm{validPairs}(2h, m)$ and $(p-m, p) \in \mathrm{validPairs}(2h, -m)$, full sea-Wick normal ordering $:c_{k+m}^\dagger c_k c_{p-m}^\dagger c_p:$ moves all $q^\dagger$ letters left of all $q$ letters in stable order with the fermionic inversion sign $(-1)^{\mathrm{inv}}$, omitting contractions. Expanding the product of sea-normal-ordered bilinears $:c_{k+m}^\dagger c_k:\,:c_{p-m}^\dagger c_p:$ via the CAR anticommutator $c_i c_j^\dagger + c_j^\dagger c_i = \delta_{ij} I$ produces:
$$
:c_{k+m}^\dagger c_k c_{p-m}^\dagger c_p: = :c_{k+m}^\dagger c_k:\,:c_{p-m}^\dagger c_p: + \delta_{p, k+m}\big[s_p t_k - (1-s_k) t_p - s_p(1-s_k) I\big],
$$
where $t_k = n_k - s_k I$. Summing over $m \in [-M, M]$ and valid band pairs $(k+m, k)$ and $(p-m, p)$, the bilinear product sum combines with the exact finite-band commutator $[\rho_{-m,\nu}, \rho_{m,\nu}]$ and the $\pm m$ contraction terms to yield:
$$
\sum_{m=-M}^M \sum_{k,p} :c_{\nu,k+m}^\dagger c_{\nu,k} c_{\nu,p-m}^\dagger c_{\nu,p}: = 2\sum_{m=1}^M \rho_{m,\nu}\rho_{-m,\nu} + \hat{N}_\nu^2 - Q_{M,\nu},
$$
where $Q_{M,\nu} = \sum_{k \le 0}(1 + 2\min(M, -k))(I - n_{\nu k}) + \sum_{k > 0}(1 + 2\min(M, k-1))n_{\nu k}$. When $M \ge h - 1$, every distance within the half-band is accessible and $Q_{M,\nu} = 2\hat{P}_\nu - \hat{N}_\nu$.

### 2. Hopping vs. Pairing Inter-branch Models
Because even-degree bilinears of distinct species commute ($[\rho_{m,R}, \rho_{n,L}] = 0$), the raw opposite-transfer inter-branch interaction (17.2) factors directly into normal-ordered density modes:
$$
H_{2,\mathrm{raw}} = \frac{g_2}{L}\left[\hat{N}_R\hat{N}_L + \sum_{m=1}^M (\rho_{m,R}\rho_{-m,L} + \rho_{-m,R}\rho_{m,L})\right].
$$
With computational creators $C_\nu = \rho_{m,\nu}$ and annihilators $A_\nu = \rho_{-m,\nu}$ ($m > 0$) on both branches, this is the number-conserving hopping interaction $C_R A_L + A_R C_L$, which annihilates $\vert{}\vec{N}\rangle_0$. The hyperbolic Luttinger pairing Hamiltonian instead requires $C_R C_L + A_R A_L$ (`pairingInterBranch`), which creates pairs of opposite-branch excitations out of $\vert{}\vec{N}\rangle_0$.

### 3. Energy-Shell Schrieffer-Wolff Decomposition
The budget decomposition $\mathcal{B}_K = \mathcal{B}_{K-1} \oplus \mathcal{H}_K$ partitions states by total excitation energy $\sum_\nu \sum_{m \ge 1} m\, n_{m,\nu}$, not by single-mode index. In particular, at $K = 2$, the repeated mode-1 state $(\rho_{1,\nu})^2\vert{}\vec{N}\rangle_0$ has excitation energy $2$ and belongs to $\mathcal{H}_2$: it is discarded by the energy-shell projection $P_1$ onto $\mathcal{B}_1$ even though it contains no mode-2 factor.

Source map addition: `bchSecondOrderPolynomial` explicitly records the algebraic coefficients of conjugation through degree two. `sw_compressed_bch_second_order` identifies its compression with `swEffectiveSecondOrder` under complementary projectors, a block-diagonal baseline, an off-block generator, and its stated generator equation. This is a finite polynomial identity; no analytic exponential or remainder estimate is asserted. `sw_2x2_exact_eigenpair` supplies a genuine nonzero eigenvector at t=2/3 with eigenvalue -1/3, while `sw_2x2_truncation_witness` supplies the distinct truncation value -4/9. The eigenpair theorem does not by itself prove that this eigenvalue is the lower one or compare with an exact exponential rotation.

Companion correction: The second-order BCH polynomial is H0+t(V+[S1,H0])+t²([S1,V]+[S1,[S1,H0]]/2). Compression removes the first-order off-block part and the diagonal-perturbation contribution to the nested bracket, leaving PH0P+tPVP+t²P[S1,V]P/2. The explicit matrix eigenvector is (-2,1), whose image under H0+(2/3)V is (2/3,-1/3)=(-1/3)(-2,1). All new theorem contracts remain unproved Phase A obligations.


### Compiler acceptance evidence

Fresh local `make verify-a` passed with Lean 4.35.0-rc4 (commit c29b6dda4f7c20e3eeaa717c4e565663c5cfa364): 70 data declarations, 37 one-sorry theorem stubs. Every audited definition has only permitted standard axioms or no axioms; there are no data placeholders. The only compiler warnings are expected theorem placeholder warnings. The transaction runner will rebuild and repeat data auditing and strict locks before accepting these sources.

### Transport repair and independent Phase A review

The external browser response `response_json.md` was preserved byte for byte; original SHA-256: `7442ccdc7973290276f4fe639ac50b618e67239bb48c9496ef0f9611c48d2056`. Its malformed JSON mixed unescaped LaTeX with differently escaped newline layers and broken single-backtick Lean fences. Local recovery separated prose and Lean transport, reconstructed readable formulas against the source notes, and writes the final envelope using a JSON serializer with the original packet ID and base SHA. No payload commands were executed.

The installed Lean compiler identified a deterministic typeclass mismatch in `highShellProj`: product equality differed from the CAR carrier's captured equality. The definition now explicitly installs `(A05.speciesOrder h).toDecidableEq`, matching existing Core; no Core changes were made.

Independent review roles: `characters` reviewed the browser-authored A07 contracts and then the locally authored A10 supplement; `same_ccr` reviewed A10 and authored that supplement; `joint_ccr` independently reviewed CH17. The requested flash/pro models are unavailable in this session, so agents used the inherited available model. Primary reviewed the final integration. All verdicts pass after the A10 coverage correction. This is interface review, not proof completion.

A07: all 18 contracts passed review of sea-word ordering, CAR contraction, finite correction weights, endpoint/full-band relation, distinct hopping/pairing models, actual adjoints and Bogoliubov constant/sign. Exact finite CAR sanity checks at h=2 found no quartic failures and verified raw=current-Q for M=0..5; these finite checks are not general Lean proofs.

A10: review found that a polynomial definition alone did not supply a truncated-conjugation theorem, and a rational inequality alone did not supply an eigenvalue witness. The supplement adds `bchSecondOrderPolynomial`, `sw_compressed_bch_second_order`, `swCounterEigenvector_2x2`, and `sw_2x2_exact_eigenpair`. An independent reviewer checked the degree-two coefficient algebra and the nonzero eigenvector (-2,1). Generic complementary projectors satisfy P+Q=1 in that contract; the ambient shell projectors instead sum to the budget projector. Apply the generic identity only on a carrier/extension where its hypotheses actually hold. No analytic exponential identity, remainder bound, or lowest-eigenvalue assertion is claimed.

CH17: all eight contracts passed review of Hamiltonian coefficients, explicit zero modes, raw-Q correction and witness nonzeroness. The sharper Sugawara bound K+|Nν|<h remains a new Phase B proof obligation; installed Core supplies only the sufficient bound 2K+|Nν|≤h. Independent finite CAR occupation checks passed 133 qualifying cases for h=1..5, without establishing a general Lean proof. The concrete h=8,M=K=2 witness meets branch margins 6≤8 and Sugawara margin 2<8, with stable velocities v1=4,v2=3. Distinct excitation degrees prevent its creator-pair terms cancelling.

The advisory `docs/stub_suggestion/` and `docs/proof_suggestion/` directories are absent. Source reconciliation used the current CH17 note, appendices A07/A10, TOC and installed frozen Core. All 37 theorem contracts remain one-sorry Phase A stubs. Definitions must pass fresh data axiom auditing before acceptance; standard axioms are `propext`, `Classical.choice`, and `Quot.sound`. Proof verification, zero-placeholder theorem auditing and promotion belong to later phases, which are outside this request.

## Review obligations

1. **Audit of exact vs. chosen interaction models:** Verify that `rawIntraBranch` ($H_{4,\mathrm{raw}}$) and `currentIntraBranch` ($H_{4,\mathrm{current}}$) are kept distinct, related by `raw_intra_eq_current_sub_correction` via `seaWickCorrection`, and that `rawInterBranch` ($H_{2,\mathrm{raw}}$) reduces to `hoppingInterBranch` while Theorem 17.5 uses `pairingInterBranch`.
2. **Audit of Sugawara and CCR margins:** Verify that `bogoliubov_expansion_on_budget` and `bogoliubov_ccr_on_budget` enforce `A06.branchMargins h M K Ns branches` ($2M + K + \vert{}N_\nu\vert{} \le h$), and that `free_fermion_eq_sugawara_on_budget` and `luttinger_hamiltonian_on_budget` enforce `sugawaraMargin h M K Ns branches` ($K \le M$ and $K + \vert{}N_\nu\vert{} < h$).
3. **Audit of formal perturbative claims vs. exact finite matrix identities:** Verify that `swEffectiveSecondOrder` is presented as a second-order polynomial in $t$, accompanied by `sw_2x2_truncation_witness` (showing the truncation gap at $t = 2/3$) and `sw_3x3_no_iff_witness` (showing that $P[S_1, V]P = 0$ does not imply $PVQ = 0$).
4. **Audit of non-vacuity witnesses:** Verify that `concrete_luttinger_witness` at $h = 8, M = 2, K = 2, N_R = N_L = 0$ and `energy_shell_discards_double_mode_one` provide explicit non-zero Fock vectors satisfying all admissibility and margin hypotheses.
