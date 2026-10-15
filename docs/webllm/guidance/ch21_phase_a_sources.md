# CH21 Phase A: reviewed source guidance (2026-10-15)

The orchestrator prepared this from a read-only analysis of the literature, the Core API and the verifier. **Everything here is a proposal, not a verified truth.** Literature anchors are paths in `References/references-transcripts/`. Abbreviations:
- GIA22 = `giamarchi_2004/2.2_physical_properties_and_correlation_functions.md`
- GIA4 = `giamarchi_2004/04_ch04_refinements_pdf114-150.md`
- GIA7 = `giamarchi_2004/07_ch07_interacting_fermions_on_a_lattice_pdf214-251.md`
- SEN3 = `senechal_1999/03_interacting_electrons_1d.md`, SEN5 = `senechal_1999/05_details_bosonization.md`, SEN6 = `senechal_1999/06_tomonaga_luttinger.md`
- VDS4 = `von_delft_schoeller_1998/04_bosonic_fock_space.md`, VDSD = `von_delft_schoeller_1998/app_d_more_on_klein_factors.md`

Note anchors: `notes/md/ch21_spinful_models.md` = N21, `notes/appendices/a09_duality_spin_and_umklapp.md` = A09n, `notes/appendices/a10_discrete_rg_and_schrieffer_wolff.md` = A10n.

## 0. Key fact: reuse frozen Core, do not re-invent

**Verifier constraint (`scripts/webllm/verify_phase_a.py:40-95`):**
- Imports must be `import Bosonize` or `import Bosonize.Core.X` only. That means no `BosonizeStubs.*`, no CH19/CH20 staging and no `import Mathlib`.
- Allowed commands: import / namespace / section / end / universe / variable / open / noncomputable / def / abbrev / instance / structure / inductive / class.
- Not allowed: `omit … in`, `set_option`, `attribute`, `local notation`, `#`.
- Data must contain no `sorry`. Each lemma/theorem must end with exactly `:= by sorry`.

**So CH21 Phase A must not depend on CH19/CH20 (or on Ch18 staging).** Everything below uses existing Core. Optional bridges to CH20/Ch18 are listed in D, for after they freeze.

**Core API to reuse (signatures checked):**
- **A05** (`Bosonize.A05`, `{σ} [Fintype σ] [LinearOrder σ]`):
  - `Mode σ h = σ × Ch01.Band (2*h)` with lex order `speciesOrder`.
  - `rho h ν m = Σ_{validPairs} Ch04.hopping`, `rho_adjoint` (ρ_m† = ρ_{−m}).
  - `rho_cross_commute (hne : ν ≠ η)` is global. `rho_positive_commute` (m, n ≥ 0) is global.
  - `chargeObservable h ν` (diagonal relative charge), `charge_budget` (`chargeObservable h ν v = (Ns ν : ℂ) • v` on `jointBudget`).
  - `jointBudget h Ns K = Ch07.speciesBudget`, `groundKet`, `ground_mem_budget`, `ground_ne_zero`, `admissible`, `r2`.
  - `annihilation/creation h ν k`, `annihilation_car`, `creation_car`, `mixed_car`, `creation_adjoint`.
  - `liftedAnnihilation h b ν (x : ℤ) = normalization(2h) • Σ_k twistedCharacter (b ν) k x • annihilation h ν k`.
- **A06:**
  - `Orientation` (`.right/.left`, DecidableEq only: **no Fintype/LinearOrder instance**).
  - `Branches σ` (`rightSpecies`, `leftSpecies`, `distinct`), `speciesOf`, `marginAt`, `branchMargins`.
  - `joint_signed_current_commutator h K hh Ns ν m n (hmargin : |m|+|n|+K+|Ns ν| ≤ h) v hv : [ρ_{ν,m}, ρ_{ν,n}] v = Ch10.schwingerCoefficient m n • v`.
  - Here `schwingerCoefficient m n = if m+n=0 then −m else 0`, so [ρ_{−m}, ρ_m] = m.
- **Ch13** (`Bosonize.Ch13`):
  - `lowerCharge`, `phaseExponent h Ns ν = Σ_{η<ν}(h+Ns η) + (h+Ns ν−1)`, `kleinPhase = (−1)^phaseExponent`.
  - `phase_cross_sign`, `pairMargin`, `fourSectorMargin`, `kleinKernel h Ns ν K`, `kernel_ground`, `kernel_ground_nonzero`, `double_kernel_ground_nonzero`.
  - `kernel_cross_anticommute` (F_η F_ν + F_ν F_η = 0 on budget), `kernel_number_shift`, `klein_isometry_equiv`.
  - `ground_top_annihilation (hN) (hν : −h+1 ≤ Ns ν) (k) (hk : k.val = Ns ν) : annihilation h ν k Ω_Ns = kleinPhase h Ns ν • Ω_{lowerCharge Ns ν}`.
  - `ground_field_coefficient` (⟨Ω_{lowered}, liftedAnnihilation h b ν x Ω_Ns⟩ = normalization · kleinPhase · liftPhase · ζ^{x·Ns ν}).
- **Ch14:** `projection h Ns K` (coordinate projector onto `jointBudget`), `projectedMap`, `zeroScalar h b Ns ν x`, `klein_zero_ground`, `physicalMap`.
- **A03:** `coordinateSpace`, `coordinateProjection`, `projection_intersection`, `coordinate_space_disjoint`, `projection_product_remainder` (Pt·A·B·Ps − Pt·A·Pm·B·Ps = Pt·A·(1−Pm)·B·Ps), `projected_product_eq_iff`.
- **Ch04:** `precedingCount`, `fermionSign`, `number_creation_commutator`, `number_annihilation_commutator`, `hopping_blocked`, `parity_creation`, `parity_annihilation`.
- **Ch06Ext:** `periodicTwist`, `liftPhase`. **A01:** `normalization L = (√L)⁻¹`, `canonicalRoot`.
- **A07Interactions:** `HyperbolicParams v1 v2` (u c s, `u_pos`, `u_sq`, `hyperbolic_id`, `match_v1`, `match_v2`).
- **A10:** `sw_compressed_bch_second_order`, `sw_off_zero_implies_effective_exact`, `offDiagPart`, `swEffectiveSecondOrder`, `shell_proj_partition`, `energy_shell_discards_double_mode_one`.

**Missing in Core (CH21 scope):**
- spinful label structure;
- raw charge/spin currents and their budget CCRs;
- charge/spin zero modes and the parity lattice;
- a multispecies charge-observable × creation/annihilation commutator (**Core gap: only single-species `Ch07`**);
- site-field Umklapp operator, H_U, charge shifts, species charge box, leakage criterion and witness;
- singlet pair, channel decomposition, and channel Klein/CAR phase identities.

## A. Claims ledger

| id | statement (finite form) | literature anchor | note | tier | finite? |
|---|---|---|---|---|---|
| ch21.c01 | 4 distinct species R↑,R↓,L↑,L↓ as two `A06.Branches` (one per spin) plus 4 cross-distinctness facts | GIA22:321-329; SEN3:130-141 | Def 21.1 | T2 | yes |
| ch21.c02 | raw R^c_{η,m}=ρ_{η↑,m}+ρ_{η↓,m}, R^s=ρ_{η↑}−ρ_{η↓}; (R_m)†=R_{−m} | SEN3:157-166 (raw J↑±J↓); GIA22:333 and SEN5:518 (with 1/√2) | Def 21.2 | T2 | yes |
| ch21.c03 | global edge formula [R^c_{η,m},R^s_{η,n}] = [ρ_{η↑,m},ρ_{η↑,n}] − [ρ_{η↓,m},ρ_{η↓,n}]; opposite chirality commutes globally | GIA22:337-339 (sectors commute, continuum) | A09n:32-40 | T1 | yes |
| ch21.c04 | on `jointBudget` with margins for both spins of η: [R^c_m,R^s_n]v=0; [R^c_m,R^c_n]v = 2·schwinger(m,n)v, so [R_{−m},R_m]v=2m v (charge and spin) | GIA22:339; SEN6:11-18 | Lemma 21.3 | T1 | yes |
| ch21.c05 | margin is necessary: ↑ full band, ↓ ground ⇒ [R^c_{−1},R^s_1]v = −v ≠ 0 | none (internal) | A09n:36 | T1 | yes (optional) |
| ch21.c06 | a(X↑Y↑+X↓Y↓)+b(X↑Y↓+X↓Y↑) = ((a+b)/2)(X↑+X↓)(Y↑+Y↓) + ((a−b)/2)(X↑−X↓)(Y↑−Y↓) (noncommutative identity) | GIA22:349-353 (g∥±g⊥); SEN5:557-573 | N21:35 | T2 | yes |
| ch21.c07 | for `HyperbolicParams` pc, ps: pc.u = ps.u ↔ v1c²−v2c² = v1s²−v2s²; free counterexample has equal velocities | GIA22:365-375 (u_ν); SEN6:11-13 (same v) | N21:35 | T2 | yes |
| ch21.c08 | Q_c=N↑+N↓, Q_s=N↑−N↓ on budget (eigenvalues); image = {(a,b) : a≡b mod 2}; inverse ((a+b)/2,(a−b)/2); (1,0) ∉ image | none (internal) | N21:21; A09n:42-51 | T2 | yes |
| ch21.c09 | [N_η, c†_{μ,k}] = δ_{ημ}c†, [N_η, c_{μ,k}] = −δ c on A05 carrier | VDS4:458-462 (Klein analogue) | Lemma 21.6 aux | T1 | yes (Core gap) |
| ch21.c10 | O_U(x)=c†_{L↑}c†_{L↓}c_{R↓}c_{R↑}; [N_η,O_U]=ΔN_η O_U with ΔN = e_{L↑}+e_{L↓}−e_{R↓}−e_{R↑}; ΣΔN=0; [Q_s^η,O_U]=0; [Q_c^L,O_U]=2O_U, [Q_c^R,O_U]=−2O_U | SEN3:136-141,161; GIA4:396 | (21.8)-(21.10) | T1 | yes |
| ch21.c11 | H_U=(g_U/L)Σ_x(O_U+O_U†) is self-adjoint for real g_U | SEN3:161 (½vg₃, other normalization) | Def 21.5 | T1 | yes |
| ch21.c12 | single-sector compression P_{Ns,K} H_U P_{Ns,K'} = 0 (no first-order diagonal effect) | GIA4:398-404 (sine-Gordon, continuum only) | A10n:157-161 | T1 | yes |
| ch21.c13 | conditional leakage: g_U≠0, ψ in sector Ns, Σ_x O_U(x)ψ≠0, Ns+ΔN outside box ⇒ H_Uψ ∉ box (adjoint part lies in sector Ns−ΔN) | none | Thm 21.7(1) | T1 | yes |
| ch21.c14 | non-invariance: P·H_U ≠ H_U·P on the box (witness) | none | Thm 21.7(2) | T1 | yes |
| ch21.c15 | nonzero H_Uψ alone does not imply leakage: h=2, R species {−1}, L full; outward term 0 (Pauli); inward image stays in box (1,1,2,2), coefficients ±g_U/16 | none | N21:109-110 | T1 | yes (optional F1 test) |
| ch21.c16 | witness: h≥1, Ns=0, K=0, order (L↑,L↓,R↑,R↓); T adds momentum 1 to both L species and removes 1−h from both R species; counts 2h, 3h−1, 2h, h; sign (−1)^{8h−1}=−1; ⟨δ_T,H_UΩ⟩ = −g_U/L² | GIA4:396 (momentum mod reciprocal lattice) | Lemma 21.8 | T1 | yes |
| ch21.c17 | O_SSC(x)=c_{R↑}c_{L↓} − c_{R↓}c_{L↑}; the two channel targets Ns−e_{L↓}−e_{R↑} ≠ Ns−e_{L↑}−e_{R↓}; their projections are orthogonal | GIA22:428-442 (O_SS = −O_SSC†) | Def 21.4 | T2 | yes |
| ch21.c18 | (P_{t1}+P_{t2}) O_SSC P_s = [P_{t1}c_{R↑}P_{m1}c_{L↓}P_s + R₁] − [P_{t2}c_{R↓}P_{m2}c_{L↑}P_s + R₂], with R_j = P_{tj}c_a(1−P_{mj})c_bP_s; any cutoffs | none (A03 insertion) | (21.7) | T1 | yes |
| ch21.c19 | CAR channel on ground: c_{a,top}c_{b,top}Ω_N = kleinPhase(lowerCharge N b, a)·kleinPhase(N, b) • Ω_{N−e_b−e_a}; Klein product F_aF_bΩ_N gives the same phase (`kernel_ground` twice) | SEN5:497-505 (string factor = `kleinPhase`); VDS4:446-462 | (21.6) | T1 | yes |
| ch21.c20 | standard order, Ns=0, every h≥1: both channel phase products = (−1)^{h+1}; ⟨Ω_{T1},O_SSC(x)Ω⟩ = (−1)^{h+1}/(2h), ⟨Ω_{T2},·⟩ = −(−1)^{h+1}/(2h); at h=2: −1/4 and +1/4 | none | F2 | T1 | yes |
| ch21.c21 | Klein factors cannot be dropped when separate N_η are not conserved (Umklapp, g₁⊥) | VDSD:46-49; SEN5:534-556,575-591 | N21:50 | — | caveat |
| ch21.c22 | KT flow, Mott gap for K_ρ<1, cos(√8φ_ρ) | GIA22:522,546; GIA7:462; GIA4:398-404 | N21:112-113 | — | **deferred** |
| ch21.c23 | energy-shell vs decimation; compressed 2nd-order BCH; converse fails | none | A10n:164-190 | T2 | exists in A10 (cite) |

## B. Convention flags (must respect)

1. **Species order (concrete witnesses):** `Fin 4` with L↑=0 < L↓=1 < R↑=2 < R↓=3. This matches Lemma 21.8's occupation order. All CAR/Klein signs depend on it (`Ch13.phaseExponent` uses lex order and is SEN5:497-505's string factor ∏_{ν<μ}). SEN numbers right movers first, so do not port SEN signs.
2. **Raw currents, no √2:** CCR coefficient 2m. The raw block coefficient (a+b)/2 times R^cR^c equals (a+b)·ρ_ρρ_ρ in GIA's 1/√2 normalization (GIA22:349 g∥+g⊥). SEN3:157-166 already uses raw sums.
3. **Mode orientation as in CH18:** m>0 raises on both branches; [ρ_{−m},ρ_m] = +m (`schwingerCoefficient`).
4. **Singlet sign:** N21's O_SSC lowers charge. GIA22:438 O_SS = ψ†_{R↑}ψ†_{L↓}+ψ†_{L↑}ψ†_{R↓} satisfies O_SS† = −O_SSC. Do not copy GIA's sign.
5. **Umklapp:** N21 O_U = (ψ†_{R↑}ψ†_{R↓}ψ_{L↓}ψ_{L↑})†, i.e. it destroys two R particles. SEN3:161 uses ½vg₃Σ_σ with the opposite chirality plus H.c. Keep N21's g_U/L normalization. Per-species shift is ±1, branch total ±2.
6. **Sites:** x ∈ `Finset.range (2*h)` cast to ℤ. Use `Ch06Ext.periodicTwist (2*h)` for every species. ζ^{2h}=1 gives the phase ζ^{−Lx}=1. Twisted boundaries are deferred.
7. **Klein:** Core Klein = `Ch13.kleinKernel` (typed Gram-kernel isometry, sign fixed by CAR order). It is not SEN's Hermitian Clifford η (SEN5:486-488), and there is no "Klein gauge choice" (SEN5:550-556).
8. **Parity constraint:** automatically true for integer species charges. Its content is the lattice equivalence plus properness. It is not a restriction on Fock vectors.
9. **Charge box:** `A03.chargeBox` takes one scalar charge function. Use a new per-species `speciesBox` (|N_η| ≤ Nmax η, totalExcitation ≤ K).
10. **Names:** never name a Luttinger parameter `K` (K is the energy budget). Avoid `s` for spin labels (it is the sinh coefficient); use `spin…`.
11. **DecidableEq on `A05.Mode`:** follow A10:205-208 (`letI : DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq`) when calling `A02.ket`/`coordinateProjection`, to avoid instance diamonds.
12. **Transcript defect:** GIA4:360-387 is a garbled repeated equation; do not cite it.

## C. Review of user drafts (`ch21-draft-gemini-pro.txt`, `a09_phase_b_stub.md`; untracked, unverified)

**Reusable:**
- Names: `rawChargeCurrent`, `rawSpinCurrent`, `umklappShift`, `umklappHamiltonian`, `spin_charge_commute`, `charge_self_ccr`, `spin_self_ccr`, `umklapp_charge_shift`, `explicit_zero_charge_leakage_witness`.
- The H_U normalization `(gU:ℂ)/((2*h:ℕ):ℂ) • Σ_x (O_U + adjoint O_U)`.
- The ΔN table (+1,+1,−1,−1).
- The witness form `inner ℂ ket_T (H_U Ω) = −gU/L²`.

**Rejected patterns:**
- `import Mathlib`; `BosonizeStubs.*`/`A08`/`Ch18` imports (A09 duality needs A08/CH20 and is out of CH21 scope).
- `instance : LinearOrder Spin := sorry` and `SpinIndex := A06.Orientation × Spin`: Orientation has no Fintype/LinearOrder, so the A05 API is unusable.
- `multiSiteCreation/Annihilation := sorry` (use `A05.liftedAnnihilation` and its adjoint).
- `kleinK1/K2 := sorry` (use `Ch13.kleinKernel` compositions).
- `zeroChargeWitness := sorry` (give an explicit occupation).
- A09 `Ch05.positionCreation` without species (ill-typed on the multispecies carrier).
- Draft `A03.chargeBox (Ch07.relativeCharge h) …` on the multispecies carrier (ill-typed).

**F2 (vacuity) defects:**
- `frozenMarginRegime := sorry` (an arbitrary submodule makes the CCRs vacuous): use the explicit `A06.joint_signed_current_commutator` margins.
- `projected_singlet_residual : True`.
- A09 `ParityConstrainedSublattice v := ∃ q : ℂ, (Qc−Qs) v = 2q•v` is true for every eigenvector because q ∈ ℂ.
- `isParityConstrained` is always true: add the properness witness (1,0) ∉ image.

**F1 (wrong statement):**
- Leakage hypothesis `∃ x, O_U(x) v ∉ box` is per site. Sites can cancel, and it is not N21's outward criterion (the spatial sum Σ_x O_U(x)ψ ≠ 0 with outside charge).
- The A09 draft currents use only the right branch.
- "Exact" singlet bosonization: combined exponentials are not part of (21.7) (N21:65).

### Reusable excerpt (verbatim draft; adapt as in D: species via `SpinBranches`, sites via `Finset.range`)

```text
noncomputable def umklappHamiltonian : A05.Operators SpinIndex h :=
  ((gU : ℂ) / ((2 * h : ℕ) : ℂ)) • ∑ x : ZMod (2 * h),
    (umklappOperator h x + LinearMap.adjoint (umklappOperator h x))
lemma explicit_zero_charge_leakage_witness (hh : 1 ≤ h) (hgU : gU ≠ 0) :
    let Ω := A05.groundKet h (fun _ => 0)
    inner ℂ (zeroChargeWitness h) (umklappHamiltonian h gU Ω) =
      -(gU : ℂ) / (((2 * h : ℕ) : ℂ) ^ 2) ∧
    -(gU : ℂ) / (((2 * h : ℕ) : ℂ) ^ 2) ≠ 0 := by
  sorry
```

## D. Recommended Phase A scope

**Module:** `BosonizeStubs/Ch21SpinfulModels.lean`, namespace `Bosonize.Ch21`; final Core path `Bosonize/Core/Ch21SpinfulModels.lean`.
- **No separate A09 module:** the A09 spin/Umklapp content lives here, and the A09 duality (A09n:3-17) belongs to CH20/A08.
- **A10 is cited, not restated.**
- **Imports:** `Bosonize.Core.Ch14Mandelstam`, `Bosonize.Core.A06ChiralFields`, `Bosonize.Core.A07InteractionsAndBogoliubov`, `Bosonize.Core.A10DiscreteSchriefferWolff`.
- **Variables:** `{σ : Type*} [Fintype σ] [LinearOrder σ]`. Write rUp := sb.up.rightSpecies, lUp := sb.up.leftSpecies, rDn := sb.down.rightSpecies, lDn := sb.down.leftSpecies.

**Data (complete, no sorry):**
1. `structure SpinBranches (σ)`: fields `up down : A06.Branches σ`, plus `rr : up.rightSpecies ≠ down.rightSpecies`, `rl`, `lr`, `ll` (all cross pairs). Add accessors `SpinBranches.rUp/rDn/lUp/lDn` as defs. Per-spin `Branches` plug directly into A06/A07/Ch17.
2. `standardSpinBranches : SpinBranches (Fin 4)` := up ⟨2,0,_⟩, down ⟨3,1,_⟩, all proofs `by decide`.
3. Currents and zero modes:
   - `rawChargeCurrent h sb η m := A05.rho h (A06.speciesOf sb.up η) m + A05.rho h (A06.speciesOf sb.down η) m`; `rawSpinCurrent` is the difference.
   - `chargeZeroMode`/`spinZeroMode h sb η` (sum/difference of `A05.chargeObservable`).
   - `chargeSpinLabel (a b : ℤ) : ℤ × ℤ := (a+b, a−b)`, `paritySublattice : Set (ℤ×ℤ) := {q | q.1 ≡ q.2 [ZMOD 2]}`, `chargeSpinInverse q := ((q.1+q.2)/2, (q.1−q.2)/2)`.
4. Site fields and pair/Umklapp data:
   - `siteAnnihilation h ν (x : ℤ) := A05.liftedAnnihilation h (fun _ => Ch06Ext.periodicTwist (2*h)) ν x`; `siteCreation := LinearMap.adjoint (siteAnnihilation h ν x)`.
   - `singletPair h sb x := siteAnnihilation rUp x * siteAnnihilation lDn x − siteAnnihilation rDn x * siteAnnihilation lUp x`.
   - `cooperTargetOne sb Ns := Ch13.lowerCharge (Ch13.lowerCharge Ns lDn) rUp`; `cooperTargetTwo` uses (lUp, rDn).
   - `umklappShift sb η := (if η=lUp then 1 else 0)+(if η=lDn then 1 else 0)−(if η=rUp then 1 else 0)−(if η=rDn then 1 else 0)`.
   - `umklappOp h sb x := siteCreation lUp x * siteCreation lDn x * siteAnnihilation rDn x * siteAnnihilation rUp x`.
   - `outwardUmklapp h sb := Σ_{x∈range(2h)} umklappOp h sb x`; `umklappHamiltonian h sb gU := ((gU:ℂ)/((2*h:ℕ):ℂ)) • Σ_x (umklappOp + adjoint umklappOp)`.
5. Box and witness configuration:
   - `speciesBox h (Nmax : σ → ℕ) (K : ℕ) := A03.coordinateSpace {S | (∀ η, |relCharge_η S| ≤ Nmax η) ∧ Ch07.totalExcitation h S ≤ K}`.
   - `bandOne h (hh : 0<h) : Ch01.Band (2*h) := ⟨1,_⟩`, `bandBottom h hh := ⟨1−h,_⟩`.
   - `leakageTargetConfig h hh : A05.Occupation (Fin 4) h` := insert (0,bandOne) (insert (1,bandOne) (((groundConfiguration h 0).erase (2,bandBottom)).erase (3,bandBottom))).
6. Velocity witnesses: `chargeParamsWitness : A07Interactions.HyperbolicParams 17 15` (u=8, c=5/4, s=3/4) and `spinParamsWitness : HyperbolicParams 5 0` (u=5, c=1, s=0). Every field by `norm_num`.

**Theorem contracts (each `:= by sorry`).**

*Currents*
1. `raw_charge_adjoint`, `raw_spin_adjoint`.
2. Edge formulas (global, from `rho_cross_commute`):
   - `charge_spin_commutator_edge`: [R^c_{η,m}, R^s_{η,n}] = [ρ_{up},…] − [ρ_{dn},…].
   - `charge_spin_opposite_commute`: η ≠ η′ gives zero, for all four c/s pairings.
3. Budget CCRs, with hypotheses `hh : 0<h`, `hup : |m|+|n|+K+|Ns (speciesOf sb.up η)| ≤ h`, `hdn` (same for down) and `v ∈ A05.jointBudget h Ns K`:
   - `spin_charge_commute_on_budget`: [R^c_m, R^s_n] v = 0.
   - `charge_self_ccr_on_budget` and `spin_self_ccr_on_budget`: [R_m, R_n] v = (2:ℂ) • schwingerCoefficient m n • v.
4. Block and velocities:
   - `spin_exchange_block_decomposition (a b : ℂ) (Xu Xd Yu Yd : A05.Operators σ h)`: identity c06.
   - `spin_charge_velocity_eq_iff (pc : HyperbolicParams v1c v2c) (ps : HyperbolicParams v1s v2s) : pc.u = ps.u ↔ v1c^2−v2c^2 = v1s^2−v2s^2`.
5. Zero modes and lattice:
   - `zero_modes_on_budget` (eigenvalues Ns↑±Ns↓, via `charge_budget`).
   - `charge_spin_label_mem`, `charge_spin_label_injective`, `charge_spin_inverse_spec` (inverse on `paritySublattice`), `parity_sublattice_proper : ((1,0) : ℤ×ℤ) ∉ paritySublattice`.

*Charges and Umklapp*
6. `charge_observable_creation_commutator` / `charge_observable_annihilation_commutator` (multispecies; Core gap; prove via Ch04 number commutators and the diagonal definition).
7. Umklapp charge statements:
   - `umklapp_charge_shift`: [chargeObservable h η, umklappOp h sb x] = (umklappShift sb η : ℂ) • umklappOp h sb x.
   - `umklapp_shift_sum_zero`.
   - `umklapp_spin_conserved`: [spinZeroMode h sb η, umklappOp x] = 0.
   - `umklapp_branch_charge`: left +2, right −2.
8. Hamiltonian statements:
   - `umklapp_hamiltonian_self_adjoint` (gU : ℝ).
   - `umklapp_sector_compression_zero`: `Ch14.projection h Ns K * umklappHamiltonian h sb gU * Ch14.projection h Ns K' = 0`. This feeds A10 with P V P = 0. Do not claim any generator or effective sign.
9. Leakage:
   - `umklapp_conditional_leakage`, with hypotheses `(hgU : gU ≠ 0) (hψ : ψ ∈ jointBudget h Ns K) (hout : outwardUmklapp h sb ψ ≠ 0) (hbox : ∃ η, (Nmax η : ℤ) < |Ns η + umklappShift sb η|)`: conclusion `umklappHamiltonian h sb gU ψ ∉ speciesBox h Nmax K'`.
   - `umklapp_box_not_invariant`: adds `ψ ∈ speciesBox h Nmax K'`; conclusion `¬ ∀ v ∈ box, H_U v ∈ box`.
10. Witness family (`sb := standardSpinBranches`, `hh : 0<h`):
    - `leakage_target_charges` (target relative charges = umklappShift).
    - `leakage_witness_preceding_counts` (2h, 3h−1, 2h, h).
    - `leakage_witness_coefficient`: `inner ℂ (A02.ket (leakageTargetConfig h hh)) (umklappHamiltonian h sb gU (A05.groundKet h 0)) = −(gU:ℂ)/(((2*h:ℕ):ℂ)^2)`.
    - `zero_charge_leakage`: for gU≠0, Ω ∈ speciesBox h 0 0 and H_UΩ ∉ speciesBox h 0 K for all K.
    - `umklapp_projection_not_commute`.
    - Optional `inward_only_no_leakage_witness` (c15) and `mixed_commutator_off_margin_witness` (c05).

*Cooper channels*
11. `cooper_targets_ne`; `cooper_target_projections_orthogonal` (`Ch14.projection h T1 K1 * Ch14.projection h T2 K2 = 0`).
12. `singlet_cross_channel_zero`: `projection h T1 Kt * (siteAnnihilation rDn x * siteAnnihilation lUp x) * projection h Ns Ks = 0`, and symmetrically.
13. `projected_singlet_two_channels` (21.7) as an ambient identity with arbitrary Ks, Km₁, Km₂, Kt₁, Kt₂ (c18). This avoids subtracting maps with distinct codomains.
14. `singlet_channel_ground_car`, for both channels:
    - Hypotheses: `hN : A05.admissible h Ns`, `−h+1 ≤ Ns lDn`, `−h+1 ≤ Ns rUp`, `ka.val = Ns rUp`, `kb.val = Ns lDn`.
    - Statement: `A05.annihilation h rUp ka (A05.annihilation h lDn kb Ω_Ns) = (kleinPhase h (lowerCharge Ns lDn) rUp * kleinPhase h Ns lDn) • Ω_{cooperTargetOne}`.
15. `klein_channel_ground` (`fourSectorMargin h K Ns lDn rUp`): the `kleinKernel` composition on Ω equals the same phase times Ω_target. Then `klein_matches_car_channel` and `singlet_ground_coefficient` (normalization² · zeroScalar · kleinPhase products; T2 with a minus sign).
16. Optional `singlet_charge_spin_shift`: total charge −2, total spin 0.

**Witnesses (explicit, nonzero):**
- W1 `concrete_spin_charge_witness`: h=2, Ns=0, K=0, `standardSpinBranches`. Margins hold, [R^c_{−1},R^c_1]Ω = [R^s_{−1},R^s_1]Ω = 2•Ω ≠ 0, and `rawSpinCurrent … .right 1 Ω ≠ 0`.
- W2 `concrete_singlet_phases`: both phase products equal (−1)^{h+1} for every h>0. At h=2, x=1 the coefficients are −1/4 (T1) and +1/4 (T2).
- W3 `concrete_leakage_witness`: h=2, gU=1, coefficient −1/16 ≠ 0.
- W4 `concrete_velocity_witness`: u_c=8 ≠ 5=u_s; the free case (1,0),(1,0) has equal u.

**Optional post-freeze bridges (not Phase A):**
- `singletPair = Ch20.orderParamSC(⟨rUp,lDn⟩) − Ch20.orderParamSC(⟨rDn,lUp⟩)`, if Ch20 Core defines SC on generic `Branches`.
- Ch20's typed residual lemma as an alternative proof of item 13.
- `Ch18.LuttingerParams` is only an alias of `A07Interactions.HyperbolicParams`, so it is not needed.

**Defer / caveat only:**
- KT flow (GIA22:522) and Mott gap (GIA7:462); sine-Gordon cos(√8φ) forms (GIA4:398-404; GIA22:361,379).
- Combined compressed spin exponentials (N21:65); normalized √2 fields.
- Spectral spin-charge separation and the tensor/direct-sum budget splitting K_c+K_s≤K (A09n:47-51).
- g₁⊥ backscattering; the Umklapp Klein product on `inverseKernel` (SEN5:575-591).
- Twisted boundaries; SW generator for H_U (needs A10 non-resonance/adapted basis); A10 budget-transfer bridge (A10n:188).
- SU(2) invariance (SEN3:180-184); SS/CDW/SDW exponents (GIA22:418-442; CH19); A09 duality (CH20/A08).
