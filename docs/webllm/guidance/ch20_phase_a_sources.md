# CH20 Phase A: reviewed source guidance (2026-10-15)

The orchestrator prepared this from a read-only analysis of the literature and the API. **Everything here is a proposal, not a verified result.** No Lean code was compiled for this document. Literature anchors point into `References/references-transcripts/`. Abbreviations: GIA22 = `giamarchi_2004/2.2_physical_properties_and_correlation_functions.md`, GIA3 = `giamarchi_2004/03_ch03_luttinger_liquids_pdf084-113.md`, SEN = `senechal_1999/06_tomonaga_luttinger.md`, VDS4 = `von_delft_schoeller_1998/04_bosonic_fock_space.md`, VDS9 = `von_delft_schoeller_1998/09_vertex_operators.md`. Note anchors: N20 = `notes/md/ch20_CDW.md`, A08 = `notes/appendices/a08_states_and_correlations.md`, A09 = `notes/appendices/a09_duality_spin_and_umklapp.md`.

## 0. Key fact: reuse frozen Core, do not re-invent

**Finite CAR layer (all frozen):**
- `A05.liftedAnnihilation h b ν (x : ℤ)` = `normalization(2h) • Σ_k twistedCharacter(b ν) k x • annihilation h ν k`. This is the position field per species. There is **no lifted creation**: use `LinearMap.adjoint`.
- `A05.creation_adjoint` gives `adjoint (annihilation h ν k) = creation h ν k`.
- Also from A05: `A05.chargeObservable`, `A05.charge_budget`, `A05.groundKet`, `A05.ground_mem_budget`, `A05.admissible`, `A05.jointBudget` (= `Ch07.speciesBudget`, a coordinate space).
- From Ch14 (namespace `Bosonize.Ch14`): `budgetSet`, `projection h Ns K` (= `A03.coordinateProjection (budgetSet …)`), `projectedMap h Ns Nt Kin Kout A`, `budgetAdjoint`, `projected_map_apply` (rfl), `projected_map_adjoint` (reverses source and target), `groundVector h hh Ns hN K`, `zeroScalar`, `physical_occupation_expansion`, `projected_recurrence_residual`.
- `A03.projection_product_remainder`: `Pt*A*B*Ps − Pt*A*Pm*B*Ps = Pt*A*(1−Pm)*B*Ps` (noncomm_ring). `A03.projected_product_eq_of_maps`, `A03.projection_idempotent`, `A03.projection_fixed_iff`, `A03.projection_adjoint`.
- From Ch13: `Ch13.lowerCharge Ns ν` (no `raiseCharge` exists), `Ch13.phaseExponent h Ns ν = Σ_{η<ν}(h+Ns η) + (h+Ns ν−1)`, `Ch13.kleinPhase = (−1)^phaseExponent`. This is exactly the note's P_ν(N) with R<L.
- Scalars and helpers: `Ch04.fermionSign` (= (−1)^#preceding, lex species×momentum order); `A01.integerCharacter ζ k x = ζ^(k*x)`; `A01.canonicalRoot`; `A01.canonical_root_primitive`; `A01.complex_character_conj` (`star χ(k,x) = χ(−k,x)` for a primitive root); `A01.normalization`; `Ch06Ext.periodicTwist`; `Ch16.standardBranches = ⟨0,1,_⟩` (R=0<L=1); `A02.commutator A B = A*B − B*A` (generic module).

**Oscillator and parameter layer:**
- From `A07Interactions`: `HyperbolicParams v1 v2` (u c s, `u_sq`, `hyperbolic_id`, `match_v1`, `match_v2 : v2 = 2*u*c*s`), `oppositeOrientation`, `bogoliubovCreator h m c s branches η = c•ρ_{m,η} + s•ρ_{−m,η̄}`, `bogoliubovAnnihilator`, `pairingMode h m v1 v2 branches`, `pairing_mode_ground_nonzero`.
- From `A05`: `A05.rho`, `A05.rho_cross_commute`, `A05.rho_lowering_budget_zero`.
- From `A06`: `A06.Orientation`, `A06.orientationSign`, `A06.Branches`, `A06.speciesOf`, `A06.branchMargins`.
- From `Ch17`: `Ch17.v1Velocity`, `Ch17.v2Velocity g2 = g2/(2π)`, `Ch17.zeroModeEnergyScalar` (has a linear μ term), `Ch17.symmetricZeroModeScalar` (= π/L[v1(nr²+nl²)+2v2 nr nl]), `Ch17.canonicalMu`, `Ch17.zero_mode_scalar_canonical_mu`.
- CH18 (staging `BosonizeStubs/Ch18Bogoliubov.lean`, will become Core unchanged): `Ch18.HyperbolicPair` (c s, `hyperbolic_id`), `.ofParams`, `luttingerG = (c−s)²`, `luttingerGInv = (c+s)²`, `LuttingerParams` (abbrev of `HyperbolicParams`), `LuttingerParams.toHyperbolicPair`, `HyperbolicPair.inverse_combination`, `luttingerG_mul_inv`, `concreteParams` (17,15,8,5/4,3/4), `concretePair`.
- Ch15 `phiField = R + L` and `thetaField = R − L`, so the duality ρ_R ↦ −ρ_R gives φ ↦ −θ and θ ↦ −φ.

**Missing in Core (CH20 scope):**
- `raiseCharge`, the left reflection f(N) and the CDW/SC target labels.
- Order parameters O_CDW and O_SC.
- The typed product with residual for these specific fields.
- Charge-shift commutators for fields.
- Charge/Klein coefficients and their duality laws.
- The mode-family duality, P* = (u,c,−s), g↔g⁻¹, D₁.

**CH19/A08 dependency:**
- No A08 carrier exists yet (`notes/draft-lean-code/a08_phase_b_stub.txt` is an unverified draft).
- Thm 20.5, the tensor-algebra automorphism D, the full vertex law (20.10) in A[[t]], and ω-transport (20.11b) all need the A08 state, Wick moments and series carrier. They are **deferred to a CH20b module after CH19 Core lands**.
- Everything in §D below is CH19-independent.

## A. Claims ledger

| id | statement (finite form) | literature anchor | note | tier | finite? / CH19 dep |
|---|---|---|---|---|---|
| ch20.c01 | O_CDW(x)=c†_{R,x}c_{L,x}, O_SC(x)=c_{R,x}c_{L,x} on `A05` Fock; distinct species R≠L | GIA22:225 (SU=ψ_R†ψ_L†); SEN:207-210 | N20:7-11 | T2 | yes / indep |
| ch20.c02 | [N_ν,O_CDW]=(δ_{νR}−δ_{νL})O_CDW, [N_ν,O_SC]=−(δ_{νR}+δ_{νL})O_SC, global (no budget) | none (CAR) | N20:13 charges | T1 | yes / indep |
| ch20.c03 | typed (20.3)/(20.4): p_t O i_s = B∘B_L + p_t c(1−P_m)c_L i_s, exact, hypothesis-free | none | N20:13-26; A03 remainder | T1 | yes / indep |
| ch20.c04 | the B_R† label is `budgetAdjoint` of the projected c_R from target to middle (reversed carriers) | none | N20:26 | T2 | yes (via `Ch14.projected_map_adjoint`) |
| ch20.c05 | ground→ground matrix element = L⁻¹·ζ^{(N_L−N_R−1)x}·P_L(N)P_R(N−e_L+e_R) (CDW); L⁻¹ζ^{(N_R+N_L)x}P_L(N)P_R(N−e_L) (SC); periodic twist; band margins | SEN:209-210 (Klein η η̄ factors) | N20:28 | T1 | yes / indep |
| ch20.c06 | L=4, ζ=i, x=1: CDW (0,0)→(1,−1) gives i/4; SC (1,0)→(0,−1) gives i/4 (hand-checked against Core signs) | internal | N20:28 | F2 | yes (witness) |
| ch20.c07 | residual is nonvacuous: h=2, Ks=Km=0, Kt=1, CDW residual on ground ≠0 (expected coefficient −1/4); at Kt=0 it is 0 | none | N20:26-28 | F2 | yes (witness) |
| ch20.c08 | D₁(x,y)=Σ_{m=1}^M(1−cos(2πm(x−y)/L))/m; D₁(x,x)=0, symmetric, ≥0 | GIA22:201-207 (continuum (1−cos px)/p) | (20.5) | T2 | yes / indep |
| ch20.c09 | Weyl vertices W_J, Thm 20.5 Exp_formal[−2gD₁t²], [−2g⁻¹D₁t²] | GIA22:173 (2.64), 185 (2.67), 191 (2.68) | N20:40-69; A08:93-124 | T1 | **CH19/A08 dep — defer** |
| ch20.c10 | P*=(u,c,−s): HyperbolicParams v1 v2 → v1 (−v2); g(P*)=g⁻¹(P), g⁻¹(P*)=g(P); involutive | GIA3:217 (H invariant under φ→θ, K→1/K); GIA22:61 (2.41) | N20:76 | T2 | yes / indep |
| ch20.c11 | family duality ρ_R↦−ρ_R, ρ_L fixed: involutive; commutators preserved up to a cross sign (cross ones vanish) | SEN:80-90 (dual rescaling) | N20:76; A09:5 | T2 | yes (family level) / indep |
| ch20.c12 | C̃_R(P)↦−C̃_R(P*), C̃_L(P)↦C̃_L(P*) (same for Ã); D X_CDW(P)=−X_SC(P*), D X_SC(P)=−X_CDW(P*) | GIA22:239,259 (CDW/SC duality, qualitative) | N20:81; A09:7 | T2 | yes (family level) / indep |
| ch20.c13 | Klein: P_R(f N)=P_R(N); P_L(f N)=−P_L(N+e_L), i.e. D F_R=F_R, D F_L=−F_L† | VDS4:447-456 (abstract Klein F) | N20:78; A09:5 | T1 | yes (scalar) / indep |
| ch20.c14 | D K_CDW = ζ^x K_SC†, D K_SC = ζ^x K_CDW† as label + coefficient identities (hand-checked for both species orders) | none | A09:7,12; N20:83-86 | T1 | yes (scalar) / indep |
| ch20.c15 | oscillator: pairing(v1,v2) of the dual family = pairing(v1,−v2); zero mode: `symmetricZeroModeScalar`(f N; g2) = (N; −g2) | GIA3:217 | N20:88-96 | T1 | yes / indep |
| ch20.c16 | the linear-μ zero mode is NOT dual-invariant (counterexample) | none | N20:98; A09:15 | F1 | yes (witness) |
| ch20.c17 | ω_{P*,f(N)}∘D=ω_{P,N}; D a star-automorphism of the A08 tensor algebra | none | N20:98; A09:15 | T1 | **CH19/A08 dep — defer** |
| ch20.c18 | the oscillator/charge duality is not a finite-Fock unitary; no T-duality or spectral claim | none | N20:98,101; A09:17 | T2 | caveat only |
| a09.c19 | spin/charge currents, parity sublattice, Umklapp shift and leakage | GIA22:413 (2.113) | A09:19-93 | — | **CH21 scope — exclude** |
| a08.c20 | compressed-vacuum counterexample diag(2s²,c²,c²)=diag(32/9,25/9,25/9) (checked) | none | A08:44-69 | — | CH19/A08 scope — cite only |

## B. Convention flags (must respect)

1. **Order of factors.**
   - O_SC = c_R c_L is the annihilation pair. Giamarchi's O_SU = ψ_R†ψ_L† (GIA22:225) is its adjoint.
   - Correlators are ω(W* W). Do not reorder.
2. **No explicit 2k_F.** Momenta are computational: both branches use `Band (2h)`, and L is index-reflected. The e^{−2ik_F x} of GIA22:413 and SEN:209 shows up here as the source phase ζ^{(N_L−N_R−1)x}.
3. **Klein convention R<L.** P_ν(N) is `Ch13.kleinPhase` (A08:34-35 equals Ch13:22-26). Charge phases act on the **source** first (Ch14 `zeroMode` precedes the Klein shift).
4. **ζ.** Use `A01.canonicalRoot (2*h)`, because the Core fields hard-code it inside `twistedCharacter`. Fix `b := fun _ => Ch06Ext.periodicTwist (2*h)` for the coefficient theorems; a general twist adds `liftPhase` factors. Positions are `x : ℤ` (A05/Ch14), not `ZMod`.
5. **Duality signs.**
   - P* flips s, swaps g↔g⁻¹, flips v2 (g2↦−g2) and keeps v1 fixed.
   - The literature form is φ↔θ, K↔1/K (GIA3:217). Here it is ρ_R↦−ρ_R, hence φ↦−θ, θ↦−φ.
   - The adjoint and the ζ^x factor in (20.10) are mandatory. A "direct CDW→SC" exchange has the wrong charge shift (N20:86).
6. **D is not an operator on `A05.Operators`.** In Phase A it is a *substitution on mode families* plus *scalar charge-label/coefficient maps*. Never type it as `≃ₐ⋆` on `Module.End` of the Fock space, the polynomial carrier or the charge module: those carry no star structure, and the charge module has no `InnerProductSpace`.
7. **Zero modes.** Use `Ch17.symmetricZeroModeScalar`, or `zeroModeEnergyScalar` at `Ch17.canonicalMu`. The linear term breaks DH=H* (N20:98).
8. **Normalizations differ.** The formal model gives L⁻² at x=y; the finite CAR value at L=4 is a different observable (N20:72). Weyl vertices are not normal-ordered vertex operators (VDS9:27-48,80; A08:109).
9. **Never name the Luttinger parameter `K`** (K is the budget). Use `luttingerG` / `luttingerGInv`.
10. **Transcript defects.**
    - GIA22:237 (2.78) reads exponent 1/(4K). That is inconsistent with the 2K of (2.68) at GIA22:191 under K↔1/K. Do not cite that exponent.
    - GIA22:67 is garbled (see CH18 guidance).
    - Power laws are context only.

## C. Review of user drafts (`notes/draft-lean-code/ch20-draft-gemini-pro.txt`, `a09_phase_b_stub.md`; unverified)

**Reusable:**
- The section split (finite CAR / formal vertices / duality).
- `paramInvolution` typed `LuttingerParams v1 v2 → LuttingerParams v1 (−v2)`. It is fully constructible; see §D.
- `lp.toHyperbolicPair` matches the CH18 staging name.
- A08 draft `shiftP` agrees with `Ch13.phaseExponent` for R<L.
- Generator-level targets `duality_F_R`, `duality_F_L` (=−F_L†), `duality_Z_R`, `duality_Z_L` (=Z_L†) are correct mathematically. Restate them as scalar coefficient laws.
- `umklappShift` (+1,+1,−1,−1) is correct, but it is CH21 work.

**Rejected patterns:**
- `import Mathlib`; `import BosonizeStubs.A08StatesAndCorrelations` (no such module; CH19 dependency).
- `sorry` in data (`formalWeylCDW`, `dualityMap`, `frozenMarginRegime`, `zeroChargeWitnessKet`, `paramInvolution`).
- `Ch06Ext.siteCreation` and `Ch05.positionCreation` without species, which is type-incompatible with `A05.Operators σ h`.
- `LinearMap.adjoint` on `(ℤ×ℤ) →₀ ℂ`.
- `≃ₐ⋆[ℂ]` on `Module.End` of non-Hilbert carriers.
- `dualityOscillatorMap` (A08 carrier) applied to A07 `bogoliubovCreator` (A05 Fock): this mixes carriers.
- Vertex laws evaluated at `t = 1`.
- `omegaPN` applied to arbitrary `Module.End` elements: A08 only defines it on the generated algebra.

**F2 (vacuity) defects:**
- `projected_*_residual`, `weyl_correlator_*`, `duality_W_CDW` and `duality_state` conclude `True`.
- The residual lemmas take arbitrary maps `cL`, `cR_dag` that are never tied to the fields.
- `orderParamSC` = c_x c_x of one species = 0 by CAR (vacuous).
- `ParityConstrainedSublattice` uses `∃ q : ℂ`, which holds for any eigenvector. This is CH21 work anyway.

**F1 (wrong statement) defects:**
- `orderParamCDW` uses a single species, so it is a density, not CDW.
- The CDW target uses `lowerCharge … rightSpecies`, but c_R† *raises* N_R.
- `umklapp_leakage_condition` infers H_U v ∉ box from one outward x, ignoring cancellation (A09:84,93). It is likely false, and it is CH21 work.

### Reusable excerpts (verbatim from the draft; adapt as in §D)

```text
/-- Involution mapping Luttinger parameters P = (u, c, s, g, gInv) to P* = (u, c, -s, gInv, g). -/
noncomputable def paramInvolution {v1 v2 : ℝ} (lp : Ch18.LuttingerParams v1 v2) :
    Ch18.LuttingerParams v1 (-v2) :=
  sorry
```
```text
def shiftP (N : ChargeKet) (ν : A06.Orientation) : ℂ :=
  if ν = .right then (-1 : ℂ) ^ ((h : ℤ) + N.1 - 1)
  else (-1 : ℂ) ^ ((h : ℤ) + N.1 + (h : ℤ) + N.2 - 1)
```

## D. Recommended Phase A scope

**Module and imports.**
- Module `BosonizeStubs/Ch20CDW.lean`, namespace `Bosonize.Ch20`, final path `Bosonize/Core/Ch20CDW.lean`.
- An optional split moves the §D3 duality section to `BosonizeStubs/A09Duality.lean` (namespace `Bosonize.A09`), which Ch20 then imports. Use one module if the packet whitelist allows only one target.
- Imports: `Bosonize.Core.Ch14Mandelstam`, `Bosonize.Core.Ch16FieldHamiltonian`, `Bosonize.Core.Ch17LuttingerModels`, `Bosonize.Core.Ch18Bogoliubov` (after promotion). **No A08/CH19 import.**
- Variables `{σ : Type*} [Fintype σ] [LinearOrder σ]`.
- Copy the Ch14 local `A05.speciesOrder` instances if `LinearMap.adjoint`/`Finset` need them.
- Only `import Bosonize…` lines are allowed; no `local notation`.

**D0. Labels (complete data, no sorry).**
- `raiseCharge Ns ν := Function.update Ns ν (Ns ν + 1)`
- `reflectLeft branches Ns := Function.update Ns branches.leftSpecies (-(Ns branches.leftSpecies))`
- `cdwTarget branches Ns := raiseCharge (Ch13.lowerCharge Ns L) R`
- `scTarget branches Ns := Ch13.lowerCharge (Ch13.lowerCharge Ns L) R`
- `cdwShift branches ν : ℤ := (if ν = R then 1 else 0) - (if ν = L then 1 else 0)`
- `scShift branches ν : ℤ := -(if ν = R then 1 else 0) - (if ν = L then 1 else 0)`

Here R, L abbreviate `branches.rightSpecies` and `branches.leftSpecies`.

**D1. Finite CAR order parameters.** Set `fieldOf h b ν x := A05.liftedAnnihilation h b ν x`.
- `orderCDW h b branches x := LinearMap.adjoint (fieldOf h b R x) * fieldOf h b L x`
- `orderSC h b branches x := fieldOf h b R x * fieldOf h b L x`
- `cdwResidualOp h b branches x Ns Km := LinearMap.adjoint (fieldOf h b R x) * (1 - Ch14.projection h (Ch13.lowerCharge Ns L) Km) * fieldOf h b L x`
- `scResidualOp` is the same with `fieldOf h b R x` in place of the adjoint.

**Theorem contracts (each `:= by sorry`).**
1. Label lemmas:
   - `lowerCharge_raiseCharge : Ch13.lowerCharge (raiseCharge Ns ν) ν = Ns`
   - `cdwTarget_apply : cdwTarget branches Ns ν = Ns ν + cdwShift branches ν`
   - `scTarget_apply` (same pattern)
   - `reflectLeft_involutive`
2. `orderCDW_charge_commutator (ν) : A02.commutator (A05.chargeObservable h ν) (orderCDW h b branches x) = ((cdwShift branches ν : ℤ) : ℂ) • orderCDW h b branches x`. Also `orderSC_charge_commutator` with `scShift`. Both are global.
3. `ambient_cdw_residual`: `Ch14.projection h (cdwTarget branches Ns) Kt * orderCDW … * Ch14.projection h Ns Ks = Pt * c_R† * Pm * c_L * Ps + Pt * c_R† * (1 - Pm) * c_L * Ps`. Cite `A03.projection_product_remainder`.
4. `projected_cdw_residual (Ns Ks Km Kt)`:
   - `Ch14.projectedMap h Ns (cdwTarget branches Ns) Ks Kt (orderCDW h b branches x)`
   - `= (Ch14.projectedMap h (Ch13.lowerCharge Ns L) (cdwTarget branches Ns) Km Kt (LinearMap.adjoint (fieldOf h b R x))).comp (Ch14.projectedMap h Ns (Ch13.lowerCharge Ns L) Ks Km (fieldOf h b L x))`
   - `+ Ch14.projectedMap h Ns (cdwTarget branches Ns) Ks Kt (cdwResidualOp h b branches x Ns Km)`.
   - `projected_sc_residual` is analogous with `scTarget`.
   - No hypotheses: the residual is retained, never dropped.
5. `cdw_creation_factor_eq_budgetAdjoint`: the first factor in 4 equals `Ch14.budgetAdjoint h (cdwTarget …) (lowerCharge Ns L) Kt Km (Ch14.projectedMap h (cdwTarget …) (lowerCharge Ns L) Kt Km (fieldOf h b R x))`. This uses the cancellation `lowerCharge (cdwTarget Ns) R = lowerCharge Ns L` (needs `branches.distinct`) and `Ch14.projected_map_adjoint`.
6. `orderCDW_ground_coeff (hh : 0 < h) (hN : A05.admissible h Ns) (hR : Ns R < h) (hL : -(h:ℤ) < Ns L)`:
   - `inner ℂ (A05.groundKet h (cdwTarget branches Ns)) (orderCDW h (fun _ => Ch06Ext.periodicTwist (2*h)) branches x (A05.groundKet h Ns)) = (((2*h : ℕ) : ℂ))⁻¹ * cdwChargeCoeff h branches Ns x`.
   - `orderSC_ground_coeff` uses `hR : -(h:ℤ) < Ns R` and `hL`.
   - Hand-check: the CAR preceding counts equal `phaseExponent h Ns L` and `phaseExponent h (cdwTarget Ns) R` (resp. `(lowerCharge Ns L) R`). The characters multiply to ζ^{(N_L−N_R−1)x}.
   - If Phase B finds the general form costly, keep it, and prove witness 7 first by evaluation.
7. `concrete_order_witness`, with h=2, `b := fun _ => Ch06Ext.periodicTwist 4`, `Ch16.standardBranches`, x=1:
   - (a) CDW from Ns=0: inner = `Complex.I / 4`.
   - (b) SC from Ns=![1,0]: inner = `Complex.I / 4`.
   - (c) `cdwChargeCoeff 2 standardBranches 0 1 = Complex.I`.
   - (d) at Ks=Km=0, Kt=1: `Ch14.projectedMap h 0 (cdwTarget …) 0 1 (cdwResidualOp … 0 0) (Ch14.groundVector 2 _ 0 _ 0) ≠ 0`. The expected component on ket R{−1,0,1}, L{0} is −1/4.
   - (e) the same residual at Kt=0 is 0. This is the "discarded L-hole is not removable by R" check (N20:28).
   - (f) `orderSC … ≠ 0`.

**D2. Charge/Klein coefficient model (scalars, no A08).** Let ζ := `A01.canonicalRoot (2*h)` and χ(k,x) := `A01.integerCharacter ζ k x`.
- `cdwChargeCoeff h branches Ns x := χ(Ns L - Ns R - 1, x) * (Ch13.kleinPhase h Ns L * Ch13.kleinPhase h (cdwTarget branches Ns) R)`
- `scChargeCoeff h branches Ns x := χ(Ns R + Ns L, x) * (Ch13.kleinPhase h Ns L * Ch13.kleinPhase h (Ch13.lowerCharge Ns L) R)`

**Contracts.**
8. `klein_reflect_right : kleinPhase h (reflectLeft b Ns) R = kleinPhase h Ns R` and `klein_reflect_left : kleinPhase h (reflectLeft b Ns) L = -kleinPhase h (raiseCharge Ns L) L`. Both are general σ (parity of −N_L equals parity of N_L).
9. Label laws:
   - `cdw_target_dual : reflectLeft b (cdwTarget b (reflectLeft b Ns)) = raiseCharge (raiseCharge Ns R) L`
   - `scTarget b (raiseCharge (raiseCharge Ns R) L) = Ns`
   - `sc_target_dual : reflectLeft b (scTarget b (reflectLeft b Ns)) = raiseCharge (Ch13.lowerCharge Ns R) L`
   - `cdwTarget b (raiseCharge (lowerCharge Ns R) L) = Ns`
10. `cdw_charge_duality (hh : 0 < h) : cdwChargeCoeff h b (reflectLeft b Ns) x = χ(1,x) * star (scChargeCoeff h b (raiseCharge (raiseCharge Ns R) L) x)`. `sc_charge_duality` is the same with `cdwChargeCoeff h b (raiseCharge (lowerCharge Ns R) L) x`. Hand-checked for R<L and L<R; the sign ratio is (−1)^{−4N_L−2}.
11. `cdwChargeCoeff_norm`, `scChargeCoeff_norm : ‖·‖ = 1` (hh : 0<h). This is the scalar shadow of C₀=C₀′=1.

**D3. Parameter and mode-family duality.**

Data:
- `HyperbolicPair.dual hp := ⟨hp.c, -hp.s, by rw [neg_sq]; exact hp.hyperbolic_id⟩`.
- `dualParams (lp : A07Interactions.HyperbolicParams v1 v2) : A07Interactions.HyperbolicParams v1 (-v2)` with `u,c := lp.u, lp.c` and `s := -lp.s`. Proofs: `u_sq`/`match_v1` by `rw [neg_sq]`, `match_v2` by `linear_combination -lp.match_v2`.
- `abbrev ModeFamily (E) [AddCommGroup E] [Module ℂ E] := A06.Orientation → ℤ → Module.End ℂ E`.
- `speciesFamily h branches : ModeFamily (A05.FockSpace σ h) := fun η k => A05.rho h (A06.speciesOf branches η) k`.
- `dualFamily ρ := fun η k => match η with | .right => -ρ .right k | .left => ρ .left k`.
- `dressedCreatorOf ρ c s η (m:ℕ) := (c:ℂ) • ρ η m + (s:ℂ) • ρ (A07Interactions.oppositeOrientation η) (-m)`.
- `dressedAnnihilatorOf ρ c s η m := (c:ℂ) • ρ η (-m) + (s:ℂ) • ρ η̄ m`.
- `pairingModeOf ρ m v1 v2` mirrors `A07Interactions.pairingMode` term-for-term.
- `chiralPhaseOf ρ h M c s η x := Σ_{m∈Icc 1 M} (m:ℂ)⁻¹ • (χ(-(orientationSign η)*m, x) • dressedCreatorOf … + χ((orientationSign η)*m, x) • dressedAnnihilatorOf …)`.
- `xCDWOf ρ h M hp x := ((hp.c - hp.s : ℝ):ℂ) • (phase R + phase L)` and `xSCOf … := ((hp.c + hp.s : ℝ):ℂ) • (phase R - phase L)`.
- `logKernel h M (x y : ℤ) : ℝ := Σ_{m∈Icc 1 M} (1 - Real.cos (2*π*m*(x-y)/(2*h))) / m`.

**Contracts.**
12. Scalars:
    - `dual_dual`
    - `luttingerG_dual : luttingerG hp.dual = luttingerGInv hp`, plus its converse
    - `dualParams_pair : HyperbolicPair.ofParams (dualParams lp) = (HyperbolicPair.ofParams lp).dual`
    - `Ch17.v2Velocity (-g2) = -Ch17.v2Velocity g2`
13. Bridges to Core:
    - `dressedCreatorOf (speciesFamily h b) c s η m = A07Interactions.bogoliubovCreator h m c s b η` (and the annihilator)
    - `pairingModeOf (speciesFamily h b) m v1 v2 = A07Interactions.pairingMode h m v1 v2 b`
14. Family laws:
    - `dualFamily_involutive`
    - `dual_commutator : A02.commutator (dualFamily ρ η m) (dualFamily ρ η' n) = (if η = η' then 1 else -1 : ℂ) • A02.commutator (ρ η m) (ρ η' n)`
    - `dual_dressed_right : dressedCreatorOf (dualFamily ρ) c s .right m = -dressedCreatorOf ρ c (-s) .right m`
    - `_left`: `= dressedCreatorOf ρ c (-s) .left m`
    - the same two laws for annihilators
15. `dual_xCDW : xCDWOf (dualFamily ρ) h M hp x = -xSCOf ρ h M hp.dual x` and `dual_xSC : … = -xCDWOf ρ h M hp.dual x`.
16. Hamiltonian:
    - `dual_pairingMode : pairingModeOf (dualFamily ρ) m v1 v2 = pairingModeOf ρ m v1 (-v2)`
    - `dual_symmetric_zero_mode : Ch17.symmetricZeroModeScalar h vF g4 g2 b (reflectLeft b Ns) = Ch17.symmetricZeroModeScalar h vF g4 (-g2) b Ns`
    - the `canonicalMu` corollary, via `Ch17.zero_mode_scalar_canonical_mu`
17. Kernel: `logKernel_self = 0`, `logKernel_symm`, `logKernel_nonneg`.
18. `concrete_duality_witness`:
    - (a) `luttingerG concretePair = 1/4` and `luttingerG concretePair.dual = 4`
    - (b) `concretePair.dual ≠ concretePair`
    - (c) at h=8, m=1, `concreteNs`, `standardBranches`: `pairingModeOf (speciesFamily 8 standardBranches) 1 17 15 (groundKet 8 0) ≠ pairingModeOf … 1 17 (-15) (groundKet 8 0)`. The difference is 30•(ρρ ground); cite `A07Interactions.pairing_mode_ground_nonzero` and `A05.rho_lowering_budget_zero`.
    - (d) `logKernel 2 1 1 0 = 1`
    - (e) the linear-μ zero mode is not dual-invariant: `Ch17.zeroModeEnergyScalar 1 1 0 0 1 standardBranches ![0,1] ≠ Ch17.zeroModeEnergyScalar 1 1 0 0 1 standardBranches ![0,-1]` (π−1 vs 1).

**F1/F2 guards:**
- Every residual stays explicit, and no theorem drops it without a stated annihilation hypothesis.
- No conclusion is `True`.
- Witnesses use s≠0, v2≠0 and h≥2.
- Duality docstrings must say "family substitution / scalar coefficient model; not a finite-Fock unitary or A08 automorphism".
- Do not restate CH18 CCR/diagonalization; cite it.

**Defer / caveat only:**
- Def 20.4 W_J, Thm 20.5, [X_J(x),X_J(y)]=0, the variances 4gD₁ and 4g⁻¹D₁, the full (20.10) in A[[t]], the tensor-algebra D, and ω_{P*,f(N)}∘D = ω_{P,N}. These go to CH20b after CH19/A08 Core, building on its `omegaP`, contractions and series carrier.
- Theorem 14.5 bosonized single-factor equalities (the CAR-to-vertex dictionary).
- t=1 / analytic exponentials, power laws (GIA22:191,237), finite CAR particle–hole implementation of D, spectral equivalence, T-duality.
- A09 spin/charge, parity lattice and Umklapp go to CH21 (Lemma 21.8).
