# CH19 Phase A — reviewed source guidance (2026-10-15)

Prepared from a read-only literature/API analysis. **These are proposals, not verified truths.** Literature anchors point into `References/references-transcripts/` (the hub). Abbreviations: GIA3 = `giamarchi_2004/03_ch03_luttinger_liquids_pdf084-113.md`, GIA22 = `giamarchi_2004/2.2_physical_properties_and_correlation_functions.md`, SEN = `senechal_1999/06_tomonaga_luttinger.md`, ML = `mattis_2013/mattis_luttinger_2013_ch01_the_luttinger_model_and_its_solution.md`, VDS4 = `von_delft_schoeller_1998/04_bosonic_fock_space.md`, VDS9 = `von_delft_schoeller_1998/09_vertex_operators.md`, VDS10 = `von_delft_schoeller_1998/10_impurity_in_tll.md`. Note anchors: N19 = `notes/md/ch19_correlations.md`, A08 = `notes/appendices/a08_states_and_correlations.md`, TOC = `notes/md/TOC.md`.

Chapter policy: build the states, prove positivity and normalization, and prove both ordered contractions. **Do not identify formal states with finite-Fock density matrices unless a proof is supplied.**

## 0. Key fact: reuse frozen Core, do not re-invent

**Gate.** The verifier accepts only `import Bosonize` / `import Bosonize.Core.X` (`scripts/webllm/verify_phase_a.py:93-95`). CH19 Phase A therefore needs CH18 promoted unchanged to `Bosonize/Core/Ch18Bogoliubov.lean` (namespace `Bosonize.Ch18`) first. Import `Bosonize.Core.Ch18Bogoliubov`; it transitively brings in A05, A06, A07*, Ch08, Ch16 and Ch17.

Verified Core signatures:
- **A02** (`A02CARHilbert.lean`):
  - `FockSpace ι = EuclideanSpace ℂ (Occupation ι)` (L21-22). Lean's `inner ℂ x y` is conjugate-linear in `x`.
  - `ket_inner` (L164), `ket_norm : ‖ket S‖ = 1` (L169), `commutator A B = A*B - B*A` (L49).
- **A05** (`A05MultiSpecies.lean`):
  - `Operators σ h`, `rho h ν m` (L53), `groundKet h Ns = A02.ket (groundConfiguration h Ns)` (L40), so `‖groundKet‖ = 1`.
  - `rho_adjoint : adjoint (rho h ν m) = rho h ν (-m)` (L448).
  - `rho_cross_commute` (global, L465).
  - `rho_lowering_budget_zero h hh ν m K (hm : K < m) Ns v hv` (L576).
  - `ground_mem_budget h hh Ns hN K` (L583), `ground_ne_zero` (L597).
- **A06** (`A06ChiralFields.lean`):
  - `Orientation` derives only `DecidableEq`; it has **no `Fintype` instance** (L29-32).
  - `Branches`, `speciesOf`.
  - `marginAt h M K Ns ν := 2M + K + |Ns ν| ≤ h` (L49-50), `branchMargins` (L52-55).
  - `latticeCharacter h ζ k x := A01.integerCharacter ζ k x.val` (L57-59).
  - `lattice_character_conj` (needs `IsPrimitiveRoot ζ (2h)`, L128).
  - `joint_signed_current_commutator h K hh Ns ν m n (|m|+|n|+K+|Ns ν| ≤ h) v hv : commutator (rho m) (rho n) v = Ch10.schwingerCoefficient m n • v` (L223-228).
  - `Ch10.schwingerCoefficient m n = if m+n=0 then -m else 0`, so `[ρ_{-m}, ρ_n] = δ_{mn}·m`.
- **A01:** `integerCharacter ζ k x = ζ ^ (k*x)`. This is a **zpow**, so product laws need `ζ ≠ 0`. Also `canonicalRoot L`, `canonical_root_primitive`.
- **A07Interactions:**
  - `bogoliubovCreator h m c s branches η = c•ρ_{m,η} + s•ρ_{-m,η̄}` and `bogoliubovAnnihilator` (L255-265).
  - `bogoliubov_creator_adjoint` (L1113).
  - `bogoliubov_ccr_on_budget h M K m hh hm hcut c s hcs branches η Ns hmargin v hv` (L1174).
  - `oppositeOrientation` (L64), `HyperbolicParams` (L68-77).
- **A07** (FiniteNormalOrdering): `Letter M = Bool × Fin M × Bool` (branch bit false=R; creator bit true=ρ_m), `natMode p = p.2.1.val+1` (L33-42).
- **Ch08** (`Ch08Boson.lean`): single-branch polynomial template.
  - `Mode M = Fin M`, `weight i = i+1`, `creation = mulLeft X`, `annihilation = weight • pderiv`, `pairing`, `monomialNorm = ∏ wᵣ·r!` (L27-88).
  - `pairing_self_nonnegative` (L302), `pairing_self_eq_zero` (L315), `pairing_vacuum` (L337), `creation_pairing_adjoint` (L343), `ccr` (L392), `annihilation_vacuum` (L216).
  - `finite_ccr_obstruction` (L900), `compressed_commutator` (L889).
  - Ch08 is **not** directly reusable for two branches, because the weight is tied to the index of `Fin M`. Copy its definitions and proofs.
- **Ch16:** `excitedKet h Ns branches η m = ρ_{m,η} groundKet` (L100-103), `excited_ket_nonzero` (`marginAt h M m Ns …`, L363), `excited_ket_mem_budget` (L349), `standardBranches = ⟨0,1,_⟩` (L105). Also `Ch02.finite_dimensional_no_go` (L300).
- **Ch18** (staging, to become Core):
  - `HyperbolicPair ⟨c, s, hyperbolic_id⟩`, `luttingerG = (c-s)²`, `luttingerGInv`.
  - `luttingerG_mul_inv`, `luttingerGInv_eq_inv`, `hyperbolic_coeff_eq_luttinger : c²+s² = (g+g⁻¹)/2`, `HyperbolicPair.inverse_combination` (carrier-independent Lemma 18.3).
  - `LuttingerParams := HyperbolicParams`. It has **no** `g`/`ginv` fields.
  - `concretePair` (5/4, 3/4), `concreteParams`, `concreteCarrierH = 8`, `concreteCutoff = 2`, `concreteBudget = 2`, `concreteNs = 0`, `concreteBranches = standardBranches`, `concrete_bogoliubov_witness`.
  - `dressed_annihilator_ground_right/left` take `HyperbolicParams v1 v2`, **not** `HyperbolicPair`. CH19 either builds params or reproves the 2-line ground identity.

Mathlib availability under `import Bosonize`, checked with `lake env lean --stdin`:
- **Available:** `FreeAlgebra.lift/ι/induction`, `MvPolynomial.pderiv/lcoeff/constantCoeff`, `LinearMap.applyₗ`, `Matrix.diagonal/mulVec`, `Finsupp.prod`.
- **Unknown constant:** `Matrix.PosDef`.
- **No `Star` instance on `FreeAlgebra ℂ X`.**

**Missing in Core (CH19/A08 scope):** two-branch oscillator carrier; word algebra and its representation; constructed state ω₀; Bogoliubov map β; dressed state ω_P; Fock vector state; density operators and kernels; compressed-vacuum counterexample.

## A. Claims ledger

| id | statement (finite form) | literature / note anchor | note | tier | finite? |
|---|---|---|---|---|---|
| ch19.c01 | No finite unital rep of scalar CCR; two layers (finite Fock vs abstract CCR state) | N19:7-9; ML:1040-1044 (vacuum Schwinger term) | exists: `Ch02.finite_dimensional_no_go`, `Ch08.finite_ccr_obstruction` — cite | T2 | caveat |
| ch19.c02 | Two-branch polynomial carrier, weight m=i+1, Gram ⟨X^α,X^β⟩=δ∏α!m^α, positive definite; C=mult, A=m∂ adjoint; CCR/commuting relations | A08:5-18; VDS4:222-230 (b\|0⟩=0) | copy Ch08 pattern on `A06.Orientation × Fin M` | T1 | yes (new) |
| ch19.c03 | ω₀(a)=coeff₀(π(a)1)=⟨1,π(a)1⟩; ω₀(1)=1; word-Gram PSD; descends through CCR ideal | A08:18 | new | T1 | yes |
| ch19.c04 | β_{c,s}(C_ν)=cC_ν+sA_ν̄, β_{c,s}(A_ν)=cA_ν+sC_ν̄; β_{c,s}∘β_{c,−s}=id iff c²−s²=1 | A08:20-25; SEN:103-106; VDS10:414-420 | use `Ch18.HyperbolicPair.inverse_combination` | T1 | yes |
| ch19.c05 | ω_P:=ω₀∘β_{c,−s}: normalized, positive, ω_P(a·β(A))=0, ω_P(β(C)·a)=0 (19.1) | N19:11-16; A08:25 | wrong pullback direction is an F1 trap (B2) | T1 | yes |
| ch19.c06 | ω_P(A C)−ω_P(C A)=m for the same generator ⇒ ω_P is not multiplicative | N19:19 | non-vacuity witness | T2 | yes |
| ch19.c07 | ω_P(C_{R,i}A_{R,j})=δ m s², ω_P(A_{R,i}C_{R,j})=δ m c² | N19:25-33; A08:76-81; GIA3:202-206 (free ⟨b†b⟩=0, bb†=1−b†b); SEN:141-149 (cosh²/sinh² weights) | (19.2)/(19.3) | T1 | yes |
| ch19.c08 | same-branch CC and AA contractions vanish | A08:81; design L34 | needed independently | T1 | yes |
| ch19.c09 | ω_P(C_{R,i}C_{L,j})=ω_P(A_{R,i}A_{L,j})=−δ m c s; ω_P(C_{R,i}A_{L,j})=0 | VDS10:414-420 (mixing structure only) | **gap in note**; the only check that is sensitive to the sign of β | T1 | yes (new) |
| ch19.c10 | s²=(g+g⁻¹−2)/4, c²=(g+g⁻¹+2)/4 (c²+s² identity already in Ch18) | SEN:157-158 (θ_c=(K+1/K−2)/4); VDS10:414-420 | scalar part only; exponent meaning deferred | T2 | yes |
| ch19.c11 | ρ_R(x):=L⁻¹Σ_{m≤M}(ζ^{−mx}C_{R,m}+ζ^{mx}A_{R,m}), L=2h | N19:40-44; A08:85; GIA22:163-165 (continuum analogue) | oscillator part only; no zero mode | T2 | yes |
| ch19.c12 | D(x,y):=ω_P(ρ_R(x)ρ_R(y))=L⁻²Σ m(s²ζ^{−md}+c²ζ^{md}), d=x.val−y.val, ζ≠0 | N19:49-53; A08:82-86 | (19.5) ordered kernel | T1 | yes |
| ch19.c13 | (D(x,y)+D(y,x))/2 has coefficient (c²+s²)/2=(g+g⁻¹)/4 on both characters | N19:54-58 | symmetrized form must not replace the ordered one | T2 | yes |
| ch19.c14 | D(x,y)−D(y,x)=L⁻²Σ m(ζ^{md}−ζ^{−md}), independent of (c,s) | derived (uses c²−s²=1) | F1 cross-check | T2 | yes (new) |
| ch19.c15 | D(x,x)=(c²+s²)M(M+1)/(2L²), real and >0 for M≥1 | ch19 draft L127-131 | positivity consistency check | T2 | yes |
| ch19.c16 | s=0 ⇒ D = free kernel (c²=1, s²=0) | N19:33 | free-vacuum check | T2 | yes |
| ch19.c17 | vector state ⟪ψ,Xψ⟫: ⟪Ω,1Ω⟫=1; ⟪ψ,X†Xψ⟫=‖Xψ‖² | A08:45 (density-matrix framing) | finite, exact | T2 | yes (new) |
| ch19.c18 | ⟪Ω,ρ_{−m}ρ_nΩ⟫=δ_{mn}m; ⟪Ω,ρ_mρ_{−n}Ω⟫=⟪Ω,ρ_mρ_nΩ⟫=⟪Ω,ρ_{−m}ρ_{−n}Ω⟫=0 under `marginAt h M 0` | ML:1040-1044; VDS4:222-230; GIA3:202-206 | Fock-side free contractions | T1 | yes (new) |
| ch19.c19 | ⟪Ω,ρ_R(x)ρ_R(y)Ω⟫ = free kernel = D at (c,s)=(1,0) | — | **scalar equality only, no state identification** | T1 | yes (new) |
| ch19.c20 | bare ground vs dressed modes: ⟪Ω,C̃_ηÃ_ηΩ⟫=m s², ⟪Ω,Ã_ηC̃_ηΩ⟫=m c²; ≠0 when s≠0 | ML:1114, 1146 (new ground state ≠ Ψ₀; infinite model) | finite form of "Ω is not the dressed vacuum" | T1 | yes (new) |
| ch19.c21 | degree≤1 two-mode slice: Q_Rᴴ Q_R+Q_Lᴴ Q_L=diag(2s²,c²,c²); s≠0 ⇒ common kernel {0}, no trace-1 ρ with Q_Rρ=Q_Lρ=0; s=0 ⇒ kernel ∋ 1 | A08:44-69 | (5/3, 4/3) gives diag(32/9, 25/9, 25/9) | T1 | yes (new) |
| ch19.c22 | ground state of a finite interacting H and a comparison map ω_P ↔ budget states | A08:72; N19:16 | none constructed | — | **defer** |
| ch19.c23 | power laws, log kernels, Gaussian vertex identities, Wick for vertices | GIA22:169-193, 183-187; SEN:141-166, 216-222; VDS9:344-377; GIA3:206-212 | analytic/formal | — | **defer** (CH20 / analytic module) |
| ch19.c24 | thermal states ⟨b†b⟩=f_B | GIA3:204-206 | not in scope | — | defer |
| ch19.c25 | witnesses: M=2, concretePair ⇒ 9/8, 25/8, −15/8; D(0,0)=51/2048 at h=8; Fock: 2, 9/8, 3/256 | internal | F2 | T2 | yes (norm_num) |

## B. Convention flags (must respect)
1. **Generators.** Project C_{ν,m} ↔ ρ_{m,ν} (m>0 raises) and A_{ν,m} ↔ ρ_{−m,ν}. `A02.commutator A C = +m`. `OscGen` bit `true` = creator (as in the A07 Letter creator bit). The abstract index `i : Fin M` ↔ m = i.val+1 (Ch08 `weight`, A07 `natMode`). The Fock side uses `m ∈ Finset.Icc 1 M` (as Core/Ch17/Ch18 do).
2. **Direction of β.** β_{c,s} matches A07 `bogoliubovCreator`. The dressed state is ω_P = ω₀∘β_{c,−s} (A08:25). ω₀∘β_{c,s} reproduces s² and c² **identically** but flips the cross contraction to +mcs. Only c09 and the annihilation laws detect the error.
3. **Sign of s.** s>0 is repulsive (CH18 flag 3). SEN's ξ has the opposite sign. s² and c² do not care; every cs term does.
4. **Ordered vs symmetrized.** Keep the complex ordered kernel. A cosine-only kernel describes a different (symmetrized) observable (A08:89; N19:58).
5. **Phases.** `integerCharacter` is a zpow, so kernel identities need `ζ ≠ 0` (they are false at ζ=0). `latticeCharacter … (x − y)` forms need `IsPrimitiveRoot ζ (2*h)`. Witnesses use `A01.canonicalRoot (2*8)`.
6. **Lengths and cutoffs.** L = 2h is the lattice length. M is the abstract mode cutoff and is independent of L. Do not assume M ≤ h on the abstract side. The Fock side needs `marginAt` (2M+K+|Ns| ≤ h).
7. **Positivity encoding.** There is no Mathlib `star` on `FreeAlgebra ℂ X`. Never use `StarAlgHom`/`≃ₐ⋆` or a multiplicative functional as a state. Encode positivity as PSD word Gram sums with `wordDagger` (reverse + swap C↔A, real coefficients).
8. **No Fintype on `A06.Orientation`.** Use `Finsupp.prod` for the monomial norm and `∑ i : Fin M` with an explicit branch. Do not add an instance unless it is needed.
9. Never name the Luttinger parameter `K` (K is the budget); use `Ch18.luttingerG`. Do not port continuum amplitudes such as GIA22's K/(2π²) or 1/π∇φ normalizations.
10. **Mathlib.** `Matrix.PosDef` is unavailable despite A08:68. State kernels and Gram diagonals explicitly.

## C. Review of the user drafts (untracked, unverified)

**`ch19-draft-gemini-pro.txt`**
- **Reusable:**
  - kernel shape and ordering (L91-96);
  - symmetrized algebra (L105-114);
  - diagonal lemma (L127-131);
  - `Fin M` indexing with m = i.val+1 (L58, L62);
  - the four contraction statements (L56-68).
- **Rejected:**
  - `import Mathlib` (L13).
  - Bare `-- BEGIN_MODULE` with no path (L19), and a stray `` ```eof `` (L144).
  - Free variables `bareCreator/bareAnnihilator` and `omega_P : A →ₗ[ℂ] ℂ` (L30, L42).
  - Abstract `[Ring A][Algebra ℂ A][StarRing A]` with no `StarModule` (L26, L133-138).
  - Adjoint relations supplied as a hypothesis `hstar` (L135-136).
  - `lp.g`/`lp.ginv` fields that do not exist (L116-118); cite `Ch18.hyperbolic_coeff_eq_luttinger` instead.
- **F1 (false as stated):**
  - L44-68 and L98-125 are claimed for an *arbitrary* linear map. For example, ω=0 refutes `interactingVacuum_normalized`, and nothing ties `omega_P` to `hp`.
  - ζ is unconstrained (L77, L98), so the kernel fails at ζ=0.
- **F2:** none of the hypotheses force the state to exist. Replace with constructed `A08.omegaP`.

**`ch19_phase_ab_design.md`**
- **Keep:**
  - carrier separation (L11);
  - non-multiplicative state (L49);
  - "anomalous zeros proved independently" (L34);
  - ordered ≠ symmetrized (L52);
  - L vs M independence (L45);
  - exclusions (B7, L75).
- **Fix:**
  - The dependency gate (L20) is outdated: CH18 becomes Core, and A08 is co-staged in this cycle.
  - Site type: Core uses `ZMod (2*h)` (= `Ch01.Lattice`) (L18).
  - B2 asks for "distinct-branch commuting as explicit input" (L65). That is an F2 pattern; on the constructed carrier it is a theorem.
  - "g=0 inverse" (L40) is moot: `luttingerG_mul_inv` gives g≠0 for every pair.

**`a08_phase_b_stub.txt`**
- **Reusable:** `bareCreator = mulLeft X`, `bareAnnihilator = (m+1)•pderiv` (L37-42); the contraction statements (L98-104); the density/kernel shape (L108-119, add `ζ ≠ 0`).
- **Rejected:**
  - `import Mathlib` (L12).
  - Data `:= sorry` (`polyGramForm` L32-33, `omega0` L46-47, `betaAutomorphism` L50-52, `shiftF`, `phaseZ`, `omegaPN`, `Q_R`… L72-137).
  - Charge/tensor/Weyl/D₁ material (L59-150): CH20 per TOC:127-131.
- **F1:**
  - `Module.End ℂ (PolyCarrier M) ≃ₐ⋆[ℂ] …` (L50-52) is ill-typed: there is no star on End of a non-Hilbert carrier.
  - β is not implementable on all endomorphisms: the squeezed vacuum is not a polynomial. Define β on the word algebra instead.
  - `omega0` on all of `Module.End` (L46) blocks the pullback.
- **F2:**
  - `common_kernel_can_be_zero` (L90-93) is ∃-quantified and holds trivially (e.g. Q_R = 1). It must be about the specific compressed matrices.
  - `weyl_correlator_*_eval : True` (L146-150) is vacuous.

### Reusable excerpt (verbatim from the A08 stub, adapt to `OscMode`)
```text
noncomputable def bareCreator (ν : A06.Orientation) (m : Fin M) : Module.End ℂ (PolyCarrier M) :=
  LinearMap.mulLeft ℂ (MvPolynomial.X (ν, m))
noncomputable def bareAnnihilator (ν : A06.Orientation) (m : Fin M) : Module.End ℂ (PolyCarrier M) :=
  ((m.val + 1 : ℕ) : ℂ) • (MvPolynomial.pderiv (ν, m)).toLinearMap
```

## D. Recommended Phase A scope

There are two modules, in dependency order, inside one lean fence with Core imports first (`import Bosonize.Core.Ch18Bogoliubov`):

1. `-- BEGIN_MODULE BosonizeStubs/A08OscillatorStates.lean` … `-- END_MODULE BosonizeStubs/A08OscillatorStates.lean`, namespace `Bosonize.A08`.
   - This is the real Appendix A08, so the CH18 N8 objection does not apply.
   - The name leaves room for `A08ChargeVertices` in CH20.
2. `-- BEGIN_MODULE BosonizeStubs/Ch19Correlations.lean` … `-- END_MODULE …`, namespace `Bosonize.Ch19`.
   - Use `variable {σ : Type*} [Fintype σ] [LinearOrder σ]` only in the Fock section.

### D1. A08 data (complete, no sorry)
```text
abbrev OscMode (M : ℕ) := A06.Orientation × Fin M
def oscWeight {M : ℕ} (p : OscMode M) : ℕ := p.2.val + 1
abbrev OscPoly (M : ℕ) := MvPolynomial (OscMode M) ℂ
def oscMonomialNorm {M : ℕ} (r : OscMode M →₀ ℕ) : ℕ := r.prod (fun p k => oscWeight p ^ k * k.factorial)
noncomputable def oscPairing (M : ℕ) (p q : OscPoly M) : ℂ :=
  ∑ r ∈ p.support, star (MvPolynomial.coeff r p) * (oscMonomialNorm r : ℂ) * MvPolynomial.coeff r q
noncomputable def oscCreation (M) (p : OscMode M) : Module.End ℂ (OscPoly M) := LinearMap.mulLeft ℂ (MvPolynomial.X p)
noncomputable def oscAnnihilation (M) (p : OscMode M) : Module.End ℂ (OscPoly M) :=
  (oscWeight p : ℂ) • (MvPolynomial.pderiv p).toLinearMap
abbrev OscGen (M : ℕ) := Bool × OscMode M          -- true = C (ρ_m), false = A (ρ_{-m})
abbrev OscAlgebra (M : ℕ) := FreeAlgebra ℂ (OscGen M)
noncomputable def creatorGen (M) (ν) (i : Fin M) : OscAlgebra M := FreeAlgebra.ι ℂ (true, (ν, i))
noncomputable def annihilatorGen (M) (ν) (i : Fin M) : OscAlgebra M := FreeAlgebra.ι ℂ (false, (ν, i))
noncomputable def oscRep (M) : OscAlgebra M →ₐ[ℂ] Module.End ℂ (OscPoly M) :=
  FreeAlgebra.lift ℂ (fun g => if g.1 then oscCreation M g.2 else oscAnnihilation M g.2)
noncomputable def omega0 (M) : OscAlgebra M →ₗ[ℂ] ℂ :=
  (MvPolynomial.lcoeff ℂ 0) ∘ₗ (LinearMap.applyₗ (1 : OscPoly M)) ∘ₗ (oscRep M).toLinearMap
noncomputable def bogoliubovMap (M) (c s : ℝ) : OscAlgebra M →ₐ[ℂ] OscAlgebra M :=
  FreeAlgebra.lift ℂ (fun g => (c : ℂ) • FreeAlgebra.ι ℂ g +
    (s : ℂ) • FreeAlgebra.ι ℂ (!g.1, (A07Interactions.oppositeOrientation g.2.1, g.2.2)))
noncomputable def omegaP (M) (hp : Ch18.HyperbolicPair) : OscAlgebra M →ₗ[ℂ] ℂ :=
  omega0 M ∘ₗ (bogoliubovMap M hp.c (-hp.s)).toLinearMap
abbrev OscWord (M : ℕ) := List (OscGen M)
def wordDagger {M} (w : OscWord M) : OscWord M := (w.map fun g => (!g.1, g.2)).reverse
noncomputable def wordElement (M) (w : OscWord M) : OscAlgebra M := (w.map (FreeAlgebra.ι ℂ)).prod
noncomputable def gramSum (M) {n : ℕ} (ω : OscAlgebra M →ₗ[ℂ] ℂ) (w : Fin n → OscWord M) (z : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, star (z i) * z j * ω (wordElement M (wordDagger (w i)) * wordElement M (w j))
noncomputable def vectorState (h) (ψ : A05.FockSpace σ h) (X : A05.Operators σ h) : ℂ := inner ℂ ψ (X ψ)
def compressedQR (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℂ := Matrix.of ![![0, (c:ℂ), 0], ![0, 0, 0], ![(s:ℂ), 0, 0]]
def compressedQL (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℂ := Matrix.of ![![0, 0, (c:ℂ)], ![(s:ℂ), 0, 0], ![0, 0, 0]]
def noteCompressedPair : Ch18.HyperbolicPair := ⟨5/3, 4/3, by norm_num⟩
```
- **Compressed-matrix basis:** (1, X_R, X_L) at mode m=1, which is orthonormal because every norm is 1. Q_R = cD_R + sX̃_L and Q_L = cD_L + sX̃_R (A08:47-52). The entries were checked by hand; human review should recheck them.
- **Where `vectorState` lives:** it sits in a `variable {σ}` section of A08, or in Ch19's Fock section.

### D2. A08 theorem contracts (each `:= by sorry`)
- **Carrier:**
  - `oscPairing_monomial` (δ · `oscMonomialNorm`);
  - `oscPairing_conj`;
  - `oscPairing_self_nonneg` (`0 ≤ re`);
  - `oscPairing_self_eq_zero` (↔ p=0);
  - `oscCreation_pairing_adjoint`;
  - `osc_ccr : A02.commutator (oscAnnihilation M p) (oscCreation M q) = if p = q then (oscWeight p : ℂ) • 1 else 0`;
  - `osc_annihilators_commute`, `osc_creators_commute`;
  - `oscAnnihilation_one`.
- **Vacuum state:**
  - `omega0_eq_pairing : omega0 M a = oscPairing M 1 (oscRep M a 1)`;
  - `omega0_one`;
  - `omega0_gramSum : (gramSum M (omega0 M) w z).im = 0 ∧ 0 ≤ (gramSum M (omega0 M) w z).re`;
  - `omega0_ccr_descends : omega0 M (a * (ι(false,p) * ι(true,q) − ι(true,q) * ι(false,p) − (if p = q then (oscWeight p : ℂ) else 0) • 1) * b) = 0`.
- **Bogoliubov map:**
  - `bogoliubovMap_inverse (hcs : c^2 - s^2 = 1) : (bogoliubovMap M c s).comp (bogoliubovMap M c (-s)) = AlgHom.id ℂ _`, and the reversed composition.
  - `bogoliubovMap_word_adjoint : oscPairing M x (oscRep M (bogoliubovMap M c s (wordElement M (wordDagger w))) y) = oscPairing M (oscRep M (bogoliubovMap M c s (wordElement M w)) x) y` (real c, s). This is the Phase B route to positivity without an algebra star.
- **Dressed state:**
  - `omegaP_one`, `omegaP_gramSum`, `omegaP_ccr_descends`;
  - `omegaP_mul_dressed_annihilator : omegaP M hp (a * bogoliubovMap M hp.c hp.s (annihilatorGen M ν i)) = 0`;
  - `omegaP_dressed_creator_mul : omegaP M hp (bogoliubovMap M hp.c hp.s (creatorGen M ν i) * a) = 0`;
  - `omegaP_commutator : omegaP (A_{ν,i} * C_{ν,i}) − omegaP (C_{ν,i} * A_{ν,i}) = ((i.val+1 : ℕ) : ℂ)` (non-multiplicativity).
- **Finite Fock:**
  - `vectorState_ground_one (h Ns) : vectorState h (A05.groundKet h Ns) 1 = 1`;
  - `vectorState_adjoint_mul_self : vectorState h ψ (LinearMap.adjoint X * X) = ((‖X ψ‖ ^ 2 : ℝ) : ℂ)`.
- **Compressed vacua:**
  - `compressed_gram : (compressedQR c s)ᴴ * compressedQR c s + (compressedQL c s)ᴴ * compressedQL c s = Matrix.diagonal ![2 * (s:ℂ)^2, (c:ℂ)^2, (c:ℂ)^2]`;
  - `compressed_common_kernel_trivial (hp) (hs : hp.s ≠ 0) (v) (hR : (compressedQR hp.c hp.s).mulVec v = 0) (hL : …) : v = 0`;
  - `compressed_no_vacuum_density (hp) (hs) : ¬ ∃ ρ, compressedQR hp.c hp.s * ρ = 0 ∧ compressedQL hp.c hp.s * ρ = 0 ∧ ρ.trace = 1`;
  - `compressed_kernel_of_s_zero (c) : (compressedQR c 0).mulVec (Pi.single 0 1) = 0 ∧ (compressedQL c 0).mulVec (Pi.single 0 1) = 0` (shows `hs` is necessary);
  - `note_compressed_witness` (diag(32/9, 25/9, 25/9) at `noteCompressedPair`).

### D3. Ch19 data (complete)
```text
noncomputable def densityKernel (h M : ℕ) (ζ : ℂ) (c2 s2 : ℝ) (d : ℤ) : ℂ :=
  (((2 * h : ℕ) : ℂ)⁻¹) ^ 2 * ∑ m ∈ Finset.Icc 1 M, (m : ℂ) *
    ((s2 : ℂ) * A01.integerCharacter ζ (-(m : ℤ)) d + (c2 : ℂ) * A01.integerCharacter ζ (m : ℤ) d)
noncomputable def oscDensityR (h M : ℕ) (ζ : ℂ) (x : ZMod (2 * h)) : A08.OscAlgebra M :=
  (((2 * h : ℕ) : ℂ)⁻¹) • ∑ i : Fin M,
    (A06.latticeCharacter h ζ (-((i.val + 1 : ℕ) : ℤ)) x • A08.creatorGen M .right i +
     A06.latticeCharacter h ζ ((i.val + 1 : ℕ) : ℤ) x • A08.annihilatorGen M .right i)
noncomputable def orderedDensityCorrelation (h M) (ζ) (hp : Ch18.HyperbolicPair) (x y : ZMod (2*h)) : ℂ :=
  A08.omegaP M hp (oscDensityR h M ζ x * oscDensityR h M ζ y)
noncomputable def fockDensityR (h M) (ζ) (branches : A06.Branches σ) (x : ZMod (2*h)) : A05.Operators σ h :=
  (((2 * h : ℕ) : ℂ)⁻¹) • ∑ m ∈ Finset.Icc 1 M,
    (A06.latticeCharacter h ζ (-(m : ℤ)) x • A05.rho h branches.rightSpecies (m : ℤ) +
     A06.latticeCharacter h ζ (m : ℤ) x • A05.rho h branches.rightSpecies (-(m : ℤ)))
def freePair : Ch18.HyperbolicPair := ⟨1, 0, by norm_num⟩
```

### D4. Ch19 theorem contracts (each `:= by sorry`; write d := (x.val : ℤ) − (y.val : ℤ))

**Abstract layer** (hypothesis `hp : Ch18.HyperbolicPair` only):
1. `omegaP_creator_annihilator_right (i j : Fin M) : A08.omegaP M hp (C_{R,i} * A_{R,j}) = if i = j then ((i.val+1 : ℕ) : ℂ) * (hp.s : ℂ)^2 else 0` (19.2).
2. `omegaP_annihilator_creator_right`: the same with `(hp.c : ℂ)^2` (19.3).
3. `omegaP_creator_creator_right`, `omegaP_annihilator_annihilator_right`: = 0.
4. Cross-branch contractions (direction detector, ledger c09):
   - `omegaP_cross_creator_creator : ω(C_{R,i} C_{L,j}) = if i = j then -(((i.val+1 : ℕ) : ℂ) * hp.c * hp.s) else 0`;
   - `omegaP_cross_annihilator_annihilator`: likewise;
   - `omegaP_cross_creator_annihilator`: = 0.
5. `ordered_density_kernel [NeZero (2*h)] (hζ : ζ ≠ 0) : orderedDensityCorrelation h M ζ hp x y = densityKernel h M ζ (hp.c^2) (hp.s^2) d` (19.5).
6. `ordered_density_kernel_lattice (hζ : IsPrimitiveRoot ζ (2*h))`: the same with `A06.latticeCharacter h ζ (±m) (x - y)`.
7. `density_commutator_expectation (hζ : ζ ≠ 0) : D(x,y) − D(y,x) = densityKernel h M ζ 1 (-1) d` (independent of hp).
8. `symmetrized_density_kernel (hζ) : (D(x,y)+D(y,x))/2 = densityKernel h M ζ q q d` with `q = (Ch18.luttingerG hp + (Ch18.luttingerG hp)⁻¹)/4`.
9. `s_sq_eq_luttinger : hp.s^2 = (g + g⁻¹ - 2)/4`; `c_sq_eq_luttinger : hp.c^2 = (g + g⁻¹ + 2)/4`.
10. Diagonal:
    - `density_kernel_diagonal (hζ : ζ ≠ 0) : D(x,x) = (((hp.c^2+hp.s^2) * (M*(M+1)/2 : ℝ) / ((2*h : ℕ) : ℝ)^2 : ℝ) : ℂ)`;
    - `density_kernel_diagonal_pos (hζ : ζ ≠ 0) (hh : 0 < h) (hM : 1 ≤ M) : 0 < (D(x,x)).re`.
11. `ordered_density_free (hs : hp.s = 0) (hζ) : D(x,y) = densityKernel h M ζ 1 0 d`.

**Finite Fock layer** (`hh : 0 < h`, `hN : A05.admissible h Ns`, `branches`, r := `branches.rightSpecies`):

12. `ground_lowering_raising (hm : 1 ≤ m) (hn : 1 ≤ n) (hmM : m ≤ M) (hnM : n ≤ M) (hmargin : A06.marginAt h M 0 Ns r) : vectorState h Ω (rho r (-m) * rho r n) = if m = n then (m : ℂ) else 0`.
13. `ground_raising_lowering (hn : 1 ≤ n)`; `ground_raising_raising` and `ground_lowering_lowering` (m, n ≥ 1): all = 0.
14. `excited_ket_norm_sq (hmargin : A06.marginAt h M 0 Ns (A06.speciesOf branches η)) : ‖Ch16.excitedKet h Ns branches η m‖^2 = m`.
15. `ground_dressed_number (hp : Ch18.HyperbolicPair) (hmargin : A06.branchMargins h M 0 Ns branches) : vectorState h Ω (bogoliubovCreator h m hp.c hp.s branches η * bogoliubovAnnihilator h m hp.c hp.s branches η) = (m : ℂ) * (hp.s : ℂ)^2`.
16. `ground_dressed_reverse`: the reversed order equals `(m : ℂ) * (hp.c : ℂ)^2`.
17. `ground_not_dressed_vacuum (hs : hp.s ≠ 0)`: the expectation in 15 is ≠ 0.
18. `fock_ground_density_kernel [NeZero (2*h)] (hζ : ζ ≠ 0) (hmargin : marginAt h M 0 Ns r) : vectorState h Ω (fockDensityR h M ζ branches x * fockDensityR … y) = densityKernel h M ζ 1 0 d`.
19. `fock_ground_matches_free_state`: the same scalar equals `orderedDensityCorrelation h M ζ freePair x y`. Its docstring must state: scalar equality at s=0 only; not an identification of states.
20. `concrete_correlation_witness`, with conjuncts:
    - M=2, `Ch18.concretePair`, i = (1 : Fin 2):
      - ω_P(C_{R,1}A_{R,1}) = 9/8;
      - ω_P(A_{R,1}C_{R,1}) = 25/8;
      - ω_P(C_{R,1}C_{L,1}) = −15/8;
      - `orderedDensityCorrelation 8 2 (A01.canonicalRoot (2*8)) concretePair 0 0 = 51/2048`.
    - Fock, h=8, `Ch18.concreteNs`, `Ch18.concreteBranches`, m=2:
      - `A06.branchMargins 8 2 0 concreteNs concreteBranches`;
      - `vectorState 8 Ω (rho 8 0 (-2) * rho 8 0 2) = 2`;
      - ⟪Ω, C̃_RÃ_RΩ⟫ = 9/8 ≠ 0;
      - ⟪Ω, ρ_R(0)ρ_R(0)Ω⟫ = 3/256.

**Phase B dependencies:**
- 1–4: compute ω₀ directly on polynomials. For example, β_{c,−s}(C_R)β_{c,−s}(A_R)·1 = s²m − cs X_RX_L.
- 12: `rho_lowering_budget_zero` (K=0) + `joint_signed_current_commutator` (K=0) + `A02.ket_inner`.
- 15: `bogoliubov_creator_adjoint` + the ground identity Ã_ηΩ = s·excitedKet(η̄), which must be reproved for `HyperbolicPair` + 14.
- 16: `bogoliubov_ccr_on_budget` (K=0).

Do not restate `Ch18.hyperbolic_coeff_eq_luttinger`, `luttingerG_mul_inv` or `concrete_bogoliubov_witness`; cite them.

### D5. Risk register
- **F1:**
  - wrong β direction (B2), detected by 4;
  - unconstrained ζ;
  - a cosine kernel standing in for the ordered one;
  - claiming that ω_P equals a vector or density state of `A05.FockSpace` (forbidden; only theorem 19 at s=0);
  - transcription errors in the Fin 3 matrices;
  - "exponent θ_c" or power-law language in docstrings.
- **F2:**
  - states or adjoint/CCR relations supplied as hypotheses or variables;
  - ∃-only counterexamples;
  - `True` conclusions;
  - only s=0 witnesses — every witness above has s≠0, except the explicit free check 11/19 and `compressed_kernel_of_s_zero`, which shows the necessity of `hs`.

**Defer / caveat only:**
- charge lattice, Klein shifts, ω_{P,N}, Weyl vertices, `exp_formal`, D₁, CDW/SC Gaussian formulas (A08:30-40, 91-127; TOC:127-131 → CH20);
- power laws and continuum limits (A08:129-131; N19:66-67);
- finite interacting ground state and comparison maps (A08:72);
- unitary implementer e^{iS} (ML:1140-1146);
- thermal states (GIA3:204);
- time dependence;
- left-branch kernel (mirror; optional);
- general Wick moments beyond two points (VDS9:344-377).
