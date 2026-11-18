# Bosonize-Lean: Project-State Review and Next-Phase Research/Implementation Plan

**Review date:** 2026-10-17  
**Planning baseline:** GitHub `lufreitas0000/bosonize-lean`, `main` at `0d185dfbadd6b8efe1eba752d2520873b35cdc0a` (latest observed commit, 2026-10-16); user-supplied *Constructive 1+1D Lattice Bosonization: Finite Constructions and Algebraic Models* (`main(2).pdf`, 239 PDF pages, generated 2026-10-17).  
**Purpose:** An evidence-bounded review, followed by a specification for an independent Google Antigravity *planning* agent. This is **not** an implementation authorization, Lean proof certificate, or proposal to overwrite frozen Core modules.

## Executive decision

**Do not start by implementing a KT beta-function theorem.** The next productive increment is a generic finite-dimensional *decimation calculus* that (i) works on genuine restricted carriers, (ii) distinguishes total excitation-energy shells from high-mode occupation elimination, (iii) handles cross-charge-sector intermediate states, and (iv) preserves explicit compression and perturbative remainders. A discrete OPE and a coupling-extraction convention can then be placed on top of it, initially in the uncompressed oscillator algebra. A KT scaling-limit theorem is a subsequent research problem rather than the acceptance criterion for the first implementation sprint.

**Recommended division of work:** Finish/revalidate already scheduled CH20b–CH21 and canonical closure according to the existing roadmap, while opening the RG extension as a **separately approved design/Phase-A package**. Do not silently turn the RG proposal into a prerequisite of the canonical 21-chapter release. Any upstream mathematical inconsistency discovered by the extension must be triaged immediately as a narrowly scoped correctness issue.

### Evidence levels used below

- **R — Repository-observed:** Paths, declarations, recorded validations and recent commits inspected via the connected GitHub repository. A historical CI report is evidence of the run it describes, not proof that I performed a fresh build today.
- **M — Manuscript-observed:** Claims in the supplied 239-page PDF. A theorem printed in the manuscript is **not** automatically a compiled Lean theorem.
- **D — Mathematical deduction:** A consequence established here from displayed assumptions; it may still require formalization.
- **P — Proposed:** Architecture, phase plan, Lean interface sketch or target proof, not implemented/verified.
- **E — External academic reference:** Bibliography checked against publisher or journal records; source authority does not substitute for a Lean proof.

## 1. Actual project state: source of truth and discrepancies

### 1.1 Repository snapshot (R)

| Component | Observed state | Evidence / limitation |
| --- | --- | --- |
| CH01–18 | Marked Phase C, promoted/frozen Core, with CH18 prose issues outstanding. | [`README.md`](https://github.com/lufreitas0000/bosonize-lean/blob/0d185dfbadd6b8efe1eba752d2520873b35cdc0a/README.md), [`adaptative_roadmap.md`](https://github.com/lufreitas0000/bosonize-lean/blob/0d185dfbadd6b8efe1eba752d2520873b35cdc0a/adaptative_roadmap.md). |
| CH19 / A08 | Marked Phase C; 62 theorem contracts promoted; fresh local audits recorded. | [`note/ch19_phase_c_validation_2026-10-16.md`](https://github.com/lufreitas0000/bosonize-lean/blob/0d185dfbadd6b8efe1eba752d2520873b35cdc0a/note/ch19_phase_c_validation_2026-10-16.md). |
| CH20 finite order parameters/duality | Marked Phase C; 64 finite theorem contracts promoted to `Bosonize/Core/Ch20CDW.lean`; local audits recorded. | [`docs/webllm/chapters/ch20.json`](https://github.com/lufreitas0000/bosonize-lean/blob/0d185dfbadd6b8efe1eba752d2520873b35cdc0a/docs/webllm/chapters/ch20.json), [`note/ch20_phase_c_validation_2026-10-16.md`](https://github.com/lufreitas0000/bosonize-lean/blob/0d185dfbadd6b8efe1eba752d2520873b35cdc0a/note/ch20_phase_c_validation_2026-10-16.md). This acceptance is for finite CH20 scope, not the formal-vertex bridge. |
| CH20b | Pending: full Wick/state/vertex transport, comparison with finite CAR, and residuals. | Roadmap and CH20 validation explicitly defer these. |
| CH21 | Pending new/revalidated specification and A–B–C cycle; roadmap mentions a **historical 47-contract draft**, not a verified current staging artifact. | No `ch21.json` in inspected chapter-status directory; `BosonizeStubs/` contains only `.gitkeep` in the observed default branch. Do **not** label CH21 proved on the basis of the PDF. |
| A10 SW support | Already present in frozen Core: `Bosonize/Core/A10DiscreteSchriefferWolff.lean`, 11 proved-target names observable in source. | It includes matrix generator, 2×2/3×3 witnesses, shell projectors, compressed BCH polynomial and a repeated-mode-one witness. Critically, the companion records that the *ambient-to-restricted-carrier bridge is not yet proved*. |
| Lean toolchain | `leanprover/lean4:v4.35.0-rc4`; `lakefile.toml` imports Mathlib and enforces warnings as errors for Core. | Pin observed. Do not assume current Mathlib API names beyond actual local source. |
| Repository validation | `make ci` runs repository scripts and both Lean libraries; recorded Phase C local validations exist. | I inspected the commands/receipts; **I did not run Lean locally**. No claim of a fresh 2026-10-17 CI or global axiom audit. |
| Book | Tracked `notes/latex/main.tex` includes Chapters 1–19 and Appendix A07; CH20–21 LaTeX files are not included in that tracked master. | [`notes/latex/main.tex`](https://github.com/lufreitas0000/bosonize-lean/blob/0d185dfbadd6b8efe1eba752d2520873b35cdc0a/notes/latex/main.tex). |

Other observed repository controls: `.agents/skills/formalizer/SKILL.md`; `docs/spec/stub_locks.v2.json`; `docs/spec/core_locks.json`; `docs/companion/`; `scripts/guards/`; `scripts/webllm/`; `note/` validation receipts. Follow these before inventing additional workflow tooling. `Bosonize.lean` imports the A10, A08, CH19 and CH20 Core modules.

**Important version/provenance discrepancy (R + M):** The **uploaded** 239-page PDF includes CH20, CH21 and Appendix G and is dated 2026-10-17; the **tracked GitHub master** still stops at CH19 plus A07. Do not infer that the uploaded PDF corresponds to `main` or that its additional mathematical text has passed the book's independent editorial/Lean alignment gates. First create a source-hash/provenance mapping, determine whether these are uncommitted local sections, a separately assembled master or a newer untracked build, and preserve them without overwriting anything.

### 1.2 Exact reusable declarations observed (R)

- `Bosonize.Ch07`: `fixedBudget`, `boxBudget`, `fixedProjection`, `boxProjection`, `excitationObservable`, `totalExcitation`, `fixed_projection_idempotent`, `fixed_projection_adjoint`, and related basis/energy lemmas.
- `Bosonize.Ch08`: `Exponents`, `BudgetIndex`, `FiniteFock`, `energy`, `budget`, `projection`, `finiteOperator`, `hamiltonian`, `finite_hamiltonian_ket`, `compressed_commutator`, `finite_ccr_obstruction`, `expNil`, and polynomial/formal-series components. `FiniteFock M K` is a **finite-dimensional EuclideanSpace**; the ambient `Polynomial M` is not finite-dimensional.
- `Bosonize.A03`: generic coordinate projector and projection-product remainder utilities (inspect exact signatures before reuse).
- `Bosonize.Ch14`: typed projected maps, physical field candidates, and explicit projection residuals.
- `Bosonize.A05`: multispecies occupation, charge vectors, density operators and joint budget carrier.
- `Bosonize.A10`: `swGeneratorMatrix`, `nonResonant`, `sw_generator_commutator_eq`, `sw_generator_skew_hermitian`, `lowShellProj`, `highShellProj`, `shell_proj_partition`, `shell_proj_orthogonal`, `shell_proj_self_adjoint`, `sw_compressed_bch_second_order`, `swEffectiveSecondOrder`, `energy_shell_discards_double_mode_one`, and 2×2/3×3 counterexamples.
- `Bosonize.Ch20`: finite-CAR order parameters, their residual operators, charge-target maps, finite witnesses, and a distinct *mode-family* algebraic duality. Do not mistake these declarations for a proved identification of all formal vertex series with finite-CAR observables.

**Interpretation:** Reuse these real declarations; avoid creating a parallel `RG.Fock`, another CAR layer, or another SW-matrix solver absent a documented and proved necessity. The `A10` companion's historical header contains older Phase-B/Phase-C statements: current module placement and recent phase records take priority over outdated sentences in retained historical notebooks.

## 2. Mathematical audit of the RG proposal

### Finding F1 — Two distinct cutoffs must remain distinct (D; high priority)

For oscillator multiplicities `n_m`, the total excitation grade is `E(n)=Σ_m m n_m`:

\[
\mathcal B_K=\operatorname{span}\{|n\rangle:E(n)\le K\}.
\]

At `K=2` with modes 1 and 2, removing the top energy shell keeps `span{1,X₁}`, while removing mode 2 within the same budget keeps `span{1,X₁,X₁²}`. This counterexample is already represented in Appendix G and the certified repeated-mode-one witness of A10. An energy cutoff is a **simplex**, not an occupation-box or tensor-factor cutoff.

**Decision:** Keep one finite Hilbert carrier and provide **independent retention predicates**: energy grade `E≤K'` and all selected high-mode occupations zero. Both give orthogonal coordinate projectors; neither projector is automatically a Wilsonian channel with Gaussian averaging.

### Finding F2 — Ambient projector identities must be restricted before applying SW (R + D; blocking)

A10 proves, on ambient multispecies Fock space,

\[
P_{K-1}+Q_K=\Pi_K.
\]

Its generic SW compressed-BCH theorem assumes **`P+Q=I`** on the entire carrier. On the ambient full Fock space, `Π_K≠I` in general. The A10 companion explicitly marks this transfer as unproved.

**Mandatory bridge:** Construct the finite retained source `\mathcal B_K` with the inherited inner product, transport ambient projectors/endomorphisms via its inclusion and coordinate inverse, and prove `P|_{\mathcal B_K}+Q|_{\mathcal B_K}=I_{\mathcal B_K}`. Alternatively formulate the generator/BCH theorem with a *third complement* and prove it contributes no term under stated hypotheses. Do not substitute the ambient shell operators directly into an identity requiring `P+Q=1`.

### Finding F3 — The shell denominator and the SW denominator are not interchangeable (D; blocking)

For a grading Hamiltonian `H₀|λ⟩=e(λ)|λ⟩`, restricted to exact shell `E`, the **Feshbach resolvent** is

\[
(z-H_{0,Q})^{-1}=\frac{1}{z-E}\,I_Q,\qquad z\ne E.
\]

But the **energy-independent SW** second-order matrix element is

\[
\langle\lambda|W^{(2)}|\lambda'\rangle
=\frac12\sum_{\mu\in Q}V_{\lambda\mu}V_{\mu\lambda'}
\left[\frac{1}{e(\lambda)-e(\mu)}+\frac{1}{e(\lambda')-e(\mu)}\right].
\]

A single `E₀` inserted into both denominators reproduces this only on an appropriate degenerate retained eigenspace, or under further assumptions. Define *two* mathematical operations: `feshbach(z)` (energy-dependent) and `swSecondOrder` (energy-independent polynomial), with a separately proved comparison when applicable.

For integer grade gaps and `E(λ)≤K'<E(μ)`, the coupled energy difference is at least one, so division is nonzero without a global `E₀` hypothesis. In a general interacting Bogoliubov baseline, the integer grading condition and block invariance require proof rather than inheritance from bare partitions.

### Finding F4 — A charge-sector-only shell loses Umklapp transitions (M + D; blocking)

The finite-CAR Umklapp operator changes individual species charge labels while preserving total electric charge. The supplied manuscript's CH21 selection rule states

\[
O_U\mathcal H_{\vec N}\subseteq\mathcal H_{\vec N+\Delta\vec N},
\]

and same-sector first-order compression vanishes. To obtain a second-order return to the initial charge sector, the intermediate `Q` must include reachable **different** species-charge sectors. If both retained and discarded subspaces are constructed in one fixed `\vec N` sector, `QVP` can vanish for a reason unrelated to the energy shell.

**Decision:** Use a charge-box or symmetry-sector carrier large enough to include `\vec N±\Delta\vec N`, define an explicit reachability predicate, and prove any omitted sectors have zero contributing matrix elements *before* specializing. Distinguish total-number/singlet conservation from per-species charge conservation.

### Finding F5 — The outer energy buffer matters (D; high priority)

A proposed reduction `\mathcal B_K→\mathcal B_{K'}` computes virtual excursions only through `\mathcal B_K\ominus\mathcal B_{K'}`. A finite-CAR perturbation might also leave `\mathcal B_K` entirely. Without invariance or an excursion bound, the expression misses these states. CH07 already has word-excursion/margin technology; reuse it to certify that the operator words relevant at second order are supported inside a chosen computational **buffer budget** `K_max`. Otherwise define and retain an outer-complement remainder.

This is not only a numerical concern: `P V (I-P) V P` need not equal `P V Q_shell V P` if `(I-Π_K)VP≠0`.

### Finding F6 — Compression is not an algebra homomorphism (M + D; high priority)

For any projection `P`,

\[
PABP=(PAP)(PBP)+PA(I-P)BP.
\]

Consequently `A↦PAP` is generally a `LinearMap` on operator spaces, **not** an `AlgHom`, `AlgEquiv` or `StarAlgEquiv`. The finite compression remainder must appear explicitly in product/OPE theorems. In contrast, true unitary conjugation on a fixed space may induce a star-algebra equivalence. Avoid conflating these categories in Lean type design.

### Finding F7 — Nilpotent exponential/BCH scope in the manuscript needs an explicit audit (M + D; high priority)

CH08 correctly distinguishes ambient CCR and finite-dimensional compressed operators, and the Lean module includes `finite_ccr_obstruction`. But any prose reading that combines **exact nonzero scalar CCR globally on one finite space** with nilpotent creation/annihilation exponentials on that *same* finite space is impossible:

\[
\operatorname{tr}[A,C]=0\ne m\dim W=\operatorname{tr}(mI_W)\quad(m>0,\ W\ne0).
\]

Formal coefficientwise exponentials and nilpotent exponentials of an individual raising/lowering map are legitimate on their specified carriers. They do **not** justify importing the ambient Weyl/BCH multiplier unchanged after budget compression. This is an audit of manuscript scope, **not a claim that the existing Ch08 Lean proofs are wrong**. Check CH08 §8.5, Appendix B §B.2, CH14, CH19–20, and the existing companion explanations against the exact compiled statements.

### Finding F8 — An exact discrete difference expansion is not yet an operator OPE (D; high priority)

On `Λ=ZMod L`, for `Tφ(x)=φ(x+1)` and `Δ=T−I`,

\[
T^r=(I+\Delta)^r,\qquad
\phi(x+r)=\sum_{j=0}^{r}{r\choose j}\Delta^j\phi(x)
\]

for natural displacement `r`. At one step, `φ(x+1)−φ(x)=Δφ(x)` is exact. For uncompressed normal-ordered vertices and a **central mixed contraction** `C(x,y)`, one obtains formally

\[
:e^{i\alpha\phi(x)}::e^{-i\alpha\phi(y)}:
=e^{\alpha^2 C(x,y)}:e^{i\alpha[\phi(x)-\phi(y)]}:.
\]

For `y=x+1`, the bracketed series contains **identity, a linear gradient, a quadratic normal-ordered difference, and higher powers**. The linear term does not vanish without a specified symmetrization/charge-conjugation assumption; zero modes, Klein factors and ordering phases may matter. Also, `:(Δφ)^2:` is not *identically* the finite Sugawara Hamiltonian: CH16 isolates a nonzero dispersion-error operator.

**Recommended decomposition:** First prove an ambient/formal Wick identity; separately prove a finite Taylor coefficient decomposition; finally project to the budget with an explicit leakage remainder. Distinguish a coefficientwise formal remainder from an operator-norm bounded analytic remainder.

### Finding F9 — RG coupling extraction is scheme dependent (D + P; high priority)

Even at order `g²`, the finite SW correction usually generates an identity term, quadratic currents, higher vertex harmonics and finite-distance/nonlocal contributions. Exact equality to one Sugawara operator is not automatic. Introduce a finite-dimensional **operator-space** projection onto a specified basis of retained observables, and define couplings by those coefficients. This yields an exact decomposition

\[
W^{(2)}=\mathcal P_{\mathrm{relevant}}W^{(2)}
+(I-\mathcal P_{\mathrm{relevant}})W^{(2)},
\]

but the smallness or RG-irrelevance of the second term is an additional theorem. The projection convention, inner product (e.g. Hilbert–Schmidt), symmetry restrictions, normalization and possible linear dependence of candidate observables must be specified. An exact finite-step coupling shift is **not automatically** the continuum Kosterlitz–Thouless beta function: its derivation requires a logarithmic scale identification, Gaussian shell contraction and rescaling, and uniform bounds in an explicit limit.

### Finding F10 — Manuscript prose is more ambitious than current certified Lean scope (R + M; high priority)

The supplied PDF contains continuum-style statements about Umklapp bosonization, KT relevance and gap formation in CH21 §§21.3–21.4, and Appendix G correctly demotes some such statements to heuristics. Treat these as **potentially conflicting scope declarations** until a theorem-to-source reconciliation is complete. Finite charge-sector leakage establishes non-invariance of a chosen truncation, not a thermodynamic Mott gap or an exact CAR–vertex identity. CH20 formal correlators and the finite-CAR equal-point example also explicitly use different normalizations/carriers.

## 3. Recommended architecture and mathematical interfaces (P)

### 3.1 One decimation engine, separate retention predicates

Let `H` be a finite-dimensional complex inner-product space with a fixed orthonormal basis `|i⟩`, integer grade `e(i)` and, when needed, charge vector `N(i)`. Introduce:

1. A **graded carrier** with a basis, grade and energy-diagonal reference Hamiltonian.
2. A **retention predicate** on basis labels (`e≤K'`, `no fast-mode occupancy`, specified charge box, or logical combination).
3. A **coordinate orthogonal projector**, range submodule, and canonical inclusion/coordinate maps.
4. A **decimation datum** on the restricted carrier with complementary self-adjoint projectors and a baseline commuting with the low projector.
5. A **generic non-resonant SW/Sylvester solver** plus a separate energy-dependent Feshbach resolvent.
6. An **observable-coefficient extraction** stage, explicitly separate from state-space compression.

The most economical first mode-decimation implementation uses `Ch08.BudgetIndex M K` and occupation predicates rather than building a second tensor-product Fock theory. Explicit tensor decomposition is a later theorem/alternative representation; the equality of full algebraic polynomial tensor factors does **not** imply the total-energy finite slice factors as a simple tensor product.

### 3.2 Carrier and charge choices

- **First proof prototype:** `Ch08.FiniteFock M K`, because it exposes weighted monomial labels and finite orthonormal coordinates without finite-band fermionic margins. Prove energy-shell vs. mode-retention inequivalence at `M≥2,K=2`.
- **Second bridge:** `A05.FockSpace σ h` with `A05.jointBudget h Ns K` and `A10` shells. Transport the generic theorem to this actual subspace and prove no dropped outer transitions under explicit margins.
- **Umklapp application:** choose a **charge-box** (not fixed vector `Ns`) and prove that reachable target sectors are included before forming second-order loops. This can be part of CH21 if its independently reviewed scope agrees.
- **OPE prototype:** uncompressed polynomial oscillator algebra or explicitly formal power-series coefficients; use finite truncation/budget only after the exact normal-ordered product is established.

### 3.3 Specific theorem deliverables

**T0 — Carrier/projector foundations**

- `range(P_K)` is the intended finite-dimensional budget; shell intersection is zero; `P_K'+Q_[K'+1,K]=P_K` on ambient space.
- A restricted-space identity `P'+Q'=I_{B_K}` with idempotence, adjoints and transported inclusion maps.
- Strict inclusion criterion: `B_K' < B_K` *iff* at least one admissible basis ket lies at energy `K'<E≤K` (not unconditionally).
- Natural mode-retention projector and a **verified different-range witness** at `M=2,K=2`.

**T1 — Resolvent/SW**

- Restricted baseline self-adjointness and `P H₀ = H₀ P`.
- Integer-gap lemma for all coupled `i∈P,j∈Q` and the nonzero complex-cast denominators.
- Explicit spectral **Feshbach** resolvent (finite sum of shell projectors) with inverse proof on the discarded subspace.
- **Separate** SW generator solution, skew-adjointness, and exact order-two compressed BCH polynomial; transport/reuse A10 instead of copy-pasting it.
- Optional analytic remainder estimate: requires normed operator structure; declare clearly unproved until implemented and checked.

**T2 — Formal OPE**

- Exact lattice shift/difference binomial theorem for operator-valued site functions.
- Ambient normal-ordering product with central-contraction hypotheses and explicit charge/Klein factors when relevant.
- Coefficientwise identity through quadratic order plus the defined remainder. For nearest-neighbor separation identify the linear and quadratic terms without dropping either.
- Compression remainder separately; derive a finite, nonvacuous estimate only if an appropriate operator norm and excitation buffer are available.

**T3 — Finite operator content / coupling extraction**

- Symmetry-adapted linearly independent finite operator family, with well-defined extraction coefficients.
- Exact `W²=Σ_i δg_i O_i+R` by definition of the operator-space projection, plus proven symmetry constraints.
- Counterexample or theorem to determine whether the retained quadratic family is closed; if not, retain the remainder explicitly.
- Scaling-limit problem formulated as a **separate conjectural research target** with regulator, time/scale variable, rescaling and uniform estimates.

### 3.4 Why not the other approaches?

| Approach | Specific obstruction or cost | Decision |
| --- | --- | --- |
| Replace `B_K` by an unrestricted tensor product of oscillator factors | Infinite-dimensional mode factors; independent occupation boxes differ from existing simplex budget and its Haldane dictionary. | Do not replace the carrier. Use occupancy predicates first; add a tensor-factor equivalence only if a Wilsonian trace construction needs it. |
| Treat the top many-body energy slice as a high-momentum Gaussian shell | Removes repeated low modes; high-shell projector is not a mode-factor conditional expectation. | Valid Feshbach decimation, **not** automatically Wilsonian mode RG. |
| Evaluate one scalar resolvent at fixed `E₀` to define the general SW Hamiltonian | Misses state-dependent/symmetrized denominators on nondegenerate low sectors. | Separate Feshbach and SW; compare conditionally. |
| Directly exponentiate finite compressed fields and invoke scalar BCH/Wick | Finite CCR trace obstruction; intermediate leakage invalidates naive product identities. | Work ambient/formally first; project with explicit residuals. |
| Assert quadratic/Sugawara closure from the second-order correction | Higher harmonics, identity, nonlocal and higher-order operators generally appear. | Define an observable extraction scheme with remainder and counterexamples. |
| Formalize continuum KT beta functions as an exact finite theorem at fixed `L,K` | No infinitesimal scale or prescribed rescaling; finite step is scheme dependent. | Defer to explicit scaling-limit/controlled approximation phase. |

## 4. Lean 4 **pseudocode** and contract sketches

**All blocks in this section are deliberately schematic, not compilation-ready Lean.** They express object/morphism boundaries, proof obligations and reuse points. The planning agent must inspect the actual Lean toolchain, `#check` the needed declarations and present a reviewed Phase-A interface *before* generating executable code. In particular, `?proof` and `?construction` below denote unresolved design/proof tasks, not accepted placeholders.

### 4.1 Generic retention and decomposition

```lean
-- SCHEMATIC: names and binders are not validated Mathlib APIs.
structure GradedBasisData (H : Type*) where
  Index        : Type
  finiteIndex  : Fintype Index
  ket          : Index → H
  orthonormal  : IsOrthonormalBasis ket
  grade        : Index → ℕ

structure OrthogonalDecimation (H : Type*) where
  keep       : H →ₗ[ℂ] H
  discard    : H →ₗ[ℂ] H
  keep_sq    : keep * keep = keep
  discard_sq : discard * discard = discard
  keep_adj   : adjoint keep = keep
  discard_adj: adjoint discard = discard
  cross_zero : keep * discard = 0
  sum_id     : keep + discard = 1

-- On the ambient physical Fock space, the last field is instead
-- keep + discard = budgetProjection.
-- CONSTRUCTION OBLIGATION: transport the operators to range(budgetProjection)
-- and only then instantiate sum_id.
```

**Lean design caution:** Specify the actual `LinearMap`, `Module.End` or `ContinuousLinearMap` types and their existing adjoint instances in the repository; do not assume a generic `IsOrthonormalBasis` name exists. `StarAlgEquiv` is appropriate for an actual *-preserving equivalence, not for `A↦PAP`.

### 4.2 Mode selection using **existing** Ch08 indices

```lean
-- SCHEMATIC, using observed Ch08 names as anchors.
def fastModeVacuumOnBudget (M K : ℕ) (mCut : ℕ)
    (s : Ch08.BudgetIndex M K) : Prop :=
  ∀ m : Ch08.Mode M,
    mCut < Ch08.weight M m →
      Ch08.indexExponent M K s m = 0

-- Proposed: basis-coordinate orthogonal projection onto the predicate.
noncomputable def keepSlowModes (M K mCut : ℕ) :
    Module.End ℂ (Ch08.FiniteFock M K) :=
  ?construction

-- Prove: self-adjoint / idempotent / exact range / monotonicity in mCut.
-- Witness: M ≥ 2, K=2, mCut=1;
-- mode-vacuum predicate keeps |n₁=2,n₂=0⟩, energy ≤1 does not.
```

Do **not** confuse mode labels (`Fin M`, typically weight `m.val+1`) with the physical momentum band `ZMod L` or the many-body grade `K`. Keep separate parameters `L`, `M`, `K`, `mCut` throughout.

### 4.3 Restricted shell transfer and SW

```lean
-- SCHEMATIC proof structure, not an API promise.
def budgetCarrier (h K : ℕ) (Ns : σ → ℤ) :=
  A05.jointBudget h Ns K  -- identify actual Submodule carrier/instances

-- REUSE:
-- A10.lowShellProj h Ns K
-- A10.highShellProj h Ns K
-- A10.shell_proj_partition h K hK Ns:
--   lowShellProj + highShellProj = Ch14.projection h Ns K

-- Proposed adapter, on a *restricted* budget carrier:
def restrictedKeep : Module.End ℂ (budgetCarrier h K Ns) :=
  ?transport_of_A10_lowShellProj

def restrictedDiscard : Module.End ℂ (budgetCarrier h K Ns) :=
  ?transport_of_A10_highShellProj

theorem restricted_partition :
  restrictedKeep + restrictedDiscard = 1 :=
  ?proof_from_shell_proj_partition_and_range

-- Only after this gate, instantiate or re-use
-- A10.sw_compressed_bch_second_order.
```

This adapter is the first blocking theorem. A full generic API should accept any `P,Q` satisfying its hypotheses; one adapter can instantiate it on the A10 partition, another on the mode-selective Ch08 partition.

### 4.4 Spectral inverse without partial/unsafe division

```lean
-- SCHEMATIC. Distinguish two cases:
-- (A) Feshbach resolvent at a scalar spectral parameter z;
-- (B) energy-independent, index-pair SW denominators.

structure EnergySeparation (low high : Finset ι)
    (energy : ι → ℕ) where
  ordered : ∀ i ∈ low, ∀ j ∈ high, energy i < energy j

-- For i∈low, j∈high prove:
--   0 < energy j - energy i
-- and cast nonzero into ℂ before field division.

-- Generic exact-shell resolvent:
-- (z I - H₀,Q)⁻¹ = Σ_{E∈shell} (z-E)⁻¹ Q_E
-- with ∀E∈shell, z≠E.

-- General SW:
-- S₁(i,j) = V(i,j)/(E_i-E_j) for coupled cross-block pairs;
-- S₁(i,j) = 0 otherwise.
-- Reuse A10.swGeneratorMatrix / nonResonant / matrix proofs.
-- Do not substitute z=E₀ for all low basis energies without a theorem.
```

### 4.5 Formal OPE and extraction

```lean
-- SCHEMATIC mathematical requirements.
-- Ambient site translation T and difference Δ := T - id.
theorem finite_newton_shift (r : ℕ) :
  T^r = ∑ j ∈ Finset.range (r+1), (Nat.choose r j) • Δ^j :=
  ?proof_noncommuting_issue_absent_because_T_eq_one_plus_Δ

-- At an uncompressed formal-series level:
-- :exp(iαφ(x))::exp(-iαφ(y)):
-- = contraction(x,y) * :exp(iα(φ(x)-φ(y))):
-- (under an explicit central mixed-commutator hypothesis).

-- Define coefficients O₀,O₁,O₂ and formal R_{≥3}, not an
-- analytic bound. Then separately prove the compressed product relation:
-- P A B P = (P A P)(P B P) + P A (1-P) B P.

structure OperatorExtraction (H : Type*) where
  retained : Submodule ℂ (Module.End ℂ H)
  coeff    : Module.End ℂ H →ₗ[ℂ] CouplingVector
  synth    : CouplingVector →ₗ[ℂ] Module.End ℂ H
  -- prove synth ∘ coeff acts as the intended operator-space projection
  -- define remainder := W2 - synth (coeff W2)
```

For norm estimates, introduce a finite-dimensional normed carrier and an appropriate bounded operator map only **after** the purely algebraic coefficient theorems are complete. The need for `ContinuousLinearMap`, explicit matrix norms, or a `Cstar` structure must be demonstrated by a concrete target bound, not added preemptively.

## 5. Proposed next steps, dependencies and acceptance gates

The project already uses **Phase A (specify/review/lock), Phase B (prove), Phase C (audit/promote/freeze)**. The RG package should follow exactly those rules, but only after an explicit architecture decision. No frozen Core edits are authorized by this document.

| Priority / phase | Deliverable | Dependencies | Exit gate / counterexample |
| --- | --- | --- | --- |
| **P0 — Baseline reconciliation** | Source inventory linking PDF pp. 42–55, 103–108, 145–155, 180–194, 222–228 to tracked notes, actual Lean declarations and validation receipts; explain uploaded PDF vs tracked master mismatch. | GitHub `main`, local book provenance if available. | Every reviewed claim has `M/R/D/P` classification; no historical notebook text used to overrule a current module. |
| **P0 — Resolve mathematical decisions** | Five ADRs: physical carrier; primary decimation; H₀ and resolvent type; vertex normal-ordering; coupling extraction/scale. | This review, CH20b/CH21 scope. | Explicit human-approved decision before Phase A signatures. |
| **P1 — Restricted projector adapter** | Prove the `P+Q=I` **on budget carrier** bridge for A10 and identify outer-excursion hypotheses. | A10, A03, Ch07, Ch14, A05. | Non-vacuous `K=2` example; fresh compiler/axiom audit; old Core unchanged. |
| **P1 — Mode-selective projector** | Retention predicate and coordinate projector on `Ch08.FiniteFock`; contrast with energy shell. | Ch08 weighted indices; projector adapter. | `M=2,K=2` explicit different-range witness; idempotence/adjoint; no full tensorization required. |
| **P1 — Non-resonant resolvent** | Exact inverse on shell(s), integer nonresonance and SW/Feshbach separation. | Restricted partition, diagonal H₀ theorem. | Correct low-state denominators, defined behavior at degeneracy, 2×2 and 3×3 regression checks. |
| **P2 — Charge-aware virtual channels** | Reachable charge boxes, operator support and second-order paths for Umklapp. | CH21 charge selection and leakage, A05. | Demonstrate a nonzero allowed `P V Q V P` matrix element or explain obstruction; include sectors beyond fixed `Ns`. |
| **P2 — Formal discrete OPE** | Newton differences + central-contraction vertex product + coefficients to quadratic order + explicit formal remainder. | Ch02, Ch08, Ch15–16, A08/CH19/CH20b. | Preserve linear term, Klein phases and ordering; separate ambient from compressed identity. |
| **P3 — Coupling identification** | Finite symmetry-adapted observable projection and `δg` definition; exact decomposition and nonzero remainder examples. | SW + OPE. | Prove coefficient unambiguity under basis-independent hypotheses, or record scheme dependence. |
| **P4 — Controlled RG/KT research** | Operator-norm estimates and a finite-size/scale limit **candidate**. | Quantitative bounds, rescaling map, operator closure analysis. | No beta-function theorem proposed until scale, normalized parameters and convergence topology are fixed. |

**Scheduling constraint:** P0/P1 specification can proceed independently as **read-only research/design** while the roadmap's CH20b/CH21 work is active, but do not run concurrent authors against common Lean files. A novel theorem package needs its own approved scope and lock before implementation. Preserve the repository's existing external-worker policy: Antigravity is authorized here **only as a planning consultant**, not as an implicit executable author/reviewer, automatic backend or budget fallback.

### Minimal verification protocol for every accepted implementation slice

1. Pin base commit SHA and exact affected file hashes. Never replace frozen `Bosonize/Core/*` sources without the formal issue/review procedure.
2. Independently review mathematical carriers, source/target types, operator order, signs, charge-sector support, margins, non-vacuity and the claimed theorem strength.
3. Verify actual Mathlib and local Core APIs using the pinned compiler. A plausible declaration name in this packet is not a verified API.
4. Compile Phase A interfaces, lock signatures, and allow only the established workflow's temporary unproved staging stubs; do not report placeholder compilation as theorem completion.
5. In Phase B: build targets, check locks, audit axioms, prove actual witnesses and preserve error/remainder terms. Reject `True`, vacuous hypotheses, fake green tests and proof assumptions smuggled through helper definitions.
6. In Phase C: independently review proofs, check standard-axiom dependencies, no `sorry/admit`, warning-as-error, source hash invariance and upstream Core preservation; run the project's `make ci` and record a fresh receipt. Separately align the corresponding Markdown/LaTeX statements.
7. For physical RG claims: demand an explicit scheme and quantify all errors; no numerical observation or formal coefficient identity may be promoted into a continuum scaling theorem without further work.

## 6. Ready-to-send Google Antigravity **planning prompt**

Copy this prompt into Antigravity, attaching this Markdown file and giving it read-only access to the *current* repository (or a versioned snapshot). No Lean code generation is authorized by this initial request. Its first job is a validated design package, not a branch merge.

> **ROLE:** Act as an independent Principal Mathematical Physicist, Lean 4/Mathlib architect and adversarial research-planning reviewer for `lufreitas0000/bosonize-lean`.
>
> **SCOPE:** Planning/review only. Do **not** edit or create Lean, Markdown, LaTeX, lock or workflow files; do not run automatic author/reviewer subagents; do not open PRs, push, merge or consume another provider's credits. If you can run read-only local compiler queries, report them as diagnostic checks, not proof acceptance. Ask for approval of mathematical architecture and phase scope **before** any implementation task.
>
> **STARTING MATERIAL:** This attached review; the uploaded 239-page `main(2).pdf` if accessible; current GitHub default branch, observed planning SHA `0d185dfbadd6b8efe1eba752d2520873b35cdc0a`. Revalidate HEAD on starting. Consult `README.md`, `adaptative_roadmap.md`, `.agents/skills/formalizer/SKILL.md`, `docs/BOOK_AND_SOURCE_COVERAGE_PLAN.md`, `note/ch19_phase_c_validation_2026-10-16.md`, `note/ch20_phase_c_validation_2026-10-16.md`, `docs/webllm/chapters/ch19.json`, `ch20.json`, `notes/md/ch07_vacuum_budget_space.md`, `notes/md/ch08_boson.md`, `notes/md/ch16_field_Hamiltonian.md`, `notes/md/ch20_CDW.md`, `notes/md/ch21_spinful_models.md`, `notes/appendices/a10_discrete_rg_and_schrieffer_wolff.md`, and actual Lean modules `Ch07VacuumBudget`, `Ch08Boson`, `A03EnergyBudgets`, `A05MultiSpecies`, `Ch14Mandelstam`, `A10DiscreteSchriefferWolff`, `Ch16FieldHamiltonian`, `Ch19Correlations`, `Ch20CDW`. Resolve exact paths from repository content; do not assume earlier checkpoint paths exist.
>
> **MANDATORY AUDIT:** (1) Inventory what is *actually compiled and frozen*, what is historical or pending, and what is only in the newer PDF. (2) Verify the unproved `P+Q=I` restricted-carrier bridge. (3) Compare energy shells and high-mode occupation shells, including the `M=2,K=2` counterexample. (4) Distinguish Feshbach resolvents from state-dependent/symmetrized SW denominators. (5) Include charge-sector-changing Umklapp intermediate states and external budget excursions. (6) Preserve compression leakage in every product identity. (7) Investigate finite CCR and nilpotent exponential scope; do not infer a global scalar CCR in finite dimension. (8) Separate ambient normal-ordered formal OPE from its compressed counterpart. (9) Define the extraction scheme and conditions for calling a finite coupling shift an RG flow. (10) Identify contradictions between the manuscript's continuum claims and the formally certified scope.
>
> **DESIGN CONSTRAINTS:** Favor pure `LinearMap`/submodule/isometric equivalence morphisms and existing coordinate projectors. Treat compression as **not an algebra homomorphism**. Retain `Branch` vs lattice-length `L`, mode cutoff `M`, total budget `K`, slow-mode threshold `mCut`, charge-box labels, zero-mode/Klein factors and exact operator-product order. Keep all unknown Mathlib APIs explicitly unresolved until inspected in the actual installed version. Do not recreate frozen infrastructure.
>
> **REQUESTED OUTPUTS (planning artifacts in one response, or separate Markdown deliverables only if explicitly authorized):**
>
> 1. `STATUS_AND_PROVENANCE`: a traceable baseline with commit SHA, source paths, claims, current verification level and missing evidence, including the discrepancy between the PDF and tracked LaTeX master.
> 2. `CRITICAL_FINDINGS`: ranked mathematical/type-theoretic issues; for each include a counterexample or proof obligation, the affected theorem, and the minimum corrective change.
> 3. `ARCHITECTURE_DECISIONS`: compare (A) total-energy projection, (B) high-mode occupation projection on existing `Ch08.FiniteFock`, (C) independent tensor-cutoff carrier; justify one recommended core abstraction and clearly distinguish mode integration from Feshbach projection.
> 4. `LEAN_API_MAP`: exact existing declarations and expected signatures, with file/line evidence; unresolved names marked as proposals. Prefer reusing `A10` rather than implementing SW again.
> 5. `DEPENDENCY_DAG`: no cyclic dependencies; named theorem packages T0–T3, carrier requirements, source/target types, margins, non-vacuity witnesses and blockers. Include the P+Q restricted carrier theorem as an explicit prerequisite.
> 6. `PHASE_A_PLAN`: independently checkable theorem contracts and companion documentation, with precise assumptions, plus one adverse example for each conceptual distinction. **Pseudocode is acceptable; executable Lean and modifications are not.**
> 7. `PHASE_B_C_VERIFICATION`: proposed compiler/guard/axiom checks, independent review division, hashes, frozen-Core preservation and evidence receipts, following existing project policies.
> 8. `NEXT_RESEARCH`: controlled OPE remainder, charge-aware Umklapp shell loops, Wilsonian Gaussian shell comparison, operator extraction, scale/rescaling and possible KT limit; mark all unproved claims explicitly.
> 9. `DECISION_REQUESTS`: at most five mathematically consequential questions to ask the user before Phase A is locked. Present a defensible default for each, without assuming approval.
>
> **FAIL CONDITIONS:** Treat `sorry`, `admit`, `True` placeholders, an unchanged interface with weaker hidden definitions, a theorem with vacuous assumptions, shell projection without correct carrier, lost charge sectors, silently discarded high-energy excursions, fabricated Mathlib APIs, unverified bibliography, conflated formal/analytic exponentials, and exact finite-step KT claims without an RG scheme as review failures. Distinguish a historical validation note from a fresh local build.
>
> **FINAL RESPONSE FORMAT:** A concise executive verdict followed by evidence table, findings, architecture decision record, theorem dependency DAG, bounded tasks with acceptance gates, open research questions, and the five human decisions. Stop after the planning deliverables. Request explicit authorization before any source changes or model-worker dispatch.

## 7. Human architectural decisions to settle before Phase A

These questions are not superficial preferences; they determine whether the proposed theorem is true and what Lean carrier to use.

1. **Initial physical model:** First build mode-selective decimation on `Ch08.FiniteFock` and then transport to finite CAR, or target the multispecies finite-CAR charge-box from the outset? **Default:** oscillator proof prototype then finite-CAR bridge, with no equality of their observables asserted without an intertwiner.
2. **Primary RG operation:** Is the scientific goal a controlled finite **Feshbach/SW spectral elimination**, or specifically **Wilsonian high-mode Gaussian integration**? **Default:** expose both as separate operations; use coordinate mode-selective projection as an intermediate construction, and do not claim their equality.
3. **Reference Hamiltonian:** Bare integer grading, free Sugawara, or Bogoliubov-diagonal interacting quadratic Hamiltonian? **Default:** prove the generic graded theorem using bare integer grading; later require explicit spectral-block invariance for interacting H₀.
4. **Vertex notion:** Formal coefficientwise normal-ordered oscillator vertex, finite compressed Taylor approximation, or actual finite-CAR local bilinear/quartic word? **Default:** formal oscillator OPE first, exact finite-CAR comparison later, retaining all normalization and compression residuals.
5. **Level of RG theorem:** Exact second-order coefficient decomposition at fixed cutoff, norm-controlled approximation, or KT flow limit? **Default:** the first two are staged targets; a continuum beta-function theorem is a new research program and requires explicit scaling hypotheses.

## 8. Source and bibliography verification

### Repository source anchors (observed at the specified commit)

- [Repository README](https://github.com/lufreitas0000/bosonize-lean/blob/0d185dfbadd6b8efe1eba752d2520873b35cdc0a/README.md)
- [Adaptive roadmap](https://github.com/lufreitas0000/bosonize-lean/blob/0d185dfbadd6b8efe1eba752d2520873b35cdc0a/adaptative_roadmap.md)
- [A10 Lean Core](https://github.com/lufreitas0000/bosonize-lean/blob/0d185dfbadd6b8efe1eba752d2520873b35cdc0a/Bosonize/Core/A10DiscreteSchriefferWolff.lean)
- [Ch08 finite oscillator Core](https://github.com/lufreitas0000/bosonize-lean/blob/0d185dfbadd6b8efe1eba752d2520873b35cdc0a/Bosonize/Core/Ch08Boson.lean)
- [CH20 frozen Core](https://github.com/lufreitas0000/bosonize-lean/blob/0d185dfbadd6b8efe1eba752d2520873b35cdc0a/Bosonize/Core/Ch20CDW.lean)
- [A10 companion](https://github.com/lufreitas0000/bosonize-lean/blob/0d185dfbadd6b8efe1eba752d2520873b35cdc0a/docs/companion/Bosonize/Core/A10DiscreteSchriefferWolff.md)
- [A10 source note](https://github.com/lufreitas0000/bosonize-lean/blob/0d185dfbadd6b8efe1eba752d2520873b35cdc0a/notes/appendices/a10_discrete_rg_and_schrieffer_wolff.md)
- [CH21 note](https://github.com/lufreitas0000/bosonize-lean/blob/0d185dfbadd6b8efe1eba752d2520873b35cdc0a/notes/md/ch21_spinful_models.md)
- [Tracked LaTeX master](https://github.com/lufreitas0000/bosonize-lean/blob/0d185dfbadd6b8efe1eba752d2520873b35cdc0a/notes/latex/main.tex)
- [Formalizer A–B–C skill](https://github.com/lufreitas0000/bosonize-lean/blob/0d185dfbadd6b8efe1eba752d2520873b35cdc0a/.agents/skills/formalizer/SKILL.md)

**Manuscript references:** user-provided PDF, printed Chapter 7 §§7.6–7.7; Chapter 8 §§8.4–8.5; Chapter 16 §§16.4–16.5; Chapter 20 §§20.2–20.3; Chapter 21 §§21.3–21.4; Appendix G §§G.2–G.5. PDF page indices differ from printed page numbering. No hash linkage to tracked GitHub LaTeX inputs was established.

### Primary academic references (metadata checked against publishers)

1. Sergey Bravyi, David P. DiVincenzo and Daniel Loss, “Schrieffer–Wolff transformation for quantum many-body systems,” *Annals of Physics* **326**, 2793–2826 (2011), [DOI: 10.1016/j.aop.2011.06.004](https://doi.org/10.1016/j.aop.2011.06.004). Relevant to the distinction between exact block rotations and perturbative effective Hamiltonians.
2. Jorge V. José, Leo P. Kadanoff, Scott Kirkpatrick and David R. Nelson, “Renormalization, vortices, and symmetry-breaking perturbations in the two-dimensional planar model,” *Physical Review B* **16**, 1217–1241 (1977), [DOI: 10.1103/PhysRevB.16.1217](https://doi.org/10.1103/PhysRevB.16.1217). The original paper has a [published erratum](https://doi.org/10.1103/PhysRevB.17.1477); consult it before importing any specific coefficient or sign.
3. Thierry Giamarchi, *Quantum Physics in One Dimension*, Oxford University Press (published online 2003; often catalogued as a 2004 volume), [DOI: 10.1093/acprof:oso/9780198525004.001.0001](https://doi.org/10.1093/acprof:oso/9780198525004.001.0001). Source for continuum bosonization/vertex/RG conventions, **not** evidence of an exact finite-lattice identity.

All other references found in repository transcripts or draft notes require independent identification/verification before citation in a formal theorem-to-literature ledger. ArXiv identifiers have deliberately not been supplied when unnecessary.

## 9. Acceptance decision for the first new phase

**Proposed approval request:** Authorize a **Phase-0/Phase-A design sprint** for `RGDecimation` (working title), comprising the restricted A10 shell bridge, Ch08 mode-selective projector, explicit non-resonance and one verified counterexample. The deliverable is a reviewed theorem-signature/companion specification, not an attempt to prove a KT flow.

**Stop conditions:** (i) The carrier and projection identity cannot be stated without altering frozen Core; (ii) the proposed H₀ fails block invariance; (iii) a charge-changing interaction is projected onto an isolated charge vector; (iv) operator-product leakage is dropped; (v) an OPE coefficient is mistaken for a genuine asymptotic estimate; or (vi) the scope conflicts with CH20b/CH21's active obligations. Escalate these as an architecture decision or narrowly scoped correctness issue, rather than weakening a theorem.

**Bottom line:** The important next theorem is not “one-step KT beta function.” It is the **correct, typed transfer of shell/projector algebra to the actual finite low-energy carrier, with all virtual channels represented**. Establish that foundation, then compare energy-decimation and high-mode-decimation maps on explicit finite examples. Only after this comparison should the project attempt a discrete OPE coefficient calculation and a finite coupling-extraction theorem.
