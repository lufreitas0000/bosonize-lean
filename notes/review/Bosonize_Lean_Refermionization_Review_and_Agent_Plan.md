# Bosonize-Lean: State-of-Project Review and Refermionization Research Plan

**Review date:** 2026-10-17  
**Primary source:** `main(5).pdf`, *Constructive 1+1D Lattice Bosonization: Finite Constructions and Algebraic Models* (239 PDF pages; dated 2026-10-17)  
**Intended readers:** mathematical-physics architect, Lean 4 / Mathlib4 proof auditor, and Google Antigravity planning agent  
**Mode:** research and architecture planning. All Lean-like snippets below are **non-compiling pseudocode**. Do not modify production Lean or LaTeX before a reviewed plan is approved.

## Executive recommendation

**Do not start by asserting a budget-level refermionization `StarAlgEquiv`.** Reuse the existing charge-sector, CAR, budget, current, and vertex layers, but first prove or explicitly delimit the maps joining them. The next research phase should be an *exact finite-system benchmark and obstruction-aware comparison*, followed by the special-point quadratic impurity model. Only then consider the thermodynamic TDOS law.

Key reasons:

1. A full finite-mode CAR representation has exact CAR, but its generic energy-budget compression does not.
2. The finite cyclic lattice current algebra differs globally from the anomalous infinite-sea chiral algebra; the monograph correctly obtains scalar current commutators **as ambient commutators evaluated on protected budget vectors**.
3. Chapter 14 explicitly leaves the unconditional finite Mattis–Mandelstam field–vertex identity unresolved and gives counterexamples to insufficient cutoff conditions.
4. Chapter 20.1 already formulates the three-carrier intermediate-projection residual needed for impurity backscattering.
5. The charge parity governing twisted Fourier boundary conditions differs from the parity of scattering insertions entering the `Z_e - Z_o` representation.
6. Exact finite-size TDOS is a discrete spectral measure; a smooth low-energy power law requires a further limiting argument.

**Evidence boundary:** This is an audit of the *uploaded monograph*, not of the checked-out Lean repository. Statements such as “promoted to Core” are claims in the notes until an agent inspects the actual pinned commit, declarations, tests, and kernel-checked dependencies. The PDF contains embedded paths and validation-record references, but does not supply those files or their current contents.

---

## 1. Documented baseline and verification ledger

The following statuses are those **reported by the monograph**, not independently certified here. Keep the distinctions between mathematical truth, manuscript proof, and Lean kernel proof.

| Layer | Sections in the monograph | Documented status | What the agent must audit |
|---|---|---|---|
| Finite lattice, centered momentum band, Nyquist convention | Chs. 1–3 | Exact finite kinematics described | Existing type and sign conventions, Fourier normalization, non-wrapping vs wrapped addition |
| Finite CAR Fock space, signs, charge sectors | Chs. 4–7 | Exact occupation-representation algebra described | Exact modes, CAR proof, adjoints, budget inclusions and projectors |
| Uncompressed oscillator/CCR and finite filtered carrier | Ch. 8 | Ambient CCR plus finite nilpotent components, **not** global finite CCR | Separate infinite polynomial carrier from finite budget; trace no-go |
| Finite density commutators | Chs. 9–10, esp. Thm. 10.6 | Ambient commutators act as Kac–Moody central terms on protected inputs, e.g. `2M + K + |N| ≤ h` | Ensure proof never treats compressed current endomorphisms as globally satisfying CCR |
| Haldane basis and multispecies Klein maps | Chs. 11, 13; Thm. 13.13 | Typed budget isometries under pair margins; ordered CAR cocycles | Exact source/target charges, inverse map, orientation, margin and non-vacuity |
| Finite vertex construction | Ch. 14; Appendix B | Nilpotent finite exponentials and a **conditional** cyclic field–vertex criterion | Unconditional equality **open**; reproduce `K=0` and missing-mode counterexamples |
| Quadratic pairing Bogoliubov transform | Ch. 18 | Ambient linear change of currents; diagonal Hamiltonian identity on budget inputs | `v1 > |v2|`, scalar correction, meaning of `g=(c-s)^2`, image may leave budget |
| Abstract states and correlations | Ch. 19; Appendix E | CH19/A08 Phase C **reported** complete in reviewed Core scope; no finite interacting ground-state equivalence | Check independent `note/ch19_phase_c_validation_2026-10-16.md` and declarations |
| Exact CDW/SC products and residuals | Ch. 20.1; esp. Thm. 20.4, 20.6 | Introduction **reports** promoted Core results, including a nonzero four-site residual | Locate exact modules and tests; reconcile later editorial wording |
| Formal vertices and algebraic duality | Chs. 20.2–20.3 | Explicitly presented as draft/awaiting independent verification; no finite-CAR equivalence | Do not treat formal series or duality substitutions as verified finite operators |
| Spinful and Umklapp development | Ch. 21 | Explicitly described as **not implemented** in Lean at manuscript date | Out of scope for initial spinless impurity phase; reusable parity ideas only |

**Internal documentation issue to resolve:** Ch. 20.1 says its promoted Core module verifies several finite-CAR results, while Ch. 20.2 says “as with Section 20.1” these derivations are mathematical drafts awaiting independent review. This may distinguish module certification from editorial approval, or may reflect an outdated paragraph. The agent must identify exact declarations/commit hashes and issue a source-status correction rather than selecting one statement without evidence.

**Referenced places in source:** printed pp. 65–68 (Ch. 10), 83–95 (Chs. 13–14), 117–133 (Chs. 18–19), 135–164 (Ch. 20), 165–194 (Ch. 21), 202–208 (Appendix B). Refer to numbered equations rather than assuming an extracted PDF's page offset.

### Priority audit of concrete existing claims

- **Thm. 10.6, Eqs. (10.12)–(10.16):** domain of central current commutator; compressed operators versus ambient compositions.
- **Thm. 13.13, Eq. (13.16):** surjective typed Klein isometry; source and target sector admissibility and cocycle phases.
- **Ch. 14, Eqs. (14.7), (14.11)–(14.17):** normal-ordered vertex candidate, projected commutator excursion, conditional cyclic comparison.
- **Remark 14.19:** `L=4,K_in=K_out=0` deep-hole obstruction and `L=12,M=1,K_out=2` missing-mode coefficient mismatch. These must become regression cases, not merely prose.
- **Ch. 18, Eqs. (18.5)–(18.18):** hyperbolic normalization and the distinction between action on a budget and invariant subspace diagonalization.
- **Ch. 19 closing verification boundary:** the Gaussian state is not proven to be the finite interacting ground state.
- **Thm. 20.4, Eqs. (20.19)–(20.23):** independent source/intermediate/target budgets and projection-excursion remainder.
- **Thm. 20.6, Eq. (20.24):** finite-charge unitary-lowering no-go.
- **Ch. 20.2.8 and 20.3.7:** formal series and duality are not finite-CAR operator equivalences.

---

## 2. Mathematical obstructions and required corrections

### 2.1 Charge-lattice coordinates and parity

Use original integer branch charges `n_R,n_L ∈ ℤ`. Avoid the ambiguous repeated symbol `N_+` for both an original branch charge and a derived relative charge. Define

\[
Q=n_R+n_L,\qquad r=n_R,\qquad n_L=Q-r,
\]

with

\[
2N_{\mathrm{rel}}=n_R-n_L=2r-Q,\qquad N_{\mathrm{tot}}=Q/2.
\]

The map `(n_R,n_L) ↔ (Q,r)` is an integral unimodular coordinate change. The alternative `(Q,d=n_R-n_L)` has image precisely `Q≡d (mod 2)`; it is **not** a surjective automorphism of `ℤ²`. Use `(Q,r)` as the stored index. Define `P := Q mod 2` once and recover half-integral physical charges in calculations only where necessary.

Original Klein lowering maps change one branch charge:

\[
F_R:(n_R,n_L)\mapsto(n_R-1,n_L),\quad
F_L:(n_R,n_L)\mapsto(n_R,n_L-1).
\]

Define the **composite lowering**

\[
K_{\mathrm{rel}}:=F_L^\dagger F_R:
(Q,r)\mapsto(Q,r-1).
\]

It lowers `N_rel` by one, preserves `Q`, and does not cross the total-charge parity class. Its adjoint raises `N_rel`. The backscattering monomial `c_R^† c_L` has the latter orientation; check all phases and operator order rather than assigning the same symbol `F_+` to both original and composite Klein factors.

A fixed-`Q` carrier is a direct sum of charge-graded fibers

\[
\mathcal H_Q=\bigoplus_r\mathcal H_{Q,r}.
\]

The finite physical lattice restricts both `r` and `Q-r` by `[-h,h]`, and the budget adds excitation constraints. The composite Klein morphism is **typed** between adjacent fibers. A global unitary lowering operator on a finite interval is impossible (Thm. 20.6); after compression use a partial shift and prove its endpoint defects. Do not assume all fibers have the same dimension outside Haldane-completeness margins.

**Model counterexample:** for a one-dimensional charge-fiber interval, a truncated lowering shift `K` has `K†K=I-P_bottom`, `KK†=I-P_top` and `{K,K†}=2I-P_bottom-P_top`. For actual Haldane fibers, replace endpoint symbols by exact initial/final projection defects and prove the formula on the chosen carrier. Note this `{K,K†}` is **not** the single-mode fermion CAR.

### 2.2 Antiperiodic Fourier sector is not `ZMod L → ℂ`

Refermionized Fourier boundary conditions depend on `P=Q mod 2`:

\[
\Psi_P(x+L)=(-1)^{1-P}\Psi_P(x),\quad
k_{n,P}=\frac{2\pi}{L}\left(n-\frac{1-P}{2}\right).
\]

`P=0` is antiperiodic, `P=1` periodic, using the reference's convention. The spatial lattice remains `ZMod L` for ordinary periodic observables, but a *twisted section* needs either an integer lift with quasi-periodicity or a gauge-trivialized carrier with a twisted translation operator satisfying

\[
T_P^L=(-1)^{1-P}I.
\]

Do **not** model an antiperiodic field as an ordinary function `ZMod L → ℂ` without its holonomy datum. Reuse Ch. 6 boundary-holonomy abstraction if it already provides this structure; avoid duplicate types.

### 2.3 The finite CAR-compression theorem

For full Fock annihilators `c_i`, orthogonal budget projection `P_B`, and compressed `a_i=P_B c_i P_B` (restricted to the range):

\[
\boxed{\{a_i,a_j^\dagger\}=\delta_{ij}I_B
-P_Bc_i(I-P_B)c_j^\dagger P_B
-P_Bc_j^\dagger(I-P_B)c_iP_B.}
\]

For `i=j`, the omitted terms are positive semidefinite. This is the canonical **exact finite-budget result**. A full set of `M` independent exact fermionic modes requires a representation of the corresponding CAR algebra; an arbitrary energy-budget dimension need not admit one. Do not state exact CAR for Fourier modes of a *compressed* vertex without the additional closure conditions that annihilate the defects.

Use protected-interior theorems for vectors on which the relevant excursions vanish. Do not promote the pointwise protected-domain statement to an endomorphism equality on the entire budget.

### 2.4 Current-algebra anomaly is not an identity of finite cyclic shifts

Ch. 10 derives the Schwinger term for **non-wrapping** partial momentum shifts via explicit lower/upper edge operators. In contrast, cyclic shift matrices commute, so their second quantizations commute globally. Also, any purported global finite-dimensional `[A,B]=m I` with `m≠0` contradicts the trace identity.

Therefore distinguish these objects throughout the new development:

1. `FiniteCAR`: full finite-band exact occupation operators.
2. `ProtectedCurrent`: ambient non-wrapping current operators evaluated on a protected budget domain.
3. `PolynomialCCR`: uncompressed bosonic oscillator/charge representation.
4. `CompressedVertex`: finite polynomial expression with explicit projection residuals.
5. `EffectiveResonantLevel`: independently defined finite quadratic impurity model.

Any claimed isomorphism must name two of these carriers and actually prove the applicable morphism or partial intertwiner.

### 2.5 The special hyperbolic point

Ch. 18 fixes

\[
c^2-s^2=1,\qquad g=(c-s)^2,\qquad v_1>|v_2|.
\]

At `g=1/2` on the chosen positive branch:

\[
c=3\sqrt2/4,\qquad s=\sqrt2/4,
\quad c-s=1/\sqrt2,\quad c+s=\sqrt2.
\]

The corresponding coefficient ratio is `v_2/v_1=3/5` for the **Chapter 18 pairing-current convention**; it is not a universal relation for every microscopic `g_2,g_4` parametrization. Implement as a specialization of the existing generic `HyperbolicPair`, not a second transformation API. Work over `ℝ` for positivity and extend scalars to `ℂ` when complex phase operators are required; `ℚ(√2)` is optional, not a foundation-level dependency.

At the free-fermion normalization `exp(i sqrt(2g) Φ_rel)`, the vertex coefficient is `sqrt(2g)=1`. However, verify that the impurity field `Φ_rel` uses the identical chiral/zero-mode normalization as the reference before equating vertices. This is not a consequence of the hyperbolic pair alone.

### 2.6 Nilpotent exponentials are not the exponential of the whole field

Ch. 14 constructs triangular `W_±` and finite `expNil` factors. If `W_+` increases the grading and `W_-` decreases it, their compressions are separately nilpotent with degree bounded by the cutoff. Scalar rescaling preserves nilpotency. But `W_++W_-` need not be nilpotent. For example, strictly upper/lower triangular `2×2` nilpotents can sum to a Pauli matrix whose square is `I`.

The finite vertex must preserve **ordered factors** and their zero-mode/Klein phases. Ordinary BCH identities cannot be imported into the compressed setting without commutator and excursion hypotheses. Ch. 14 already records this limitation.

### 2.7 Regularization and phase-field reconstruction

The discrete Umbral difference calculus is not, on its own, a substitute for continuum ultraviolet renormalization. A sharp Fourier band is a regulator with a *different* finite-size correction structure from the soft multiplier `exp(-a|q|/2)` used in von Delft–Schoeller. Do not set `a=0` inside their intermediate expressions and discard `O(a/L)` terms.

Suggested program:

- Specify a finite Fourier multiplier `w_m`, and reconstruct the nonzero-mode phase field from currents.
- Define the inverse difference operator **only on mean-zero functions**, with the zero charge mode separate.
- Decide if products are formed before projection (non-aliasing) or via cyclic convolution (aliasing).
- Derive the refermionized-density bilinear expression and identify the exact finite-cutoff/edge discrepancy.
- Only after these identities are established, formulate a regulator-comparison or limiting theorem.

An exponential-vertex equality alone does not prove equality of phase fields: operator exponentiation is non-injective.

### 2.8 Zero-mode phase, parity Majorana, and the quadratic model

In the notation of the reference, for `P∈{0,1}` and integer `𝒩 = N_rel - P/2`:

\[
\tfrac12N_{\mathrm{rel}}^2
=\tfrac12\mathcal N(\mathcal N+P)+P/8.
\]

Keep the finite-size shift `Δ_L P/8` with `Δ_L=2πu/L` (assuming lattice spacing one and the velocity convention `u`). This is a physically relevant `O(1/L)` **zero-mode** contribution; it is not identical to UV corrections `O(a/L)`.

The reference's unitary zero-mode rotation is a diagonal charge-dependent phase; implement it as an indexed basis phase map rather than requiring a general matrix exponential. Define `γ=(-1)^𝒩` with `γ†=γ`, `γ²=1` and prove its anticommutation with charge-changing refermions. A normalized Majorana `α_d=γ/√2` satisfies `{α_d,α_d}=1`. Do not append an unrelated impurity fermion that doubles the Hilbert space without explicit motivation.

Distinguish an *effective exactly quadratic model* from a proved unitary equivalence to the microscopic **finite-band** impurity Hamiltonian: this equivalence is an additional comparison theorem.

### 2.9 Factorization and the two meanings of parity

For a genuine tensor decomposition `H=H_- ⊗ H_+`, product state, independent Hamiltonian summands, and tensor-product operator, the two-point function factors exactly. However, physical charge sectors obey a parity-gluing condition, and electron insertion changes total charge `Q`. Therefore a physical Green's function factorization needs sector-resolved source/target and cocycle compatibility rather than merely an unqualified tensor-product slogan.

Use distinct type names:

- `ChargeParity`: `Q mod 2`, determines twisted Fourier boundary condition.
- `InsertionParity`: parity of the number of impurity-scattering events between operator insertions in a Dyson/Coulomb-gas expansion.

The `Z_e(τ)-Z_o(τ)` difference in von Delft–Schoeller Appendix K refers to *scattering-insertion parity*, not automatically to the even/odd total-charge sector partition functions. Treat any relationship as a theorem requiring proof.

### 2.10 TDOS is a finite spectral measure, then a limiting theorem

For a finite Hamiltonian, exact zero-temperature local addition/removal spectra have atoms:

\[
\rho_{\rm DOS}(\omega)=
\sum_n |\langle n,Q+1|c_x^\dagger|G,Q\rangle|^2
\delta(\omega-(E_n^{Q+1}-E_G^Q))
+\sum_m |\langle m,Q-1|c_x|G,Q\rangle|^2
\delta(\omega+(E_m^{Q-1}-E_G^Q)).
\]

Specify chemical potential/energy-origin convention. In Lean, prefer a finite *weighted list or finitely supported spectral measure* (transition energy, nonnegative weight); distributions or smooth densities are unnecessary for the first phase. A smeared resolvent/Poisson-kernel density is a separate explicitly regularized object. The `ρ_DOS(ω) ~ ω` statement at `g=1/2` is an infrared/thermodynamic asymptotic, not a pointwise identity for finite `L`.

---

## 3. Proposed categorical interfaces — Lean-style pseudocode

The following is **architectural pseudocode, not compilable Lean 4**. Names, coercions, module instances, exact imports, and `LinearMap` orientation must be reconciled against the actual pinned repository and Mathlib revision. In particular, `opaque` and dependent-index syntax below denote required interfaces, not declarations to copy unchanged into production files.

### 3.1 Charge and graded carriers

```lean
-- PSEUDOCODE ONLY
structure ChargeCoord where
  total : Int   -- Q = n_R + n_L
  right : Int   -- r = n_R

leftCharge q := q.total - q.right
relativeTwice q := 2 * q.right - q.total
chargeParity q := q.total mod 2

-- fiber includes branch admissibility and a joint excitation budget
BudgetFiber (L K : Nat) (q : ChargeCoord) : Type

-- one needs a proof of admissibility in both source and target
relLower (q : ChargeCoord) :
  BudgetFiber L K q →ₗ[Complex]
  BudgetFiber L K { total := q.total, right := q.right - 1 }

-- a parity-fixed direct-sum carrier, finite only after restricting index support
FixedTotalCarrier (L K : Nat) (Q : Int) :=
  DirectSum (admissibleRightIndices L K Q) (BudgetFiber ...)
```

**Clarification:** An actual `DirectSum` index may be over admissible `(Q,r)` subtypes. If family dimensions change with `r`, prefer a dependent direct sum to a homogeneous `Finsupp`; do not introduce a fake unconditional isometry. For finite computation, a finite `Finset` of admissible indices with explicit inclusions may be simpler than unrestricted `ℤ`-indexed support.

### 3.2 Twisted Fourier character and boundary condition

```lean
-- PSEUDOCODE ONLY
structure TwistDatum (L : Nat) (P : ZMod 2) where
  holonomy : UnitComplex
  condition : holonomy = (if P == 0 then -1 else 1)

TwistedSection (L : Nat) (P : ZMod 2) : Type
liftField : TwistedSection L P → (Int → Complex)

-- proof obligations
lemma winding : liftField f (x + L) = holonomy(P) * liftField f x
lemma translation_L : (twistedTranslate P)^L = holonomy(P) • id
lemma twisted_fourier_orthogonality : ...
```

Keep `L` for lattice length, `R`/`L` (or `+`/`-`) for branch constructors **without** a local variable named `L` for the left branch; follow the repository's established convention.

### 3.3 Finite compression defects

```lean
-- PSEUDOCODE ONLY
ambientAnnihilator (i : Mode) : End Complex FullFock
budgetProjection (sector cutoff) : End Complex FullFock
compress (P : Projection) (A : End Complex FullFock) := P * A * P

-- formal equation to prove in the ambient endomorphism algebra
lemma compressed_car_defect (P) (i j : Mode) :
  anticommutator (compress P (c i)) (compress P (cDag j))
   = kronecker i j * P
     - P * c i * (I-P) * cDag j * P
     - P * cDag j * (I-P) * c i * P

lemma protected_car (h_defects_zero : ...) :
  anticommutator ... = kronecker i j * identity_on_interior
```

The actual proof should reuse Ch. 20.1's projection insertion calculus. Add a test where the defect is **strictly nonzero**; do not test only protected inputs.

### 3.4 Relative Klein operator and cocycle

```lean
-- PSEUDOCODE ONLY
relKleinLower q :=
  compose (originalKleinRaise Left) (originalKleinLower Right)

lemma relKlein_total_conserved : target.total = source.total
lemma relKlein_relative_shift : target.right = source.right - 1
lemma relKlein_phase_matches_CAR : ...
lemma relKlein_adjoint_reverses_carriers : ...
lemma relKlein_boundary_defect : Kdag*K = sourceProjection - defectIn
```

The exact factor order must be checked against the reference and the Chapter 13 `P(ν,N)` cocycle. Proving only `Q` conservation is insufficient: signs on basis occupation states and cross-anticommutation are acceptance criteria.

### 3.5 Special hyperbolic pair and vertex

```lean
-- PSEUDOCODE ONLY
specialPair : HyperbolicPair Real :=
  { c := 3 * sqrt(2) / 4
    s := sqrt(2) / 4
    invariant := proof_of_(c*c - s*s = 1) }

lemma specialPoint_g : (specialPair.c - specialPair.s)^2 = 1/2
lemma specialPoint_vertex_coefficient : sqrt(2 * (1/2 : Real)) = 1

normalOrderedVertex q x :=
  expNil(raisingPhase q x) ∘
  budgetTransition ∘
  expNil(loweringPhase q x) ∘
  relKleinLower q ∘ zeroModePhase q x

-- ORDER ABOVE IS ILLUSTRATIVE ONLY.
-- Reconstruct the authoritative order from Eq. (14.7) and verify charge directions.
```

Crucial: do not copy this illustrative factor order as a theorem. The target-normalized phase factors and source zero mode must be verified against Eq. (14.7), and the backscattering creator has the opposite composite-Klein orientation.

### 3.6 Quadratic impurity model and finite spectral data

```lean
-- PSEUDOCODE ONLY
ChargeDiagonalRotation (Q P) : LinearIsometryEquiv ...
parityMajorana (Q) : End Complex FixedTotalCarrier

lemma parityMajorana_selfAdjoint : gamma† = gamma
lemma parityMajorana_square : gamma*gamma = I
lemma parityMajorana_anticommutes (k) : ...

EffectiveImpurityHamiltonian (L Q couplings twist) : HermitianEnd ...

-- target only after proving a matching carrier/intertwiner
lemma impurity_equivalence (U : UnitaryMap H1 H2) :
  U * physicalProjectedImpurity * U† = EffectiveImpurityHamiltonian

structure SpectralAtom where
  energy : Real
  weight : Real
  weight_nonnegative : 0 <= weight

localTDOSFinite : Finsupp SpectralAtomIndex Real
lemma tdos_weight_nonnegative : ...
lemma tdos_sumrule : totalSpectralWeight = (CAR_derived_expectation ...)
```

Prefer finite spectral projectors and algebraic identities before committing to diagonalization of a general parameter-dependent Hermitian matrix. A `StarAlgEquiv` is appropriate only **after** its algebra-domain relations are proved; for a single operator intertwining result, a `LinearIsometryEquiv`/unitary conjugation statement is weaker and often enough.

---

## 4. Phased backlog with gates

| Gate | Goal and deliverable | Prerequisites | Minimal acceptance test / counterexample |
|---|---|---|---|
| **G0 — Inventory and verification** | Commit-pinned inventory of actual Lean declarations, proof status, unsound axioms, imports, notes, and dependency graph | Repository access | `lake build` and target test logs reproduced; no "proved" status without proof term and source |
| **G1 — Integral charge geometry** | `(Q,r)` equivalence, admissible fibers, parity, sector transitions; architectural decision for finite vs unrestricted charge supports | CAR charge and Haldane layers | Inverse charge mapping, both parities, `Q` preservation of `K_rel` |
| **G2 — Twist/Fourier** | Parity-indexed twisted sections, unitary Fourier orthogonality, winding and translation identities | G1, Chs. 3 and 6 | `P=0`: antiperiodic, `P=1`: periodic; no false `ZMod L → ℂ` periodicity |
| **G3 — Composite Klein and compression** | Cocycle-exact typed shift, adjoints and endpoint defects, general compressed CAR defect, protected-sector corollary | G1, Chs. 13 and 20.1 | `L=4` and `L=12` prior counterexamples; nonzero defect witness |
| **G4 — Refermionized vertex bridge** | Definitions in ambient formal oscillator-charge model; explicit cutoff-dependent comparison and residuals; no unconditional CAR claim | G2–G3 and Ch. 14 | Leading vertex matrix elements, cross-signs, missing-mode test; no unexplained use of BCH |
| **G5 — Special point and quadratic model** | `g=1/2` specialization, source zero-mode phases, parity Majorana, finite quadratic effective Hamiltonian | G1–G4 (or independent construction without false comparison) | Exact `g=1/2`; Hermiticity; `γ²=1`; `Δ_L P/8` retained |
| **G6 — Finite observables** | Exact sector-resolved correlators and finite TDOS spectral atoms; proper `InsertionParity` expansion | G5 plus a proven tensor/graded-sector representation | Spectral weights ≥0, sum rules, `Q±1` selection, small-size matrix comparison |
| **G7 — Optional asymptotic research** | Regulator comparison, uniform-in-`L` estimates, thermodynamic TDOS law | G6 and new analytic design | State theorem with topology, order of limits, quantified cutoff and finite-size errors |

**Suggested sequencing:** G0 → G1+G2 (can partly overlap) → G3 → G4 → G5 → G6. Do not make G4's unproved comparison a hidden premise of G5: the effective resonant-level Hamiltonian can be constructed independently while its equivalence remains a separate conditional target. G7 is an independent research proposal, not a finite-Lean sprint commitment.

### Non-vacuity and adversarial requirements at every gate

- Track whether hypotheses admit concrete nonzero fibers; give at least one constructive witness.
- Distinguish maps with codomain ambient Fock from endomorphisms of a budget.
- Verify the same signs in both the `R,L` and `+,-` conventions before exposing a public API.
- For each equality `A=B`, test a basis state near each finite-band boundary and a protected interior state.
- Do not replace a target theorem by hypotheses that trivially imply it, or by `by decide` on a single toy instance.
- Require negative regression tests that would fail if the defect term were omitted.
- Reject `sorry`, unreviewed `axiom`, fake `True` theorems, and unused/excessively strong premises as evidence of success.
- Keep numerical checks as **diagnostics**, never substitutes for kernel proofs.

---

## 5. Architecture decision records to settle before implementation

**ADR-01 — Ambient representation.** Is the goal (A) finite CAR with an effective quadratic model, (B) algebraic infinite-sea/oscillator refermionization with finite computational budgets, or (C) both with an explicit comparison? **Recommendation: C as long-term architecture, A as the first completely certifiable observable target.** Do not pretend the two are already equivalent.

**ADR-02 — Exactness contract.** Will "refermionized CAR" mean (a) exact CAR in a *complete new finite-mode Fock representation*, (b) a protected-domain equality, or (c) compressed CAR plus a defect? **Recommendation: make (c) primary for budget transport; use (a) for an independently constructed finite effective Fock model.**

**ADR-03 — UV/geometry.** Preserve the existing discrete lattice and finite Fourier band, or introduce an auxiliary finite circumference with an unbounded integer Fourier ladder? **Recommendation: preserve the existing lattice as primary and treat the continuum-circle construction as a distinct comparison model.**

**ADR-04 — Physical state carrier.** Fixed total charge `Q` is convenient for the impurity Hamiltonian, but the electron Green's function transitions `Q → Q±1`. **Recommendation: an indexed family of fixed-`Q` fibers, with a finite direct sum for the observable calculation.**

**ADR-05 — Primary physics deliverable.** Prove first the exact finite-system spectral measure and parity energies, then decide whether a continuum `ρ(ω)∼ω` project is worth the additional analysis.

Every ADR must include chosen option, alternative rejected, mathematical justification, needed declarations, empirical/counterexample check, and downstream breakage assessment.

---

## 6. External references and API verification

### Primary peer-reviewed reference

J. von Delft and H. Schoeller, **“Bosonization for beginners — refermionization for experts,”** *Annalen der Physik* **7**, 225–305 (1998), DOI **10.1002/andp.19985100401**. Publisher record: <https://doi.org/10.1002/andp.19985100401>. Author manuscript identifier: `cond-mat/9805275` (metadata cross-check: <https://arxiv.org/abs/cond-mat/9805275>). Key areas: Sec. 10.C (finite-size refermionization), especially construction of new fermions, phase-field reconstruction, zero-mode/parity, impurity Majorana rotation; Appendix K for `Z_e-Z_o`. The source's thermodynamic TDOS conclusion is `ρ_DOS(ω) ∼ ω` at `g=1/2`, not a finite-volume smooth-density identity.

### Authoritative Mathlib documentation to consult at pinned commit

- Mathlib `Algebra.DirectSum.Finsupp`: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/DirectSum/Finsupp.html>
- Mathlib `Data.Finsupp.Defs`: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finsupp/Defs.html>
- Mathlib `LinearAlgebra.Projection` (source, includes projection onto complementary/orthogonal submodules): <https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/LinearAlgebra/Projection.lean>

**API rule:** The public documentation pages and their names can change. The agent must verify exact declarations/instances in the repository's `lake-manifest.json`-pinned Mathlib version and use source inspection or `#check` in a disposable scratch module; do not promote the pseudocode names above as actual buildable code.

---

## 7. Antigravity agent handoff prompt — paste in full

> **ROLE:** You are the mathematical-physics architect and independent Lean 4/Mathlib4 proof auditor for `Bosonize-Lean`. Work in **research/planning mode only**. The attached review and `main(5).pdf` are the source material. The review distinguishes manuscript assertions from confirmed kernel theorems.
>
> **MISSION:** Produce a commit-pinned, dependency-aware strategy to extend the existing finite-lattice constructive bosonization formalization to a `g=1/2` local impurity and finite-size refermionization. Do **not** implement or refactor production Lean modules in this phase. Prepare a staged technical plan for later approval.
>
> **MANDATORY FIRST STEP:** Inspect the actual repository layout, `lean-toolchain`, `lakefile`, `lake-manifest.json`, source modules, tests, notes, and existing validation logs. Record HEAD commit, dirty state, Lean/Mathlib versions, exact imported declarations, and whether `lake build` succeeds. Do not rely on source-file names invented by this prompt. If repository or logs are inaccessible, mark all statuses *unverified* and request access rather than fabricating them.
>
> **READ THE DOCUMENTED FOUNDATION:** Audit Chapters 7–8, 10–11, 13–14, 18–20 and Appendix B of the monograph, especially Thm. 10.6, Thm. 13.13, Eqs. (14.7), (14.11)–(14.17), Remark 14.19, Eqs. (18.5)–(18.18), the Ch. 19 proof-status boundary, Thm. 20.4, Thm. 20.6, and §§20.2.8/20.3.7. Classify each claim as `kernel_proved`, `manuscript_proved_only`, `conditional`, `counterexample`, `planned`, or `not_verified`, with the defining declaration or document anchor.
>
> **MATHEMATICAL AUDIT:** (1) Type charge coordinates as integral `(Q,r)` and prove compatibility with branch charges and parity `P=Q mod 2`. (2) Define the composite Klein lowering `K_rel=F_L† F_R` as a typed charge-shift map, with CAR cocycle and boundary defects; distinguish its adjoint. (3) Treat even/odd twisted Fourier boundary conditions as parity-indexed sections, not ordinary periodic functions. (4) Prove/formulate exact compressed CAR anticommutator defects and protected-sector corollaries; do not assert global CCR/CAR for arbitrary truncated vertex modes. (5) Preserve Ch. 14's ordered `expNil` factors, full cutoff coverage, and counterexamples. (6) Specialize `HyperbolicPair` at `g=1/2`, keeping all zero modes and `O(1/L)` terms. (7) Separate parity of total charge from parity of impurity insertions in `Z_e-Z_o`. (8) Define exact finite spectral measures before proposing asymptotic TDOS claims.
>
> **DESIGN REQUIREMENTS:** Prefer existing structures and theorem reuse. Objects are typed carriers and subtypes; morphisms are `LinearMap`, typed adjoints, `LinearIsometryEquiv`, and only then `AlgEquiv`/`StarAlgEquiv` if mathematically justified. Separate pure definitions/theorems from executable finite tests. State every source/target carrier and projection point. Never hide projection excursions or assume budget invariance. Maintain consistent branch labels and sign conventions; distinguish lattice length `L`, oscillator cutoff `M`, budget `K`, and physical circumference if introduced.
>
> **DELIVERABLES (MARKDOWN ONLY, NO PRODUCTION CODE):**
> 1. `repository_audit.md` — pinned environment, executable validation logs, theorem/declaration map, fake-green/nonvacuity risks, missing proofs, known failures.
> 2. `proof_status_ledger.md` — exact document theorem ↔ Lean declaration links, assumptions, carrier, strength, confidence, outstanding comparison.
> 3. `architecture_decisions.md` — ADR-01 through ADR-05, options, recommendations, rejected alternatives, migration impacts.
> 4. `refermionization_theorem_spec.md` — explicit mathematical theorem statements, inputs/outputs, boundary defects, counterexamples, and non-compiling Lean-style interface pseudocode.
> 5. `phased_implementation_plan.md` — G0–G7 tasks, prerequisites, estimated proof difficulty (qualitative), tests, acceptance gates, parallelization boundaries, and rollback path.
> 6. `research_reference_audit.md` — only primary peer-reviewed literature/books, with publisher-verified metadata; mark every unchecked claim as such. Include a table of where the source uses a continuum circle/infinite sea and where the monograph uses a finite lattice.
>
> **ADVERSARIAL VALIDATION:** For every proposed theorem, specify at least one example where it is nontrivial and one case in which weakening a hypothesis fails. Reproduce the Ch. 14 `K=0` deep-hole and insufficient-mode-coverage counterexamples, and Ch. 20.1's nonzero intermediate-projection residual. Demand no `sorry`, unreviewed axioms, tests equivalent to `True`, hidden strong hypotheses, or statements proved only by definitionally circular assumptions. Distinguish formal proof from finite matrix numerical testing.
>
> **STOP CONDITIONS:** Stop and flag a decision if a necessary equivalence is unjustified, if `g=1/2` field normalizations disagree, if any parity sector is missing, if an apparent exact CAR fails at a budget boundary, or if a required source declaration is not actually present. Do not silently repair the mathematics by changing the model.
>
> **FINAL RESPONSE FORMAT:** Produce an executive findings page, critical path diagram, task dependency table, theorem ledger, ADR decisions, precise proof obligations, falsifying cases, bibliography and open questions. Do not promise a thermodynamic `ρ_DOS(ω)∼ω` theorem until a separate order-of-limits and convergence design exists. **No production Lean implementation until the user explicitly authorizes the next phase.**

---

## 8. Definition of “ready for implementation”

Antigravity's planning deliverables are acceptable when:

1. Each reused foundational theorem is linked to a repository declaration and checked against the pinned toolchain, or explicitly marked not found.
2. The *first* new theorem has a concrete type, no ambiguous source/target charge, realistic hypotheses, and a minimal non-vacuous witness.
3. The implementation graph has no circular dependencies among composite Klein factors, vertex comparison, quadratic impurity equivalence, and TDOS.
4. Every bridge between finite CAR and uncompressed oscillator/charge algebra has a documented map and either a proof or an explicit residual/conditional status.
5. All negative witnesses are scheduled before strong equality claims.
6. No thermodynamic or continuum statement is represented as a consequence of finite linear algebra alone.

**Recommended first approved implementation unit:** integral charge-coordinate equivalence, admissible fixed-`Q` fiber interfaces, and charge/parity typing. It is independent of the disputed vertex equivalence and creates the exact domain/codomain discipline needed for all subsequent refermionization morphisms.
