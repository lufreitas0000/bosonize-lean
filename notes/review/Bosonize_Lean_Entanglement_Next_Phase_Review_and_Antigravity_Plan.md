# Bosonize-Lean — Entanglement Extension: Source Audit, Mathematical Strategy, and Antigravity Planning Packet

**Review date:** 2026-10-17  
**Status:** Research and architecture review; **not a verified Lean implementation**.  
**Requested scope:** Connect the finite spatial CAR net (Chapter 6) with states/correlators (Chapter 19) and investigate exact finite-volume entanglement and charged moments.  
**Implementation authorization:** **Planning only.** All Lean blocks below are **non-compiling architectural pseudocode**, deliberately not verified against the repository or Mathlib. Do not generate or modify production Lean code until separately authorized.

## Executive decision

**Do not begin by restricting the abstract interacting Luttinger functional to the spatial CAR net.** In the current mathematical sources, the dressed functional is defined on an *uncompressed oscillator \(*\)-algebra*, not on the finite CAR operator algebra or a budget endomorphism algebra. There is no established state-preserving identification allowing this restriction.

Instead, build an **exact finite-CAR entanglement subsystem**, then add a **separately gated state/correlator comparison** with the bosonic theory:

1. Preserve the full-Fock local CAR net as the spatial-locality carrier.
2. Construct genuine full-Fock states, their local restrictions, exact local charge projectors, and charge-generating polynomials.
3. Derive integer Rényi moments using finite tensor products and replica permutation identities, without operator logarithms.
4. Prove the exact periodic discrete density-primitive/boundary identity **including the uniform charge mode**.
5. Connect the primitive to the Chapter 15 truncated current field only through an explicit missing-mode/wrap remainder.
6. Provide a free, gauge-invariant CAR quasi-free benchmark using a one-particle correlation matrix; do not transfer this Gaussian determinant formula to the interacting bosonic oscillator state without a new theorem.
7. Defer interacting finite-CAR relative entropy and coherent modular identities until the state carrier and comparison bridge have been established.

This ordering minimizes dependency on unproved Mattis–Mandelstam identities, makes small finite-lattice statements falsifiable, and creates a reusable foundation for stronger research questions. It is the preferred approach under the stated proof-audit and finite-dimensional constraints, **not a mathematical optimality theorem**.

---

## 1. Source inventory and reliability boundaries

### 1.1 Materials actually reviewed

| Source | Snapshot / identified status | How to use it |
|---|---|---|
| **`main(1).pdf`**, *Constructive 1+1D Lattice Bosonization: Finite Constructions and Algebraic Models* | Dated **17 October 2026**; 239 PDF pages | Most recent attached mathematical narrative. Especially Chs. 4–7, 9–10, 14–15, 18–20, Appendix E. It is a **monograph**, not evidence that each claim is already compiled in Lean. |
| **`Bosonize_Lean_Ch19_Ch20_Formalization_Strategy.md`** | Dated **16 October 2026**; explicitly design specification, not compilation certification | Useful for architecture, the three-carrier separation, operator-word protection and agent gates. Its suggestions require rechecking against current Core. |
| **`ch19_phase_ab_design.md`** | Dated **13 October 2026**; unverified design draft | Names proposed Ch19 interfaces and explains why A08 and Ch18 imports must be checked. Its file names and APIs are **provisional**. |
| **`packet(20261015-183527).md`** | Older drafting/workflow packet; source baseline recorded therein | Historical workflow evidence, not current repository truth. States that Ch19/A08 reached Phase B but not Core promotion and distinguishes book writing from proof acceptance. |

**Not inspected:** the live Git checkout, current Git commit, `lakefile`, `lean-toolchain`, `lake-manifest.json`, source modules, build logs, current proof runner, frozen Core hashes, pending branches, and agent permissions. This document **cannot certify** live implementation status. The Antigravity agent must establish it as its first task.

### 1.2 Evidence labels for subsequent work

Use these labels in all plans, pull requests and manuscript updates:

- **M — Mathematical claim in manuscript:** a theorem with a purported proof in the book; not automatically compiled.
- **D — Design / hypothetical interface:** a proposal with no checked Lean declaration.
- **S — Staged Lean:** source exists but verification/promotion status must be established.
- **V — Verified Lean:** current pinned-toolchain build succeeds, with no untrusted placeholders or unexpected axioms in the theorem's dependency closure.
- **P — Promoted Core:** V plus the project's explicit source-lock, dependency, review and release criteria.
- **N — Numerical witness:** useful counterexample or regression check, never a proof.

Never equate M, S, V and P. In particular, **“Phase B complete” does not imply P**.

### 1.3 What the monograph presently establishes or explicitly limits

| Existing foundation | Monograph locator | Source-level assessment |
|---|---|---|
| Full fermionic Fock space, CAR and position/momentum fields | Chs. 4–5 | Mathematically appropriate base for a full spatial local net. |
| Local field algebras, even subalgebras, graded locality, inclusions | Ch. 6, especially Defs. 6.2–6.4 and Thms. 6.7–6.9 | Defines **spatial** graded CAR locality. Do not infer a continuum type-III net or dynamical spacelike causality without time evolution and relevant estimates. |
| Charge sectors, budget projections, filtered actions and excursion corrections | Ch. 7, especially §§7.6–7.7 | Energy budgets are global; spatial support and momentum cutoff do not commute generically. |
| Local density Fourier transform and cyclic wrapping | Ch. 9, §9.7, Eq. (9.18) | Microscopic density modes contain **nonwrapping currents plus wrap remainder**. |
| Protected current/Schwinger commutators | Ch. 10 | Valid on stated protected input domains, **not global finite-dimensional CCR**. |
| Projected Mattis–Mandelstam candidate | Ch. 14, Thm. 14.17, Rem. 14.19 | **Conditional equivalence only**; deep-hole and missing-mode counterexamples. |
| Dual fields and discrete gradients | Ch. 15, §15.4, Thm. 15.15 | Periodic derivative cannot supply the missing uniform Fourier mode. |
| Bogoliubov transformations and finite interacting Hamiltonian expressions | Ch. 18 | Does **not** construct an interacting finite-CAR state equal to the abstract dressed oscillator vacuum. |
| Abstract Gaussian state and ordered kernels | Ch. 19, especially Eq. (19.16), Thm. 19.10, §19.5 | Functional lives on uncompressed CCR/oscillator algebra. Abstract and finite-sea expectations agree for certain **free protected quadratic** quantities, not all words or an interacting vacuum. |
| Exact projected CAR composites / formal vertices | Ch. 20, especially §20.1 residual, §20.2 formal vertices, §20.3 model duality | Distinct carriers. Nonzero projection residuals and a finite CAR/formal-vertex normalization mismatch are explicit; formal series are not analytic unitary operators without convergence. |
| Implementation caveat in Appendix E | Appendix E.1 and E.6 | Ch19 proof batch reported Phase-B complete, **not Core promoted**; compression does not inherit a common dressed vacuum. |

**High-priority status verification:** Obtain a live proof ledger for Ch06, Ch07, A08, Ch14, Ch15, Ch18, Ch19 and Ch20 with exact module paths, theorem names, build status, axioms, accepted patches and promotion decisions. The uploaded book alone cannot supply that ledger.

---

## 2. Mathematical audit: five non-negotiable corrections

### 2.1 A state cannot be restricted across unrelated algebra carriers

Let the full physical space be \(\mathcal H_F=\mathcal F_-(\mathfrak h)\), where \(\mathfrak h=\mathbb C^{\mathrm{Branch}\times\Lambda}\) in the two-branch model, and let \(\mathfrak A_F=\operatorname{End}_{\mathbb C}(\mathcal H_F)\). The spatial net is \(\iota_I:\mathfrak A(I)\hookrightarrow\mathfrak A_F\).

For an energy budget \(\mathcal B_K\subset\mathcal H_F\), let \(j_K:\mathcal B_K\hookrightarrow\mathcal H_F\) be the isometric inclusion. Compression is

\[
\mathcal C_K(A)=j_K^\dagger A j_K.
\]

It is unital, \(*\)-preserving, and completely positive, but **not multiplicative**:

\[
\mathcal C_K(AB)-\mathcal C_K(A)\mathcal C_K(B)
=j_K^\dagger A(1-P_K)Bj_K,\qquad P_K=j_Kj_K^\dagger.
\tag{2.1}
\]

It is incorrect to model this map as `AlgHom`, `AlgEquiv` or `StarAlgEquiv`; use a linear map and prove positivity separately. If \(\omega_K\) is a genuine positive normalized state on \(\operatorname{End}(\mathcal B_K)\), its full-CAR extension and restriction are legitimate:

\[
\omega_I=\omega_K\circ\mathcal C_K\circ\iota_I.
\tag{2.2}
\]

But Ch19's dressed functional \(\omega_P=\omega_0\circ\beta^{-1}\) is on the **uncompressed oscillator \(*\)-algebra**. Equation (2.2) does not furnish a state-preserving map from that algebra into the physical net.

**Concrete obstruction / regression theorem:** on a fixed-particle-number budget, \(P_Kc_xP_K=0=P_Kc_x^\dagger P_K\), but \(P_Kc_x^\dagger c_xP_K\) can be nonzero. Compressing separate generators then multiplying loses a legitimate local number observable.

### 2.2 Local field net vs. parity-even observable net

Ch6 distinguishes \(\mathfrak A(I)\), generated by odd CAR fields, from its even subalgebra \(\mathfrak A^+(I)\). These give different algebraic entropy problems. A finite even CAR algebra can have a nontrivial center (local parity blocks). A graded Hilbert-space factorization also requires a chosen orbital ordering/Jordan–Wigner convention.

**Recommendation:** primary milestone uses the **full local CAR field algebra**, with a documented spatial Fock tensor factorization and local density matrix. Add restrictions to the parity-even algebra as a **separate module**, not a change of meaning to existing `localState` notation. Ensure the `Branch`/species index is accounted for: with two orbitals per spatial site, a region of \(\ell\) sites has local Hilbert dimension \(2^{2\ell}\), not \(2^\ell\).

### 2.3 A bosonic Gaussian state is not necessarily fermionic quasi-free

Bosonic oscillator Wick rules in Ch19 do **not** imply Wick's theorem for microscopic fermion fields. The familiar determinant formula involving a restricted one-particle correlation matrix applies to **gauge-invariant quasi-free CAR states**, notably finite Slater determinants and thermal quadratic fermions, not to generic interacting Luttinger states or Haldane partition excitations.

**Recommendation:** first implement a free-CAR quasi-free **benchmark**; make any interacting determinant evaluation explicitly conditional on an independently proved CAR quasi-free hypothesis (generally false for interacting states).

### 2.4 Purity ratios are not relative entropies

The \(n\)-th integer Rényi moment \(\mathrm{Tr}(\rho_I^n)\) is polynomial in matrix entries and can be expressed as a replica-permutation expectation. The ratio \(\mathrm{Tr}(\rho_I^2)/\mathrm{Tr}(\sigma_I^2)\) is a **purity ratio**, not an information-theoretic Rényi divergence. For example, where \(\sigma\) is invertible,

\[
D_2^{\rm Petz}(\rho\Vert\sigma)=\log\operatorname{Tr}(\rho^2\sigma^{-1}).
\]

Faithfulness/support conditions matter for relative modular operators. Never introduce operator logs just to define the first exact charged moments. Their scalar entropy logs can be postponed.

### 2.5 Symmetry-resolved entanglement and entanglement asymmetry differ

For a globally charge-invariant state \([\rho_F,Q]=0\), the reduced state satisfies \([\rho_I,N_I]=0\), so it has nontrivial **charge-resolved entanglement** but zero **\(U(1)\) entanglement asymmetry**. Do not propose a nonzero asymmetry for the definite-total-charge dressed vacuum without deliberately changing the state/symmetry.

For general, charge-noninvariant \(\rho_I\), the charged coefficient \(\operatorname{Tr}(\rho_I^n\Pi_q)\) is **not** generally the \(n\)-th moment of the \(q\)-block. To obtain sector moments use \(\operatorname{Tr}[(\Pi_q\rho_I\Pi_q)^n]\); the equality with coefficients of \(\operatorname{Tr}(\rho_I^n z^{N_I})\) requires \([\rho_I,N_I]=0\).

---

## 3. Exact finite-lattice theorem targets

### Theorem group T1 — Physical state restriction

Assume a finite-dimensional Hilbert space \(\mathcal H_F\), a normalized positive full-CAR state \(\omega_F\), and inclusion \(\iota_I\) of the local \(*\)-algebra. Define \(\omega_I=\omega_F\circ\iota_I\). Prove complex linearity, normalization, positivity, and functorial restriction \(I\subseteq J\).

If \(\omega_F(A)=\operatorname{Tr}(\Gamma_FA)\), additionally construct a graded-ordering-dependent spatial Fock factorization and show

\[
\omega_I(A)=\operatorname{Tr}(\Gamma_IA),\quad \Gamma_I=\operatorname{Tr}_{I^c}\Gamma_F.
\tag{T1}
\]

Specify whether `Γ_I` represents full field algebra or parity-even algebra restriction; do not conflate them.

### Theorem group T2 — Compression defect / state lifting

For \(j_K\) an isometry, prove \(\mathcal C_K\) linear, unital and adjoint-preserving, positivity and the exact defect (2.1). An elementary proof of complete positivity is

\[
\sum_{i,j}\langle v_i,\mathcal C_K(A_i^\dagger A_j)v_j\rangle
=\left\|\sum_j A_jj_Kv_j\right\|^2\ge0.
\tag{T2}
\]

This is optional for the first state-restriction implementation if positive vector states on full Fock are already available, but it is the correct link to energy-budget states.

### Theorem group T3 — Charge generating **polynomial**

Let \(O_I=\mathrm{Branch}\times I\) be the finite local orbital type and \(n_a=c_a^\dagger c_a\), with \(n_a^2=n_a\) and \([n_a,n_b]=0\). Then

\[
\boxed{\mathcal P_I(z)=\prod_{a\in O_I}(1+(z-1)n_a)
=\sum_{q=0}^{|O_I|}z^q\Pi_{I,q}.}
\tag{T3}
\]

All coefficients \(\Pi_{I,q}\) are pairwise orthogonal projectors and sum to the identity. For a positive normalized state,

\[
p_{I,q}=\omega_F(\Pi_{I,q})\ge0,\qquad\sum_qp_{I,q}=1.
\]

At \(z=e^{i\alpha}\), \(\mathcal P_I(z)=e^{i\alpha N_I}\), as a **finite spectral identity**, not a formal oscillator-series substitution. If a `Finset.prod` API requires commutative multiplication, do **not** assume matrix multiplication commutes globally: construct an ordered fold of these **specific commuting factors**, then prove independence of ordering.

Normal ordering by a translation-invariant reference \(q_{\rm ref}\) shifts the charge \(N_I\mapsto N_I-\ell q_{\rm ref}/L\). Keep the shift as a scalar factor; ordinary polynomial variables are simplest for unshifted integer local charge.

### Theorem group T4 — Exact discrete boundary primitive with zero mode

Let \(\Lambda=\mathrm{ZMod}\,L\), \(L>0\), and choose an **oriented interval** of length \(0<\ell<L\):

\[
I(x_1,\ell)=\{x_1,x_1+1,\ldots,x_1+\ell-1\},\quad x_2=x_1+\ell\pmod L.
\]

Set \(Q=\sum_x n_x\), \(\delta n_x=n_x-Q/L\), and choose a periodic primitive \(\Phi\) satisfying \(\Delta\Phi(x)=\delta n_x\). Such a primitive exists since \(\sum_x\delta n_x=0\); fix a basepoint or zero-average convention for uniqueness. Then

\[
\boxed{N_I=\frac\ell L Q+\Phi(x_2)-\Phi(x_1).}
\tag{T4a}
\]

With a translation-invariant reference occupation \(q_{\rm ref}\):

\[
:N_I:=\Phi(x_2)-\Phi(x_1)+\frac\ell L(Q-q_{\rm ref}\,1).
\tag{T4b}
\]

Because all density operators commute, the chosen microscopic primitives commute and the exact finite-dimensional characteristic-unitary identity follows:

\[
e^{i\alpha N_I}=e^{i\alpha\ell Q/L}\,e^{i\alpha\Phi(x_2)}e^{-i\alpha\Phi(x_1)}.
\tag{T4c}
\]

**Essential qualification:** this \(\Phi\) is an exact **microscopic density primitive**, not automatically the Ch15 oscillator phase. The latter omits the zero mode and generally high-momentum/wrapping terms. Before a bosonization identification, prove

\[
:N_I:=\frac\ell L(Q-q_{\rm ref}\,1)
+\Phi_M(x_2)-\Phi_M(x_1)+R_I^{(M)}.
\tag{T4d}
\]

Here \(R_I^{(M)}\) is **defined as an exact difference**, then decomposed into omitted modes and Ch9 wrap remainders. Do not assert \(R_I^{(M)}=0\) without an explicit protected-domain/matrix-element proof. The full Fourier primitive, if desired, is

\[
\Phi(x)=\frac1L\sum_{q\ne0}
\frac{\zeta^{-qx}}{\zeta^{-q}-1}\,\widehat{\delta n}_q,
\qquad\widehat{\delta n}_q=\sum_x\zeta^{qx}\delta n_x.
\]

### Theorem group T5 — Replica moment / sector resolution

For full-CAR density \(\Gamma_F\), reduced density \(\rho_I\), and the operator \(U_I^{(n)}\) implementing the cyclic permutation of **local** factors among \(n\) replicas,

\[
\boxed{\operatorname{Tr}(\rho_I^n)
=\operatorname{Tr}(\Gamma_F^{\otimes n}U_I^{(n)}).}
\tag{T5a}
\]

Test the graded spatial ordering and cyclic-permutation convention carefully. With local charge polynomial,

\[
Z_n(z)=\operatorname{Tr}(\rho_I^n\mathcal P_I(z)),\quad
Z_n(z)=\sum_q z^q\operatorname{Tr}[(\Pi_q\rho_I\Pi_q)^n]
\]

for \([\rho_I,N_I]=0\). For general states, introduce charge dephasing \(\mathcal T(\rho_I)=\sum_q\Pi_q\rho_I\Pi_q\) and study its moments separately.

A zero-log observable is the purity \(P_2=\operatorname{Tr}(\rho_I^2)\). Relative-entropy or Rényi-divergence names must not be assigned to unrelated purity ratios.

### Theorem group T6 — Explicit free-fermion benchmark (optional first release)

For a **gauge-invariant CAR quasi-free** state with restricted one-body covariance \(C_I\), prove or first test in a separate mathematical module

\[
\boxed{Z_n(z)=\det[(1-C_I)^n+zC_I^n].}
\tag{T6}
\]

This is an exact finite-dimensional benchmark for free Slater/thermal quadratic states and provides independent small-lattice oracle data. It is **not** a consequence of the Ch19 bosonic oscillator Wick theorem. If Mathlib proof dependencies for matrix spectral calculus dominate the sprint, defer this theorem and retain brute-force small-system checks as **numerical witnesses only**.

### T7 / T8 — Deliberately deferred research

- **T7 (conditional finite-CAR/current comparison):** for an explicitly given class of words, state, domain, cutoff and intertwiners, prove agreement of specified matrix elements/correlations with bounded or vanishing residuals. Reuse Ch14 and Ch19 hypotheses; do not present a general interacting-state equivalence.
- **T8 (relative entropy / modular):** after selecting full vs even local algebra, faithful states/supports and an actual finite-CAR interacting state, develop finite relative modular operators, Petz/sandwiched Rényi divergences or coherent modular formulas. No unrestricted type-III conclusions from a single finite system.

---

## 4. Lean 4 architectural pseudocode — **NOT code to paste or compile**

The following is **interface notation using Lean-like syntax**, not a set of verified Mathlib declarations. Names such as `FullCAR`, `LocalCAR`, `End`, `LocalOrbital`, `adjoint`, `trace`, `TensorPower`, and `orderedProduct` are conceptual placeholders. The agent must first map each to existing repository and pinned Mathlib APIs. `THEOREM_TO_PROVE` and `CONSTRUCTION_TO_SPECIFY` are obligation markers, **not axioms**.

### 4.1 Domain objects and state morphisms

```lean
-- PSEUDOCODE: DO NOT COMPILE OR TREAT AS ACCEPTED THEOREMS.
namespace Bosonize.Research.Entanglement

-- Reuse existing finite Fock, field operators and local StarSubalgebra.
variable (H : Type) (B : Type)
variable [ComplexHilbert H] [ComplexHilbert B] -- conceptual constraints

structure BudgetInclusion where
  incl : B →ₗᵢ[ℂ] H
  -- projector and adjoint laws must be derived, not postulated.

def compress (j : BudgetInclusion H B) (A : End ℂ H) : End ℂ B :=
  j.incl.adjoint ∘ₗ A ∘ₗ j.incl

-- Required contracts; their proofs are not supplied here.
theorem compress_unital : compress j (1 : End ℂ H) = 1 := THEOREM_TO_PROVE
theorem compress_star : compress j (star A) = star (compress j A) := THEOREM_TO_PROVE
theorem compress_defect :
  compress j (A * B) - compress j A * compress j B =
  j.incl.adjoint ∘ₗ A ∘ₗ (1 - j.projector) ∘ₗ B ∘ₗ j.incl :=
  THEOREM_TO_PROVE

structure PositiveState (A : Type) where
  linear : A →ₗ[ℂ] ℂ
  normalized : linear 1 = 1
  positive : ∀ a, 0 ≤ (linear (star a * a)).re
  -- Hermitian reality or nonnegative-real embedding may need stronger data.

-- For iI : LocalCAR I ↪⋆ₐ[ℂ] FullCAR:
def restrictState (ω : PositiveState FullCAR) (iI : LocalInclusion I) :
    PositiveState (LocalCAR I) := CONSTRUCTION_TO_SPECIFY

end Bosonize.Research.Entanglement
```

**Type risks:** `StarSubalgebra` membership vs coercion to the ambient algebra, finite-dimensional inner-product `adjoint` interfaces, `LinearIsometry` vs `LinearIsometryEquiv`, and the distinct roles of a positive linear state and a multiplicative algebra morphism. Do not create a new `PositiveState` structure if the project already supplies a compatible certified abstraction.

### 4.2 Oriented interval and charge polynomial

```lean
-- PSEUDOCODE ONLY
structure OrientedInterval (L : ℕ) where
  start : ZMod L
  length : ℕ
  nonempty : 0 < length
  proper : length < L

-- The map Fin length → ZMod L sends i ↦ start + i and is injective.
def sites (I : OrientedInterval L) : Finset (ZMod L) := ...

def localCharge (I : OrientedInterval L) : End ℂ FullFock :=
  ∑ x ∈ I.sites, ∑ ν : Branch, occupation (ν, x)

-- Use an ORDERED fold over local orbitals; general endomorphisms
-- do not form a commutative monoid.
def chargePolynomial (I : OrientedInterval L) (z : ℂ) :
    End ℂ FullFock :=
  orderedProduct (sort (localOrbitals I))
    (fun a => 1 + (z - 1) • occupation a)

theorem local_occupations_commute :
  ∀ a b, Commute (occupation a) (occupation b) := THEOREM_TO_PROVE

theorem chargePolynomial_coefficients :
  chargePolynomial I z = ∑ q : Fin (orbitalCount I + 1),
    z ^ (q : ℕ) • chargeSectorProjector I q := THEOREM_TO_PROVE
```

**Avoid a false shortcut:** `localCharge` is a local operator in the **full** ambient space. Even when its compressed image is meaningful, the algebra of separately compressed odd fields does not recover it.

### 4.3 Microscopic density primitive

```lean
-- PSEUDOCODE ONLY
-- Start with cumulative sums from a fixed base site;
-- establish their periodicity from sum_x deltaDensity x = 0.

def totalCharge : End ℂ FullFock := ∑ x : ZMod L, density x

def deltaDensity (x : ZMod L) : End ℂ FullFock :=
  density x - (1 / (L : ℂ)) • totalCharge

def densityPrimitive (x : ZMod L) : End ℂ FullFock :=
  cumulativeSumFromBasepoint deltaDensity x

theorem densityPrimitive_forwardDiff (x : ZMod L) :
  densityPrimitive (x + 1) - densityPrimitive x = deltaDensity x :=
  THEOREM_TO_PROVE

theorem intervalCharge_telescopes (I : OrientedInterval L) :
  localCharge I =
    ((I.length : ℂ) / (L : ℂ)) • totalCharge
    + densityPrimitive I.endPoint - densityPrimitive I.start :=
  THEOREM_TO_PROVE

-- Only later: define truncatedCurrentPrimitive M,
-- and its EXACT difference from densityPrimitive.
def intervalWrapAndTailResidual ... :=
  localCharge I - zeroModeContribution I
    - (truncatedCurrentPrimitive M I.endPoint
       - truncatedCurrentPrimitive M I.start)
```

**Type risks:** division by `L` requires `L ≠ 0`; intervals in `ZMod L` have no natural linear order, so encode orientation and length explicitly. Proofs involving the Nyquist mode require the project's existing centered-band conventions. Distinguish the operator-valued microscopic primitive from Ch15's chiral/dual oscillator phase names.

### 4.4 Rényi and charge-resolved observables

```lean
-- PSEUDOCODE ONLY
-- Local density operator from a CHOSEN graded spatial tensor equivalence.
def reducedState (factorization : FermionicSpatialFactorization I)
    (Γ : DensityMatrix FullFock) : DensityMatrix (LocalFock I) := ...

def renyiMoment (ρ : DensityMatrix (LocalFock I)) (n : ℕ) : ℂ :=
  trace (ρ ^ n)

def chargedMoment (ρ : DensityMatrix (LocalFock I))
    (n : ℕ) (z : ℂ) : ℂ :=
  trace ((ρ ^ n) * localChargePolynomial I z)

-- U acts cyclically on local subsystem factors of n replicas.
theorem replicaTraceIdentity (n : ℕ) (hn : 1 ≤ n) :
  renyiMoment (reducedState factorization Γ) n =
    trace ((tensorPower Γ n) * (localCyclicPermutation factorization n)) :=
  THEOREM_TO_PROVE

theorem chargedMoment_sectorExpansion
    (hInvariant : Commute ρ (localCharge I)) :
  chargedMoment ρ n z =
    ∑ q, z ^ q * trace ((sectorProjector q * ρ * sectorProjector q) ^ n) :=
  THEOREM_TO_PROVE
```

**Type risks:** traces and positivity are real/complex-valued in different conventions; `ρ^n` lies in the local endomorphism algebra; fermionic graded permutation operators must be constructed explicitly. Do not use `Matrix.log` in the first acceptance gates.

### 4.5 Invariants that the agent must NOT encode as unconditional axioms

```text
BAD:  omega_dressed : State (End ℂ BudgetSpace)
      -- without constructing the state there.
BAD:  compress (A*B) = compress A * compress B
BAD:  [compressedCurrent(-m),compressedCurrent(m)] = m * 1
BAD:  density(x) = forwardDifference(truncatedChiralField M x)
BAD:  all interacting states are CAR quasi-free
BAD:  symmetryResolvedMoment = coefficient(chargedMoment)
      -- without a charge-commutation hypothesis.
BAD:  formalVertex(t=1) is a unitary CAR field
      -- from coefficientwise formal power series alone.
BAD:  S_2(ρ)-S_2(σ) is a Rényi relative entropy.
```

---

## 5. Recommended development phases and acceptance gates

| Phase | Work product | Dependencies | Acceptance / refusal gate |
|---|---|---|---|
| **P0 — Repository truth audit** | Current inventory of Core/staging/proof runner, pinned Mathlib APIs, source hashes and a theorem provenance ledger | Repository access | **No implementation** until actual import paths, states, Fock carrier and statuses are confirmed. |
| **P1 — Semantic contract & notation** | Decision record on full-vs-even local algebra, finite physical state, interval representation, branch and charge conventions | P0 | Every proposed theorem states its carrier and quantifiers; no unproved bridge implicit. |
| **P2 — Charge foundation** | Oriented intervals, commuting local occupations, local charge projectors/polynomial, exact normalization of sector probabilities | Ch04–06 interfaces | `sorry`/axiom-free proof and independent L=4,6 witnesses; no fake green tests. |
| **P3 — State restriction / budget compression** | Positive state restriction; full-Fock vector/density states; compression defect and optional complete positivity | P0, P1, finite linear algebra | Explicit nonmultiplicative witness; no `StarAlgHom` for compression. |
| **P4 — Density primitive / boundary identity** | Periodic mean-zero primitive; zero-mode telescoping; exact current-tail/wrap residual | Ch01–03, Ch09, Ch15 | Identity includes \(\ell Q/L\); Fourier wrap term is accounted for. |
| **P5 — Replica and charged moments** | Partial trace or local algebra state, swap/cyclic identity, charge-resolved formulas with commutation hypothesis | P2–P3 | Traces agree on independent small cases; charge noninvariant counterexample included. |
| **P6 — Free-fermion benchmark** | Slater/quasi-free current matrix, purity/charged-moment comparison, optional determinant theorem | P5, validated quasi-free carrier | Independence from bosonic Ch19 Gaussian assumption is explicit. |
| **P7 — Research bridge, later sprint** | Protected current-word comparison and bounded/vanishing remainder theorems | Ch14, Ch18–20 promotion/proof ledger | Only proved finite-domain equalities; counterexamples and residuals retained. |
| **P8 — Modular/continuum, optional** | Relative modular operator and relative entropy under support hypotheses; coherent CCR-vs-CAR comparison; scaling limits | P7 and new analytic inputs | No statement of continuum type-III behavior, universal CFT entropy or finite interacting equality without proof. |

**Suggested immediate milestone:** P0 + P1 (agent planning), then P2 as the first narrowly scoped implementation. P3 and P4 can be parallel only after P1 has fixed the algebra and state carriers. P5 should not bypass these interfaces. P7–P8 should not block the useful exact finite-CAR results.

### Adversarial tests / minimal proof witnesses

1. **Compression failure:** fixed-number budget; \(Pc_xP=0\), but \(Pc_x^\dagger c_xP\neq0\) for a suitable state.
2. **Four-site Ch14 counterexamples:** reproduce the deep-hole and missing-mode failures *with their original target/source cutoffs*.
3. **Ch20 projection residual:** reproduce Eq. (20.40) for the distinct source/intermediate/target budgets; reject a blanket zero-residual lemma.
4. **Charge polynomial:** check \(z=1\) gives identity, \(z=0\) gives zero-occupancy projector, coefficients are mutually orthogonal; probabilities sum to one.
5. **Orientation/periodicity:** interval crossing the periodic seam telescopes correctly; \(\ell=L\) gives \(N_I=Q\) if explicitly supported, while the first proper-interval API uses \(\ell<L\).
6. **Zero mode:** sum of forward differences is zero and cannot equal \(n_x\) globally unless its total charge vanishes; ensure T4 contains \(Q/L\).
7. **Replica:** pure product state \(P_2=1\); maximally mixed local \(d\)-state has \(P_2=1/d\); Bell/occupation-entangled small example against explicit partial trace.
8. **Symmetry distinction:** definite-total-charge global state gives zero \(U(1)\) asymmetry but can have nontrivial local charge probabilities.
9. **Noninvariant counterexample:** construct \([\rho_I,N_I]\ne0\) and verify charged coefficients are not generally sector-block moments.
10. **Gaussian boundary:** Slater determinant matches the free correlation-matrix formula; an interacting bosonic oscillator Wick rule alone is **not** accepted as that proof.

**Execution integrity:** A pass requires an actual pinned-toolchain Lean run, a complete theorem statement, absence of `sorry`/`admit`/`by trivial` substitutions, and no unexpected axioms or hidden mock definitions in the imported proof closure. Numerical examples are independent diagnostic witnesses, not substitutions for formal proofs.

---

## 6. Research questions requiring new results (do not treat as implementation bugs)

1. **Interacting finite state:** Which finite CAR Hamiltonian and charge sector define \(\Gamma_F^{\mathrm{int}}\)? Is the intended target an exact ground state, Gibbs state, variational state, or a family of low-energy approximants? Finite ground-state existence is automatic for Hermitian matrices; agreement with \(\omega_P\) is not.
2. **State-preserving current bridge:** For which finite protected word family \(W\), basis isometry, and state pair can we prove \(\omega_F(\pi_F(w))=\omega_P(\pi_B(w))\) for every \(w\in W\)? What bounds the omitted words/modes?
3. **Boundary currents:** Can \(R_I^{(M)}\) be made to vanish on a precisely stated protected subspace, or only in selected matrix elements? Since a sharp interval includes high spatial Fourier components, low-energy input alone does not guarantee small \(R_I^{(M)}\).
4. **Coherent excitation:** Is the proposed \(V_\alpha\) a unitary in the **local physical algebra**, a global unitary, or only a formal series in the CCR model? Local unitaries preserve all local Rényi spectra of that region, even when relative entropy to the reference state is nonzero.
5. **Fermionic superselection:** Are entropies defined on full CAR fields, local parity-even observables, or \(U(1)\)-invariant observables? How should central charge-sector blocks be counted?
6. **Asymmetry choice:** If \(U(1)\)-invariant ground states are the reference, is the actual target charge resolution, or are coherent charge-breaking superpositions physically intended?
7. **Efficiency claim:** Which extra structure avoids exponential evaluation? Replica identities are algebraically exact but do not automatically yield polynomial-time algorithms. Quasi-free reductions or certified tensor-network structures can change the complexity.
8. **Scaling theorem:** If a continuum claim is desired, specify families \(L,M,K,a\), the limiting topology, and uniform error estimates. No finite exact identity alone establishes type-III entropy or CFT universal logarithms.

---

## 7. Antigravity planning-agent handoff prompt (copy the entire block)

> **Role:** Principal mathematical physicist and Lean 4/Mathlib architect. Work as an **adversarial planning and repository-audit agent** for the `bosonize-lean` entanglement extension. This is a **design-only task**. Do not create/edit Lean source, tests, shell scripts, CI or the monograph, and do not assert a theorem has compiled unless you have examined current build evidence. You may read the repository and existing logs; ask for explicit authorization before running anything that changes tracked files or frozen dependencies.
>
> **Project context:** The finite lattice is `ZMod L`, with `L = 2*h`, a centered Nyquist-asymmetric momentum band, multi-branch CAR Fock space and spatial local graded `StarSubalgebra` net. Energy budget operators act on global momentum/excitation-filtered subspaces. Ch19's interacting Gaussian state is an uncompressed oscillator-algebra functional `ω_P = ω_0 ∘ β⁻¹`, not an established state on the finite CAR/budget operator algebra. Ch14's projected vertex correspondence is conditional. Ch09 Fourier densities contain wrap terms; Ch15 gradients omit a charge zero mode; Ch20 formal vertices, finite CAR composites and projection residuals must remain distinct.
>
> **Primary input:** `Bosonize_Lean_Entanglement_Next_Phase_Review_and_Antigravity_Plan.md` (this packet) and the 2026-10-17 monograph `main(1).pdf`. Secondary input: the 2026-10-16 Ch19–20 strategy note, Ch19 Phase A/B design, and the current *live* repository. Historical notes never override current checked source.
>
> **Work sequence:**
>
> 1. Inventory the current Git revision, toolchain, pinned Mathlib version, imports, Core/staging boundaries, proof runner, test commands, outstanding merge/conflict state and affected module paths. Report exact source paths and declaration names; mark any inaccessible evidence as `UNKNOWN`, not `VERIFIED`.
> 2. Build a traceability matrix: monograph theorem/equation → currently declared Lean theorem → module and carrier → actual hypotheses → dependency closure → proof status (`M`, `D`, `S`, `V`, `P`). Explicitly investigate Ch06/07/09/14/15/18/19/20 and A08/Appendix E. Verify the claim that Ch19 is Phase-B complete but not Core promoted.
> 3. Check whether a canonical positive linear state, density matrix, subalgebra restriction, adjoint/compression, partial trace, finite tensor permutation, local occupancy projector, and `ZMod` oriented interval already exist. Use the *installed* Mathlib signatures, not guessed names. Do not introduce duplicate abstractions if suitable interfaces exist.
> 4. Critically review mathematical contracts T1–T6 in this packet. Find counterexamples, absent hypotheses, accidental use of non-multiplicative compression as an algebra map, failed graded signs, zero-mode/wrap omissions, wrong charge symmetry assumptions and false claims that bosonic Gaussianity implies CAR quasi-freeness.
> 5. Propose a minimal dependency DAG and module boundaries, respecting frozen Core and the project's current runner whitelist. Keep pure finite algebra separate from physical-state selection, budget compression, quasi-free specialization and CCR comparison.
> 6. Plan increments P0–P6 with one principal theorem family per independently verifiable sprint. For every sprint specify inputs, exact theorem contracts, assumptions, proof outline, Mathlib dependencies, explicit witness tests, expected blockers, acceptance gate and fallback if upstream proof APIs are unavailable.
> 7. Prepare an independent longer-term research backlog P7–P8: state-preserving CAR/CCR correspondence, protected-word and wrap-error estimates, coherent-state relative entropy, algebraic parity-sector entropy, possible continuum limits. Separate known mathematical facts, manuscript claims, open conjectures and numerical proposals.
> 8. Run a **red-team review** of the proposed architecture without implementing it. Include at least the fixed-charge compression counterexample, Ch14/20 counterexamples, the periodic zero-mode obstruction, a non-\(U(1)\)-invariant state sector-moment counterexample and a bosonic-vs-CAR Gaussian mismatch.
>
> **Non-negotiable constraints:** No `sorry`, `admit`, invented lemmas, fake green tests, hidden new axioms, `by trivial` substitutes, unproved promotion claims, global finite-dimensional CCR assertions, full interacting CAR/CCR equality inferred from two-point kernels, or assuming finite series evaluate analytically at `t=1`. Distinguish type I lattice entropy from type III continuum AQFT. Do not silently change sign, normalization, spin structure, Nyquist or multi-species conventions.
>
> **Required deliverables, all Markdown and planning-only:**
>
> - `00_current_state_audit.md`: current paths, source hashes, tested commands/results, Core/staging evidence and source/claim provenance. Use `UNKNOWN` where verification failed.
> - `01_architecture_decisions.md`: carrier and algebra map choices, full/even net decision, state choice, rejected alternatives, remaining questions.
> - `02_theorem_contracts.md`: typed Lean-style **pseudocode only** for the smallest P2–P5 interfaces, explicit assumptions, proof sketches and counterexample witnesses. These are not accepted Lean theorems.
> - `03_dependency_and_sprints.md`: prioritized module DAG, sprint gates, owners/parallelism only when dependency-safe, risks and rollback path.
> - `04_adversarial_review.md`: falsification attempts, mathematical errors found, resolutions and still-open obstructions.
> - `05_research_backlog.md`: literature tasks, exact references with verified metadata, expected new mathematics and preconditions for modular/continuum phases.
>
> **Final decision required from agent:** a single recommendation for the **first implementation sprint**, preferably local-charge generating polynomials on the full CAR net, with a concise list of exact declarations and proofs to implement **only after author approval**. If the source audit shows incompatible prerequisites, propose the minimum prerequisite repair instead and explain why.

### What the human should approve before authorizing implementation

- Choice of primary algebra: full local CAR net, even net, or both with distinct interfaces.
- Choice of first physical state carrier (full-Fock vector/density state), without identifying it with \(\omega_P\).
- Confirmed live module paths and promotion/dependency constraints.
- The P2 theorem list and explicit adversarial acceptance tests.
- Whether P3 budget positivity and P4 zero-mode primitive should precede or follow initial charged-moment demonstrations.

---

## 8. Verified research references and scope

Only published peer-reviewed articles are listed. These references motivate mathematical questions; none establishes that the corresponding `bosonize-lean` theorem has been formalized.

1. **H. Araki**, “Relative Entropy of States of von Neumann Algebras,” *Publications of the Research Institute for Mathematical Sciences* **11**, 809–833 (volume year sometimes indexed as 1975/1976). DOI: [10.2977/prims/1195191148](https://doi.org/10.2977/prims/1195191148). Relevant to relative modular operators, support and state restriction.
2. **H. Bostelmann, D. Cadamuro and S. Del Vecchio**, “Relative Entropy of Coherent States on General CCR Algebras,” *Communications in Mathematical Physics* **389**, 661–691 (2022). DOI: [10.1007/s00220-021-04249-x](https://doi.org/10.1007/s00220-021-04249-x). Relevant to coherent CCR relative entropy, **not** an automatic finite CAR statement.
3. **M. Goldstein and E. Sela**, “Symmetry-Resolved Entanglement in Many-Body Systems,” *Physical Review Letters* **120**, 200602 (2018). DOI: [10.1103/PhysRevLett.120.200602](https://doi.org/10.1103/PhysRevLett.120.200602). Relevant to charged moments and resolution by conserved charge.
4. **F. Ares, S. Murciano and P. Calabrese**, “Entanglement asymmetry as a probe of symmetry breaking,” *Nature Communications* **14**, 2036 (2023). DOI: [10.1038/s41467-023-37747-8](https://doi.org/10.1038/s41467-023-37747-8). Relevant to the distinction between sector resolution and broken-symmetry coherence.
5. **I. Peschel and V. Eisler**, “Reduced density matrices and entanglement entropy in free lattice models,” *Journal of Physics A: Mathematical and Theoretical* **42**, 504003 (2009). DOI: [10.1088/1751-8113/42/50/504003](https://doi.org/10.1088/1751-8113/42/50/504003). Relevant to free/quasi-free correlation-matrix benchmarks.

### Review stopping point

The current evidence supports a **planning decision** and a set of exact finite-mathematical theorem targets. It does **not** justify telling an implementation agent that Ch19/Ch20 are Core-certified, that the interacting Luttinger state has already been realized in the finite CAR net, or that finite-cutoff local charge equals a truncated chiral-field boundary difference without an explicit zero-mode and wrap/tail correction.

**Next action:** authorize **only the Antigravity P0/P1 repository and mathematical contract audit**. After its provenance ledger is reviewed, select and implement the smallest P2 charge-polynomial theorem family with an independent adversarial check.
