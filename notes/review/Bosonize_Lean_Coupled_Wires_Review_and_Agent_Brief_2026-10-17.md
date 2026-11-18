# Bosonize-Lean: Project-State Review and Next-Phase Research/Implementation Brief

**Date:** 17 October 2026  
**Audience:** Mathematical-physics lead, Lean 4/Mathlib architects, adversarial verification agents, Google Antigravity planning agent  
**Decision stage:** Architecture and proof planning; **no implementation authorized by this document**  
**Primary project record inspected:** `main(4).pdf`, *Constructive 1+1D Lattice Bosonization: Finite Constructions and Algebraic Models*, dated 17 October 2026, 239 PDF pages.

> **Evidence boundary.** This is a review of the supplied *manuscript*, not an independent verification of the repository. The Lean source tree, `lakefile`, dependency lock, compiler output, CI logs, and independent validation records were **not supplied**. Terms such as “Core verified” below mean **the manuscript reports that verification**, unless and until a repository audit reproduces it. Statements about the coupled-wire extension are mathematical proposals, not claims that these modules exist.

## 1. Decision summary

**Recommended next action:** run a read-only, evidence-based repository and manuscript status audit, then implement a small, purely algebraic finite **open alternating-chirality array** as the first coupled-wire research target. Do not start with QED\(_3\) gauge dynamics, continuum claims, or an unconditional finite-CAR bosonization isomorphism.

The first finite-wire milestone should certify all of the following:

1. An even-sized, ordered transverse wire type with an explicit cut; a signed chiral pairing and **integer** charge lattice.
2. The coupled-wire transformation \(D\), with \(D^2=I\), \(D^{\mathsf T}JD=-J\), its mod-2 charge parity properties, and the **failure of locality at the periodic seam**.
3. An explicit transported multi-wire fermionic cocycle, with convention-checked antisymmetry, associativity, and source/target charge maps.
4. Two-site locality of **adjacent transformed charge differences**, as a charge-lattice identity, before claiming locality of exponential operators.
5. A reusable *word-excursion/budget certificate* and projected-product residual theorem; no illicit exact CCR on a finite invariant space.

**Do not claim** at this milestone that there is a `StarAlgEquiv` between finite electron CAR and physical QED\(_3\), a globally unitary finite charge-lowering Klein factor, an exact compact exponential at a fixed truncation, an exact gauge constraint inherited from a path integral, or anomaly matching from fermion parity alone.

## 2. What the supplied monograph establishes—and what is actually evidenced

The project record is a mathematical manuscript with explicit claims of Lean promotion for selected items. It is **not** a complete machine-verification ledger. The proposed extension should preserve the manuscript's careful distinctions among ambient CAR operators, budget-projected maps, uncompressed oscillator algebras, formal vertex series, and continuum interpretations.

| Area | What the monograph says | Status to use in planning | Where to check |
|---|---|---|---|
| Spatial and momentum lattice, CAR, Fock net, budgets, current margins, Haldane basis, multispecies Klein maps | States exact finite constructions and, in several appendices, Lean verification claims | **Reported foundation; audit kernel artifacts** | Chapters 1–13, Appendices A–C |
| Schwinger term / Kac–Moody on low-energy states | Current commutator is valid on prescribed protected states, not as a global finite-matrix CCR | **Retain ambient/projected distinction** | Chapters 7, 9–11; Appendix A |
| Projected Mattis–Mandelstam dictionary | Conditional cyclic-span criterion is presented; unconditional field–vertex identification is **open** and counterexamples expose insufficient margins/mode coverage | **Open bridge; never silently promote** | Chapter 14, §§14.7–14.8; Appendix B.5 |
| Bogoliubov state and Wightman correlations | Chapter 19 says CH19/A08 Phase C was promoted and audited; carefully distinguishes abstract state from finite interacting ground state | **Reported verified, but documents conflict** | Chapter 19 end; Appendix E.1 |
| Projected CDW/SC products | Chapter 20.1 reports a promoted finite-CAR Core module, including a nonzero projection residual witness | **Reported partial Chapter 20 support** | §20.1, especially manuscript pp. 135–144 |
| Formal oscillator vertices, CDW↔SC model duality | §§20.2–20.3 explicitly describe manuscript drafts, not a completed Chapter 20 Lean formalization | **Unverified proposal** | §§20.2.8, 20.3.7; Appendix F |
| Spin/charge separation, Umklapp, Schrieffer–Wolff applications | Prior finite support lemmas are distinguished from integrated spinful development and physical spectral claims | **Partial support; composite theorems unverified** | Chapter 21 §§21.1, 21.4.7; Appendix G |
| Coupled-wire Dirac–QED\(_3\) extension | Not included as a formalized part of the supplied 1+1D monograph | **Research stage only** | This brief and peer-reviewed literature |

### 2.1 Specific inconsistencies to resolve before new code

- **CH19 promotion drift.** The chapter-end “Verification boundary” reports *CH19/A08 Phase C* promoted/audited in Core, while Appendix E.1 describes only a Phase-B staging state and says that is not Core promotion. Determine the actual Git commit, declarations, imports and validation evidence. Update the stale prose only after verifying.
- **Chapter 20 naming drift.** §20.1 says there is a promoted Chapter 20 Core module for finite products and residuals, but §20.3.7 says there is “no implemented Chapter 20 Lean module” certifying its duality statements. These can coexist if “Chapter 20 module” is scoped to §§20.2–20.3; make that explicit everywhere. Do not let an agent interpret the chapter as uniformly certified.
- **Appendix F status.** Its charge-reflection map and formal vertex exchange are marked *proposed*, not present in the Lean Core. Avoid treating earlier 1+1D CDW/SC duality as a ready-made `StarAlgEquiv` for coupled wires.
- **Manuscript proof ≠ kernel proof.** Generic remarks such as “the formal statement and proof” are insufficient evidence without exact Lean declaration names and an actual successful build. A mathematical counterexample or a theorem proof on paper is not a replacement for kernel evidence.

### 2.2 Already documented obstructions that must be inherited

**Finite CCR no-go.** If \(V\) is finite-dimensional over \(\mathbb C\), \(\operatorname{tr}[A,B]=0\). Thus \([A,B]=mI_V\) with \(m\neq0\) is impossible for globally preserving endomorphisms. Projected *ambient* relations may hold:

\[
P[A,B]P=[PAP,PBP]+PA(1-P)BP-PB(1-P)AP.
\]

A protected matrix-element/ambient-commutator identity is not a compressed CCR identity.

**Field–vertex bridge unresolved.** Chapter 14 provides a conditional cyclic-generator criterion, requires ground-vector matching, matching intermediate projection excursions and sufficient mode coverage, and explicitly does **not** establish unconditional \(P_{\rm out}c_xP_{\rm in}=B(x)\). Its \(L=12\), \(M=1\), \(K_{\rm out}=2\) example shows a missing-mode mismatch despite a margin bound. Never build dual-fermion CAR proofs by invoking this conjectured equality.

**Finite formal vertices are not exact fermion operators.** §20.2 notes a finite Fourier-sawtooth exchange-phase remainder. The uncompressed polynomial CCR carrier is infinite-dimensional even with finitely many oscillator modes; polynomial/formal series coefficients need not define convergent compact vertex operators on the finite CAR space.

**Finite charge shifts are typed maps.** §13 and Appendix B construct Klein maps between admissible sectors and budgets; finite total charge space has nonuniform sector dimensions. A globally unitary charge ladder is not available.

**Projected compositions carry residuals.** A finite CAR product compressed only at the ends is generally different from a product with an intermediate projection. This is central to the proposed multi-wire budget accounting.

## 3. Critical definition choices for the 2+1D extension

### 3.1 Geometry and model selection

Preserve the existing notation: **\(L=L_x=2h\) is the longitudinal lattice length**, and **\(L_y\)** is the transverse wire count; use **\(\nu\in\{\mathrm{pos},\mathrm{neg}\}\)** for branch/chirality. Never use `L` as a branch constructor.

The general reusable species type may be
\[
\sigma=\operatorname{ZMod}(L_y)\times\mathrm{Branch}.
\]
But the microscopic array in Mross–Alicea–Motrunich (2016) has one chiral mode of **alternating chirality on each wire**. Using *both* branches on *each* wire changes the microscopic model and may change its anomaly structure. Therefore distinguish:

- `WireSpecies`: the reusable full product type, suitable for existing multispecies CAR;
- `ActiveChiralSpecies`: a subtype or explicit active-channel embedding, alternating with representative parity;
- `WireModel`: the specification of active modes, signs, boundary conditions and couplings.

For a first theorem, require \(L_y=2M_y\) with \(M_y\ge 1\), use an **open ordered transverse array**, and keep the periodic closure as a separately proved extension. A cyclic `ZMod` type may be retained as a site label, but an order based on `ZMod.val` is a **chosen cut**, not a translation-invariant linear order.

### 3.2 Exact integer transformation for even open arrays

On wires \(y,z\in\{0,\ldots,L_y-1\}\), let
\[
J_{yz}=(-1)^y\delta_{yz},\qquad
D_{yz}=\begin{cases}0,&y=z,\\
\operatorname{sgn}(y-z)(-1)^z,&y\ne z.
\end{cases}
\]

For even \(L_y\), target the exact combinatorial identities
\[
D^2=I,\qquad D^{\mathsf T}JD=-J,\qquad D\mathbf 1=\mathbf 1,
\qquad D\in GL(L_y,\mathbb Z).
\]
The assertions above are **mathematical targets**: independently prove the formulas for all even sizes in Lean. Explicit integer-matrix evaluations for small sizes are only smoke tests, not proofs.

For internal neighbors \(0\le y<L_y-1\):
\[
D_{y+1,z}-D_{y,z}=(-1)^y(\delta_{z,y}-\delta_{z,y+1}).
\]
This is a strong locality lemma for transformed *charge combinations*. At the periodic seam \((L_y-1,0)\) an extensive string generally remains. Adding periodic transverse bonds therefore requires Wilson/holonomy or sector data; the open-chain proof cannot be silently reused at the seam.

**Important:** \(D^{\mathsf T}JD=-J\) reverses the chiral pairing. It does **not** alone construct a unitary on finite fermionic Fock space or an isomorphism preserving the same CAR representation. Specify the appropriate opposite/oriented current algebra if claiming an algebra map.

### 3.3 Integral charges, Klein factors and cocycles

Start with the integral lattice
\[
\Gamma=\mathbb Z^{\sigma},\quad e_a\in\Gamma,
\]
with an explicit total species order: first wire representative, then `Branch.pos < Branch.neg`. For an ordered charge lattice define a normalized \(\mathbb Z_2\)-valued 2-cocycle, for example
\[
\epsilon(q,r)=(-1)^{\sum_{a>b}q_a r_b}.
\]
Then certify
\[
\epsilon(q,r)\epsilon(q+r,s)
=\epsilon(r,s)\epsilon(q,r+s),\qquad
\epsilon(e_a,e_b)=-\epsilon(e_b,e_a)\;(a\ne b).
\]

**Sign convention is part of the theorem.** In the monograph the Klein factor is a *lowering* arrow with a source-action phase, so moving from the displayed cocycle to that exact kernel must include a declared sign/orientation convention. Do not silently replace the existing source/target order.

The transformed cocycle is obtained by **transport**:
\[
\epsilon_D(p,q)=\epsilon(D^{\mathsf T}p,D^{\mathsf T}q),
\]
not by assuming unchanged elementary Klein signs. Check parity, conjugation, source/target charge tracking and anticommutators of *admissible typed arrows*. Simple `Branch`-wise CAR does not automatically guarantee physical dual-fermion CAR if the vertex part has nontrivial exchange phases or a budget truncation.

### 3.4 Rational transverse kernels are not compact charge automorphisms

The transverse difference map \((\Delta_y f)_y=f_{y+1}-f_y\) has the uniform zero mode in its kernel on the periodic array. Its inverse requires a zero-mode choice and can involve rational coefficients. An operator in \(GL(n,\mathbb Q)\) is not automatically an automorphism of the **integer compact vertex charge lattice**. Treat the integral \(D\) transformation, the rational inverse-difference Green operator, and the exponent/vertex domain as different interfaces.

### 3.5 Gauge symmetry is not obtained for free

The emergent gauge variables of the field-theoretic wire derivation are auxiliary fields introduced to localize nonlocal interactions. A finite operator model with **exact Gauss law** requires a chosen gauge-link Hilbert space and representation. For an oriented finite graph, a representative algebraic Gauss constraint has the form
\[
G_v=(\operatorname{div}E)_v-n_v+b_v.
\]
Gauge-covariant hopping generally requires a link:
\[
T_{uv}=\widetilde\psi_u^\dagger U_{uv}\widetilde\psi_v,
\qquad [G_w,T_{uv}]=0.
\]
Undressed matter hopping is not usually gauge invariant. Nor is a gauge-charged dual fermion itself expected to commute with \(G_v\). Plaquette flux and gauge-invariant dressed matter operators require **separate** commutation theorems.

There is another finite-dimensional obstruction: **unitary** \(U\) and Hermitian \(E\) cannot satisfy \([E,U]=U\) on a nonzero finite-dimensional Hilbert space. Distinct choices are (a) a finite-dimensional **quantum-link** truncation with nonunitary raising links and exact infinitesimal Gauss commutators, or (b) a \(\mathbb Z_q\) clock gauge theory with exact finite Weyl relations but a different gauge group. Pick explicitly; neither is automatically noncompact QED\(_3\).

### 3.6 Global sectors and anomaly claims

Local cocycle and charge identities are not enough for global Dirac–QED\(_3\) duality. Introduce separately:

- longitudinal/tangential spin-structure or boundary-twist choices;
- transverse seam cut and Wilson holonomy;
- background electromagnetic flux and regulator/counterterm conventions;
- Gauss-law total-charge constraint on a torus;
- physical electric charge versus emergent gauge charge versus emergent magnetic flux.

For the even-array integer transformation, \(D\mathbf1=\mathbf1\) implies preservation of **the naive sum-of-wire integer charge** (and therefore its parity) when charges are related by \(N=D^{\mathsf T}\widetilde N\). This does **not** by itself establish the physical charge assignment of QED\(_3\) dual fermions, or parity-anomaly matching. The continuum anomaly question involves background gauge invariance, spin/`spin_c` structure, antiunitary symmetry and possible bulk inflow. Treat these as later regulator-level questions, not first-milestone theorems.

## 4. Generalized finite-budget contract

The 1D baseline uses margins such as \(2K+|N_\nu|\le h\) for partition/Klein bases and \(2M+K+|N_\nu|\le h\) for specified current words. A multi-wire interaction changes individual charges and may make intermediate states leave a budget even if initial and final states are admissible.

A proof-relevant operator word
\[
W=O_r\cdots O_1
\]
should carry **explicit, compositional metadata**:

1. source and target charge vectors; \(\Delta N(O_j)\in\Gamma\);
2. prefix charge excursions \(\Delta N^{(j)}=\sum_{i\le j}\Delta N(O_i)\);
3. longitudinal momentum support \(m(W)\) of each constituent;
4. a certified upper bound on excitation cost at each prefix, \(\Delta K_a^{(j)}\);
5. the allowed source, intermediate and target budget projectors.

A **sufficient** frozen-margin certificate for every species \(a\) has the form
\[
m(W)+K_a+\max_j\Delta K_a^{(j)}+
\max_j|N_a+\Delta N^{(j)}_a|\le h.
\]
The actual inequality depends on the precise definition of \(K_a\), the word's action, and the monograph's current-margin convention. Do not instantiate it blindly: the agent must derive the bound from a support lemma and compare it with existing `BudgetSpace` semantics. For an inter-wire hopping \(a_y^\dagger a_{y+1}\), the net charge transfer is supported on two wires, but a momentum-unrestricted hopping need not have a bounded **low-energy excitation cost** merely because its charge transfer is small.

Primary generic projection theorem:
\[
P_{\rm out}ABP_{\rm in}
=P_{\rm out}AP_{\rm mid}BP_{\rm in}
+P_{\rm out}A(I-P_{\rm mid})BP_{\rm in}.
\]
Promote a reusable typed residual, rather than defining the wrong middle-projected product as the physical product.

### Admissible observables by increasing difficulty

1. Integral charge-lattice maps and current bilinears.
2. Local **gauge-neutral** adjacent hopping combinations, with protected matrix elements.
3. Nonlocal single dual-vertex arrows with broad transverse charge support.
4. Gauge-covariant dressed operators in a separately specified gauge extension.
5. Periodic global flux-changing operators and continuum interpretation.

Each level should have a declared carrier and theorem scope. The nonlocal individual dual vertex may require a more restrictive domain than a local adjacent dual hopping product.

## 5. Proposed categorical interfaces (schematic Lean pseudocode)

**Warning:** This is non-executable Lean-style pseudocode, *not* an assertion that the identifiers shown already exist in Mathlib or the project. Use the project's pinned Lean/Mathlib version to choose actual names and instance constraints. These sketches show object boundaries and theorem contracts, not compilable files.

### 5.1 Pure geometric layer

```lean
-- SCHEMATIC ONLY; DO NOT PASTE AS A COMPILABLE MODULE.
inductive Branch
  | pos | neg

structure WireGeometry where
  L : Nat                 -- existing longitudinal length, never chirality
  h : Nat
  Ly : Nat
  longitudinal_even : L = 2 * h
  transverse_even : ∃ My, Ly = 2 * My
  transverse_nonzero : 0 < Ly

Wire g := ZMod g.Ly
Species g := Wire g × Branch
ActiveSpecies g := {a : Species g // alternatingChirality g a}

orderedWire : Wire g → Fin g.Ly        -- chosen canonical representative/cut
chirality : ActiveSpecies g → ℤ     -- ±1 (model-dependent)
```

**Proof obligations:** the parity predicate is well-defined on the chosen representatives; the active set has exactly one branch per wire; the total order is explicitly chosen; internal neighbors are distinguished from the periodic seam; degenerate lengths are ruled out or handled.

### 5.2 Integer linear map and pairing

```lean
Charge g := ActiveSpecies g → ℤ
Pairing g : Charge g → Charge g → ℤ
D : Charge g ≃ₗ[ℤ] Charge g              -- AFTER bijectivity proof

theorem duality_involution : D.comp D = LinearEquiv.refl ℤ (Charge g)
theorem duality_chiral_form :
  Pairing g (D q) (D r) = -Pairing g q r
theorem adjacent_difference_local :
  row D (y + 1) - row D y = signedUnitDifference y
theorem periodic_seam_requires_dressing :
  seamDifference D = explicitStringCharge g
```

**Dependency correction:** first define \(D\) as an integer `LinearMap` / matrix, prove \(D^2=I\), *then* promote it to an equivalence. Avoid defining an equivalence with an unproved inverse.

### 5.3 Cocycles and finite charge arrows

```lean
structure ChargeCocycle (Γ : Type) where
  epsilon : Γ → Γ → Sign
  normalized_left  : ∀ q, epsilon 0 q = 1
  normalized_right : ∀ q, epsilon q 0 = 1
  cocycle : ∀ q r s,
    epsilon q r * epsilon (q + r) s =
      epsilon r s * epsilon q (r + s)

transportCocycle : ChargeCocycle Γ → (Γ ≃+ Γ) → ChargeCocycle Γ

structure BudgetArrow (source target : BudgetCarrier) where
  map : source.space →ₗ[ℂ] target.space
  charge_delta : Charge
  admissibility : BudgetAdmissibility source target charge_delta

-- Theorems must compose explicitly typed arrows, including parity signs.
-- No global unitary charge-ladder axiom.
```

**Proof obligations:** convention matching to Chapter 13 lowering arrows, cocycle associativity, sign under target/source swap, cross-wire fermionic exchange on admissible carriers, adjoints between reversed carriers, counterexample at exhausted charges.

### 5.4 Ambient operators and excursions

```lean
structure OperatorWord (ambient : Type) where
  factors : List (ambient →ₗ[ℂ] ambient)
  deltaCharge : List Charge
  energyCostBound : Prefix → Species → Nat
  modeSupportBound : Nat

protectedWord : OperatorWord H → BudgetSpec → Prop
projectedWord : OperatorWord H → BudgetSpec → TypedArrow

-- Target: projected ambient products = middle-compressed products + excursion.
theorem projection_residual :
  Pout * A * B * Pin =
    Pout * A * Pmid * B * Pin +
    Pout * A * (1 - Pmid) * B * Pin
```

**Type warning:** use the actual ambient endomorphism type and lifted projectors to avoid mixing `Submodule` maps and global `LinearMap`s. Word metadata must be certified from the factors; an unverified user-provided `energyCostBound` is not a proof.

### 5.5 Gauge extension—**research gate, not immediately implement**

```lean
structure FiniteGaugeModel where
  sites : Type
  links : Type
  matter : HilbertCarrier
  gaugeLinks : HilbertCarrier
  E : links → SelfAdjointOperator gaugeLinks
  U : links → LinearOperator gaugeLinks
  gauss : sites → LinearOperator totalHilbert
  physical : Submodule ℂ totalHilbert

-- Schematically:
theorem gauge_covariant_hopping (u v : sites) :
  commutator (gauss w) (matterCreate u * link U (u,v) * matterDestroy v) = 0
```

Do **not** place `U` and `E` in this structure with incompatible finite-dimensional axioms (`U` unitary and `[E,U]=U`). Decide quantum-link versus finite clock model first. The Gauss constraint and physical-sector dimension count must be proved independently of the original free-wire algebra.

## 6. Roadmap: small milestones and proof gates

| Phase | Goal | Concrete artifacts | Exit gate |
|---|---|---|---|
| **0 — Evidence and architecture audit** | Establish what the repository **really** proves, resolve manuscript drift | `STATUS_LEDGER.md`, `DECLARATION_INDEX.md`, `ASSUMPTION_REGISTER.md`, `ADR-0001-WireModel.md`, and source-to-claim map | Clean build under locked dependencies; machine-checked declarations or explicitly marked gaps; reviewer signs off on model choice |
| **1 — Finite wire charge geometry** | Ordered even open array and exact signed integer transformation | `WireGeometry`, `ChargeLattice`, `ChiralMatrix` modules (names provisional), proofs of \(D^2\), pairing reversal, charge parity, adjacent locality and seam obstruction | Generic even-size theorem, not just enumerated matrices; small \(L_y=2,4,6\) tests as witnesses |
| **2 — Transported cocycle / typed vertices** | Charge-lattice cocycle, transported sign, finite target-sector arrows | `ChargeCocycle`, `DualKlein`, `VertexDomain` specs | Cross-wire exchange proof with explicit sign convention; boundary tests; no reliance on an unproved full Mattis–Mandelstam identity |
| **3 — Budgets and interacting words** | Explicit prefix excursions, support bounds and projection remainders | `BudgetExcursion`, `ProjectedWords`, `InterWireHopping` | Certified intermediate margins, non-vacuity examples, open/seam comparison, counterexamples when hypotheses are removed |
| **4 — Finite gauge construction (optional decision)** | Choose regulator and introduce exact Gauss constraints | ADR for quantum-link vs \(\mathbb Z_q\); `GaugeLinks`, `Gauss`, `PhysicalSpace` | Gauge-invariant dressed hopping and plaquette proofs; nontrivial physical space; global Gauss constraint and dimension analysis |
| **5 — Global sector and anomaly research** | Finite parity, twists, seam holonomy and flux-sector maps | `SpinStructure`, `HolonomySector`, `ParityMap`; research note on regulator anomaly | Explicit sector map and hypotheses; no continuum anomaly claim from parity alone |
| **6 — Continuum/observable research** | Decide what can be shown beyond exact finite algebra | observable-to-operator contract, numerical experiments, scaling/continuum conjecture ledger | Every claimed limit has a topology, family of embeddings, a bound, and a statement distinguishing theorem/numerics/heuristic |

**Dependency order:** Phase 0 → Phase 1 → Phase 2 → Phase 3. Phase 4 requires a separate architecture decision after Phase 2; it should not block the exact integral charge/cocycle research. Phases 5–6 are conditional on the earlier proof gates.

### 6.1 Deliberately excluded from the first sprint

- Redesigning the existing 1D CAR representation without evidence of a deficiency.
- Writing a large monolithic coupled-wire/QED\(_3\) Lean file.
- Deriving a Chern–Simons gauge action from a finite regulator by verbal analogy.
- Calling a finite clock model noncompact U(1) or calling an arbitrary quantum link QED\(_3\).
- Equating all formal vertices with bounded finite fermionic fields.
- Claiming a continuum scaling dimension or physical gap from a handful of finite matrices.
- Claiming parity anomaly matching on the basis of \((-1)^F\) alone.

## 7. Verification discipline and adversarial tests

**Every claimed milestone must provide:** declaration name; actual file path; imports; Lean and Mathlib commit identifiers; exact theorem statement and hypotheses; a `lake`/kernel verification log; proof dependencies; at least one nonzero/nontrivial witness; and a separate negative test or counterexample when applicable.

The verification agent must search for: `sorry`, `admit`, `axiom`, vacuous `False` hypotheses, inconsistent instances, hypotheses reproducing the desired conclusion, fake/mock implementations, self-referential test lemmas, trivial `True` smoke tests, hidden `noncomputable` assumptions where constructive evaluation is promised, and opaque wrappers around unverified lemmas. `by decide` on a fixed \(L_y\) does not establish a theorem for arbitrary even \(L_y\).

### Falsification tasks (do not omit)

1. **Odd transverse size:** show that the even-wire involution does not silently generalize without additional hypotheses. Explicitly report what fails.
2. **Periodic seam:** demonstrate that the internal adjacent-locality lemma is not being falsely applied across the cut.
3. **Cocycle reversal:** exchange two distinct wires and verify \(-1\) with the chosen lowering/raising convention; check three-charge associativity.
4. **Finite-dimensional CCR:** try to assert \([A,B]=I\) for a nonzero finite invariant carrier; ensure the proof cannot pass.
5. **Budget leakage:** construct a nonzero intermediate-excursion residual, and a word whose initial and final sectors satisfy margins while a prefix does not.
6. **Gauge noninvariance:** distinguish bare matter hopping from link-dressed hopping under the declared Gauss generator.
7. **Physical-sector non-vacuity:** show at least one explicit state solves the constraints; count sectors in a small gauge graph.
8. **Wrong regulator equivalence:** make the specification explicitly reject identification of a finite \(\mathbb Z_q\) clock model with exact noncompact U(1) QED\(_3\).
9. **Monograph status drift:** compare the CH19 Phase-C statement to Appendix E Phase-B text and §20.1 promotion to §20.3.7 draft; do not mark “resolved” without source inspection.

### Proposed agent roles

- **Project auditor (read-only):** repository inventory, statement-to-declaration provenance, version pin, build reproduction.
- **Mathematical architect:** defines objects, theorem boundaries, hypotheses and categorical maps; owns ADRs.
- **Physics derivation auditor:** independently rederives \(D\), chiral pairing, charge assignments, global sectors and gauge-convention signs.
- **Lean API investigator:** verifies Mathlib declarations against the *pinned* project dependency; proposes imports and minimal interfaces without implementing unapproved modules.
- **Adversarial verifier:** searches for vacuity, hidden invariance/continuum assumptions, false identifications and counterexamples.
- **Documentation integrator:** updates internal status references only after evidence-gated acceptance.

Agents should not independently change foundational signs, Fourier orientation, cutoff semantics, or branch names. Every such change requires an explicit interface decision and regression impact report.

## 8. Architecture decisions requiring human sign-off

Write these as short ADRs, with accepted/rejected alternatives, rationale, consequences, and testable obligations.

1. **Physical model:** alternating single-chiral wire versus two active branches per wire. Suggested initial choice: alternating active subtype over a reusable full species type.
2. **Transverse topology:** even open ordered array as theorem core versus periodic array with seam/holonomy from the start. Suggested first milestone: open ordered array with explicit future seam extension.
3. **Dual operator scope:** exact integral charge-lattice map, typed finite-budget dual vertex, or actual Hilbert-space unitary equivalence. Suggested initial claim: charge/cocycle map plus controlled projected identities.
4. **Gauge regulator:** quantum-link, \(\mathbb Z_q\), or no independent gauge Hilbert space. Suggested initial choice: postpone until exact operator-duality milestones are proved.
5. **First physical observable:** local dual hopping/current correlator, parity-sector map, or vortex sector-changing amplitude. Suggested first: local adjacent hopping and its budget residual, followed by global parity and seam sectors.

## 9. Standalone Google Antigravity agent prompt

Copy the following block as a **planning-only task**. Attach this review and the monograph PDF; provide repository access separately. The prompt is written so the agent must obtain the real code state rather than assume the manuscript's promotion claims are already verified.

```text
ROLE
You are the principal Lean 4/Mathlib mathematical-physics architect and independent
formal-verification auditor for the Bosonize-Lean project. Your task is to ORGANIZE,
RESEARCH, and PRODUCE A STRATEGY PLAN, not to implement code in this round.

INPUTS
1. Attached 239-page manuscript: "Constructive 1+1D Lattice Bosonization:
   Finite Constructions and Algebraic Models" (17 October 2026).
2. Attached review: "Bosonize-Lean: Project-State Review and Next-Phase
   Research/Implementation Brief" (17 October 2026).
3. Read-only access to the actual Bosonize-Lean repository. If repository
   access is absent, declare code verification unavailable; do not fabricate paths,
   theorem names, imports, or build results.

STRICT RULES
- PLANNING ONLY: do not edit source, write executable Lean modules, restructure
  directories, commit, or push. Lean-like statements in your deliverables are
  explicitly labeled PSEUDOCODE.
- Separate (A) formal kernel proofs; (B) mathematics proved only on paper;
  (C) computed finite examples; (D) conditional theorems; (E) open conjectures;
  (F) continuum and effective-theory heuristics.
- Never call a theorem "verified" without an exact declaration path, hypotheses,
  dependency version, and reproducible kernel check. A test succeeding under
  `sorry`, `axiom`, mock definitions, vacuous assumptions or `by trivial` is not
  evidence of the intended mathematics.
- Preserve L as the longitudinal lattice length; use Ly for transverse wire
  count; use Branch.pos / Branch.neg (or equivalent signed indicator) for chirality.
- Keep the existing Fourier, sea-subtraction, Jordan-Wigner ordering, charge-shift
  orientation, budget, and Hilbert-inner-product conventions. Report conflicts;
  do not silently change conventions.
- Favor pure generic interfaces: Types/Subtypes, LinearMap, LinearEquiv,
  AlgHom/AlgEquiv and StarAlgEquiv only when their actual hypotheses are proved.
- Reference only verified peer-reviewed articles/books for physics claims.
  Check authors, title, venue, volume, year and DOI. Use current project-pinned
  Mathlib documentation to validate API suggestions.

WORK PACKAGE 0: FORENSIC STATUS AUDIT
1. Inspect repository tree, lean-toolchain, lakefile/Manifest and CI configuration.
2. Enumerate relevant declarations and import dependencies from 1D CAR, budgets,
   currents, Haldane completeness, Klein factors, Ch14 dictionary, Ch19/A08,
   Ch20.1, Ch20.2/20.3, Chapter 21 and Appendices E/F/G.
3. Reproduce any existing build and test result; distinguish what was actually
   run from what is merely reported in manuscript notes.
4. Explicitly reconcile:
   - Chapter 19 "Phase C promoted" versus Appendix E.1 "Phase B only";
   - Chapter 20.1 promoted finite-CAR residuals versus Chapter 20.2/20.3 drafts;
   - Chapter 14 unconditional field–vertex identity marked OPEN;
   - Appendix F algebraic charge duality marked PROPOSED;
   - Chapter 21 integrated statements not fully Lean verified.
5. Produce a source-to-theorem ledger with provenance and confidence.

WORK PACKAGE 1: MATHEMATICAL AUDIT BEFORE DESIGN
1. Distinguish one alternating chiral mode per wire from two active branches
   on each wire. Identify anomaly and doubling consequences.
2. Fix even Ly and an ordered transverse cut. Check for all even Ly:
      D_yz = 0 (y=z), sign(y-z)*(-1)^z (y≠z),
      J_yy = (-1)^y,
      D^2 = I, D^T J D = -J, D*1 = 1,
      D_(y+1),z - D_y,z = (-1)^y (δ_yz - δ_(y+1),z)
   for interior neighbors, and explicitly identify the nonlocal seam term.
3. Construct the integral charge lattice and signed cocycle; prove the
   cocycle law and transformed cross-wire fermionic sign. Check the exact
   source-action lowering convention inherited from Chapter 13.
4. Audit compact vertex integrality, rational inverse transverse differences,
   transverse zero mode, Klein charge bounds and finite vertex exchange phases.
5. Identify precisely what has an ambient-operator statement, a protected
   matrix-element statement, a projected-budget statement, or a formal series
   statement. Use the finite trace no-go to reject a global finite CCR.
6. Do not infer a gauge Hilbert space or Gauss law from an auxiliary path
   integral. Propose regulator alternatives and their different theorem targets.

WORK PACKAGE 2: IMPLEMENTATION DESIGN, WITHOUT IMPLEMENTING
1. Recommend the smallest 4–6 modules, their imports and *pure interfaces*.
2. Provide Lean-style NON-COMPILING pseudocode for each interface and theorem.
3. Build a theorem dependency DAG and write acceptance tests and counterexamples.
4. Define a typed budget-arrow and compositional intermediate-excursion record.
5. Separate periodic seam/holonomy from the open-array theorem.
6. Plan a later gauge module only after an ADR chooses quantum-link or clock
   variables and a physical constraint space.
7. Propose a way to reuse established 1D declarations rather than rewriting
   them. Identify necessary adapter lemmas and any API friction.

WORK PACKAGE 3: RESEARCH PLAN
1. Prioritize exact finite operator observables (hopping, currents, parity,
   charge transfers) before vortex/monopole and continuum scaling claims.
2. Specify the physical electric-charge/emergent-charge/flux conventions.
3. Specify global spin structure, boundary twist and torus Gauss-law issues.
4. Give an explicit, falsifiable theorem/conjecture/limiting-hypothesis ledger.
5. Recommend which open questions require new literature checking and which
   can be settled by finite combinatorial proof.

MANDATORY OUTPUTS (Markdown, no source edits)
A. PROJECT_STATUS_LEDGER.md — source/declaration evidence, gaps, contradictions.
B. ARCHITECTURE_DECISIONS.md — model, topology, gauge-regulator alternatives.
C. COUPLED_WIRE_MATH_SPEC.md — definitions, conventions, exact theorem targets,
   counterexamples, references and scope limits.
D. LEAN_MODULE_PLAN.md — 4–6 narrow modules, imports, interface pseudocode,
   dependency DAG, risks and proof gates.
E. VERIFICATION_MATRIX.md — positive/non-vacuous witnesses, negative tests,
   boundary sector and false-green tests.
F. RESEARCH_BACKLOG.md — ordered research hypotheses and observables, with
   explicit distinction between theorem, calculation, numerical test and conjecture.
G. EXECUTIVE_DECISION.md — no more than two pages, listing unresolved human
   decisions and the smallest defensible next coding task.

STOP CONDITIONS
- If the actual repository cannot be accessed, stop any claim of code verification;
  deliver a manuscript-only provisional plan and an evidence-request list.
- If a proposed statement contradicts the finite trace obstruction, an existing
  Chapter 14 counterexample, the finite-charge unitary no-go, or periodic seam
  locality, classify it as INVALID and propose a weaker correct statement.
- If an API is uncertain under the pinned Mathlib version, label it UNKNOWN;
  propose how to inspect rather than inventing a declaration.
- Do not begin implementation before the human approves ADRs and proof contracts.

SUCCESS CRITERION
A different Lean agent can start the first approved module from your plan without
having to invent mathematical assumptions, change naming conventions, or accept
unverified equivalences. Every theorem has a carrier, quantified hypotheses,
conclusion, dependencies, negative tests, and verification status.
```

## 10. Source map and references

### Manuscript reading map (printed page numbers, not PDF viewer indices)

- **Chapters 7–11 (pp. 42–76):** budget, word excursions, protected Schwinger term and Haldane basis.
- **Chapter 13 (pp. 83–89) and Appendix B (pp. 202–208):** ordered multispecies CAR, typed Klein lowering, finite Taylor/truncation limits.
- **Chapter 14 (pp. 90–95):** conditional cyclic criterion, missing-mode/deep-hole counterexamples and open full field–vertex correspondence.
- **Chapter 19 (pp. 121–133):** abstract positive state, finite-state comparison, claimed Phase-C status.
- **Chapter 20 (pp. 135–164):** verified-claimed 20.1 support versus explicitly draft 20.2–20.3.
- **Chapter 21 (pp. 165–194):** spinful margins, effective Hamiltonian support versus unverified integrated physical conclusions.
- **Appendix E (pp. 218–220):** outdated/conflicting CH19 promotion status; **Appendix F (p. 221):** proposed algebraic charge-lattice duality; **Appendix G (pp. 222–228):** finite shell reduction and counterexamples.

### Verified peer-reviewed physics references

1. David F. Mross, Jason Alicea, and Olexei I. Motrunich, “Explicit Derivation of Duality between a Free Dirac Cone and Quantum Electrodynamics in (2+1) Dimensions,” *Physical Review Letters* **117**, 016802 (2016). DOI: https://doi.org/10.1103/PhysRevLett.117.016802. **This is the correct journal citation for arXiv:1510.08455; it is not PRX 6, 041017.**
2. David F. Mross, Jason Alicea, and Olexei I. Motrunich, “Symmetry and Duality in Bosonization of Two-Dimensional Dirac Fermions,” *Physical Review X* **7**, 041016 (2017). DOI: https://doi.org/10.1103/PhysRevX.7.041016.
3. Nathan Seiberg, T. Senthil, Chong Wang, and Edward Witten, “A Duality Web in 2+1 Dimensions and Condensed Matter Physics,” *Annals of Physics* **374**, 395–433 (2016). DOI: https://doi.org/10.1016/j.aop.2016.08.007.
4. Shailesh Chandrasekharan and Uwe-Jens Wiese, “Quantum Link Models: A Discrete Approach to Gauge Theories,” *Nuclear Physics B* **492**, 455–471 (1997). DOI: https://doi.org/10.1016/S0550-3213(97)80041-7.

### Final recommendation

**Authorize Phase 0 (read-only provenance and status audit) first.** Once the actual Lean proof surface is known, approve an ADR specifying the alternating even open array and exact integer charge-lattice transformation. The smallest new proof should be the \(D\) matrix and its chiral-pairing/locality identities. This gives an independently verifiable foundation for the transported cocycle and multi-wire budget semantics, without relying on the unresolved 1D physical field–vertex equality or presupposing a finite QED\(_3\) gauge construction.
