# Audit of all 21 reference notes for Lean implementation

Date: 2026-10-08. Baseline Core checkpoint: `299cfccab24024dcf27eb08ae7a77f4f25f3cd99`.

All 21 numbered Markdown files in `notes/md`, the master TOC, and `docs/stub_suggestion/chapter_3_fourier_stub_draft.md` were read in full. This is a mathematical/interface audit before the next chapter, not chapter 3 Phase A. Chapters 4–21 and the chapter 3 suggestion were already untracked when this audit began. The original files and the frozen Core modules were not edited. The read-source inventory records their hashes.

## Decision before chapter 3

Use the suggestion's two-step Fourier strategy, with corrected assumptions and an existing-library reuse check. Prove character identities and unscaled inversion first, then isolate the single real normalization scalar 1/√L in the complex Hilbert layer. The approach is sound and efficient; avoiding square roots everywhere would complicate the physical CAR interface unnecessarily.

For the immediate ℂ implementation, adapting installed `ZMod.dft` and transporting its codomain to the centered band may be cheaper than rebuilding its inverse. Retain a separate field/domain layer only if arbitrary roots or scalar fields are a concrete requirement. Appendix A01 gives the proposed contracts and supporting lemma order. This is a design recommendation, not a claimed compile-tested chapter implementation.

The supplied generic commutative-ring architecture is false as stated even when L is invertible: ζ=4 in Z/15 is a primitive second root, 2 is a unit, and 1+ζ=5≠0. The saved Lean probe proves this. Negative integer powers also need more structure than a bare commutative ring. The suggested half-power Laplacian identity is both underspecified and sign incorrect. The asymmetric 1/L inverse normalization is legitimate algebraically; it becomes unsuitable only if used as the same-counting-inner-product unitary CAR basis change without compensating structure.

## How to read the findings

**Blocker** means a statement is false as written, a construction is undefined on its declared carrier, or a global/restricted claim has incompatible types. **Gap** means the intended result may be correct but a definition, proof decomposition, or hypothesis is missing. **Design** identifies a maintainability or efficiency decision. Counterexamples and direct algebraic deductions are distinguished from proposals requiring further proof.

## Coverage of every chapter

| Chapter | Assessment and implementation concerns | Proposed appendix |
| --- | --- | --- |
| 1 | Core is already proved/frozen. Preserve positive Nyquist endpoint; distinguish integer representatives from residue-group arithmetic. “Symmetric sea” must not change `[-h+1,h]`. | A01, A03 |
| 2 | Core is already proved/frozen. Polynomial intertwining and finite-matrix trace obstruction are sound. Its scalar `CommRing` forward difference cannot be directly instantiated with a noncommutative endomorphism algebra later. | A06 |
| 3 | Sound finite Fourier goal; choose explicit positive length, character representative laws, scalar cancellation, adjoints, and normalized Euclidean carriers. Suggestion has ring and dispersion errors. | A01 |
| 4 | Concrete CAR is feasible; needs basis extension, atomic sign arithmetic, proof of CAR/adjointness, one Hilbert carrier, and ordered products for parity. | A02 |
| 5 | DFT CAR and number invariance are sound with the unitary normalization. Bare H₀ has a nonzero vacuum constant; keep it separate from normal-ordered energy. | A01, A04 |
| 6 | Constructive local net feasible. Odd part is a subspace; graded locality requires homogeneous-word reasoning. Global matrix-unit construction needs ordered signs and star closure. | A02 |
| 7 | Rank and frozen-margin claims plausible; supply exact integer triangular energy, empty-sector cases, sorted-index/reindexing lemmas, and nondecreasing displacement proof. Define fixed-charge vs charge-box budgets separately. | A03 |
| 8 | Ambient polynomial CCR feasible. Creation exponentials not defined on polynomials; compressed BCH has boundary terms; normal-ordering carrier is wrong; dagger/current inner product and broad Heisenberg no-go wording need correction. | A02, A03, A05 |
| 9 | Nonwrapping density construction feasible. Typed valid pairs avoid subtype friction; bare-vacuum eigenvalue in LI sketch is wrong; negative output budgets need cases; nonzero vacuum norms should precede LI. | A03, A04 |
| 10 | Finite edge formulas and M1/M2 program plausible. Prove exact edge-hop support before the budget theorem. Restricted CCR is an ambient action statement, not a global finite-subspace representation. K=0 witnesses are dimension one. | A03, A04 |
| 11 | Requires an actual configuration↔rectangle-partition bijection, word order independence, all intermediate margins, and Gram induction. Suggested `Multiset.prod` does not apply to arbitrary endomorphisms. | A04 |
| 12 | Sugawara equivalence has a credible partition-basis route, but its all-n commutator lemma is false under input-only R2; h−1 is not all valid modes. Separate equivalence proof from the corrected commutator corollary. | A04 |
| 13 | Haldane basis is only a budget basis. Adjacent-sector maps need both sectors' regimes; global density commutation/Clifford claims do not follow. Fix occupation-vs-relative-charge phases and explicit ambient extension. | A02, A05 |
| 14 | Major blockers: unprojected raising nilpotency and unprojected vertex equality fail at K=0; zero mode is antiperiodic despite periodic fermions; adjoint signs are wrong; adjoints and CAR do not follow from input-only equality. | A03, A05 |
| 15 | Major blockers: identical chiral signs give the wrong φ/θ bracket pattern; exact gradient has missing i/minus; finite difference cannot cancel 1/m; periodic derivative kernel must have zero mean; coincident sine quotient and kernel naming need repair. | A06 |
| 16 | Exact weighted-energy idea is useful, but scalar factor bookkeeping misses a mixed-square contribution. Error normalization, ground-state kernel, cyclotomic-vs-π scalars, and finite identity vs Taylor/RG statements need separation. | A06 |
| 17 | Transfer-domain/filtering and fermionic normal ordering unspecified. Species bilinears commute, fermions do not. Ground-energy shift contradicts ch12 unless chemical potential changes. Written g₂ hopping form differs from the pairing form needed in ch18. | A07 |
| 18 | Hyperbolic scalar package is useful. Requires the correct pairing Hamiltonian, real/star-compatible parameters, positivity, sign choice, and vacuum constant. Linear inverse does not produce a global algebra equivalence or dressed-vacuum existence. | A07, A08 |
| 19 | State existence/positivity cannot be replaced by rewrite assumptions on a finite compressed algebra. Missing opposite-ordered contraction makes its spatial correlator zero in the free case incorrectly. Power law needs an analytic contract. | A08 |
| 20 | D₁, exact prefactors, vertex exponential carrier, and duality map are unspecified. Restricted equalities cannot be multiplied freely. Fixed-budget `AlgEquiv` and topological interpretation require mapped charge/zero-mode domains. | A05, A08, A09 |
| 21 | Raw spin/charge currents avoid √2 until normalization. Edge cancellation is restricted, charge lattice has parity constraints, and fixed total budget is not a full tensor product. Umklapp per-species shift is wrong by factor two; leakage does not prove a gap. | A09 |

## Prioritized issue register

| ID | Priority | Exact location | Finding and evidence | Repair |
| --- | --- | --- | --- | --- |
| F01 | Blocker | Ch03 suggestion: tier 1 / orthogonality | Primitive root plus `[CommRing]`, even with length a unit, does not imply character orthogonality. Lean-proved Z/15 witness. | Field/domain or principal-root hypotheses; A01. |
| F02 | Blocker | Ch03 suggestion: integer powers | `zpow` needs an inverse/division structure; arbitrary ring roots should be lifted to units. | Character/unit abstraction or field layer; A01. |
| F03 | Blocker | Ch03 suggestion: algebraic Laplacian | Fractional k/2 exponent unspecified and negative sign incorrect. At L=4, ζ=i, k=2, primary eigenvalue is −4, suggested expression is +4. | Use ζ^k+ζ^−k−2; A01. |
| F04 | Design | Ch03–05 normalization and Hilbert types | Algebraic linear equivalence is not unitarity. 1/L inverse scaling is valid; physical CAR scaling needs \|a\|²L=1. | Separate algebra and one scalar normalization proof; A01/A02. |
| F05 | Gap | Ch04.4, Ch06.2–6.5 | Carrier norm/adjoint API and graded adjoin induction incomplete; noncommutative products need fixed order. | Euclidean/matrix bridge, graded words and matrix units; A02. |
| F06 | Design | Ch07.2, 7.7–7.9 | Charges and triangular ground energies need ℤ; natural subtraction and sorted-list bounds add avoidable friction. | Integer arithmetic, order isomorphism and displacement lemmas; A03. |
| F07 | Blocker | Ch08.16 and generating function after 8.18 | exp(βX) does not map polynomials to polynomials. Central BCH does not create that operator. | Formal coefficient identities or restricted finite expressions; A05. |
| F08 | Blocker | Ch08.8 technical normal ordering | One variable family cannot encode creators and annihilators. Mechanical normal ordering is not well-defined on equal represented operators. | Symbol/word carrier with evaluation-preserving Wick reduction; A02. |
| F09 | Blocker | Ch08.2 discussion | “No nontrivial finite-dimensional Heisenberg representations” is stronger than trace no-go. | State no scalar-identity CCR; correct trace discussion; A05. |
| F10 | Blocker | Ch09.6 final LI proof sketch | It uses H₀Ω=0; actual bare value is −h(h−1)/2. Result need not fail, but proof premise does. | Shift Hamiltonian or use EΩ+m eigenvalues; A04. |
| F11 | Gap | Ch09.11, Ch10–12 margins | Negative natural budgets and operator composition domains unspecified. Input-only equality is not a rewrite rule on arbitrary outputs. | Filtered maps, word excursions and composition lemma; A03. |
| F12 | Gap | Ch11.1 and Ch12 technical partition API | Endomorphism `Multiset.prod` unavailable; rectangle bijection and full Gram induction are substantial missing work; cited API path/name inaccurate. | Ordered folds, finite `Nat.Partition`, counting equivalence; A04. |
| F13 | Blocker | Ch12.2 / 12.1 note | Unrestricted mode commutator false: h=1,K=N=0 gives H_sug=0 but ρ₁Ω≠0. h−1 is not all nonzero shifts. | Eigenbasis-first proof, output-budget/cutoff corollary; A04. |
| F14 | Blocker | Ch13.4–13.11 | A budget Haldane basis does not define global operators; Nmax<h alone is insufficient for adjacent-sector dimension equality at high energy. Clifford conclusion unjustified. | Typed sector isometries with source and target margins; A05. |
| F15 | Blocker | Ch14.3–14.5 | Raising beyond K does not annihilate ambient vectors; at K=0 W⁻Ω≠0. | Explicit compression or full finite nilpotency; A05. |
| F16 | Blocker | Ch14.8 | At h=2,K=N=0,x=0, c_xΩ has a non-ground hole component; proposed B_xΩ has only target ground. | Redesign theorem as specified source/target matrix elements or larger carrier; A05. |
| F17 | Blocker | Ch14.3 zero phase, 14.7 adjoint | Zero mode changes sign under x→x+L. Also `(W⁺)†=−W⁻`, contradicting the stated adjoint. | Fix boundary twist, phases, minus signs and order; A05. |
| F18 | Blocker | Ch14.9–14.10, Ch20.2 | Input-only equality does not imply same-input adjoint equality or product/CAR equality. | Projection/adjoint/target-domain lemmas; A03/A05. |
| F19 | Blocker | Ch15.7–15.9 | Identical R/L representations give self-brackets 2C and cross-bracket zero. | Explicit opposite chirality orientation; A06. |
| F20 | Blocker | Ch15.10–15.13 | Missing i and minus; `(ζ^m−1)/m` not constant. Periodic Δ kernel has zero sum but included-zero-mode δ has sum one. | Actual differentiated finite kernel and zero-mode subtraction; A06. |
| F21 | Blocker | Ch15.12 and ch15 technical Δ reuse | Quotient formula undefined at coincidence; End coefficient algebra is not a CommRing. | Piecewise finite kernel; module-valued differences; A06. |
| F22 | Blocker | Ch16.3–16.7 | Two mixed-square contributions supply factor two; error scaling inconsistent; error annihilates sector grounds too. Taylor/RG is not exact finite algebra. | Explicit normal-order symbol expansion and comparison contract; A06. |
| F23 | Blocker | Ch17.1–17.6 and technical CAR swap | Transfer filters, ± domain and four-fermion normal ordering missing; CAR technical commutator wrong; N²/2 needs chemical-potential shift. | Explicit raw sums, Wick convention and units; A07. |
| F24 | Blocker | Ch17.8–17.10 vs Ch18.2–18.12 | Hopping form has v1±v2 scalar eigenvalues, not common √(v1²−v2²). | Choose actual rotation model or derive pairing model; A07. |
| F25 | Blocker | Ch18.10–18.11 and corollary | Squaring does not choose hyperbolic sign; stability needs v1>\|v2\|; transform direction/sign and zero-point constant missing; faster-wave claim too broad. | Positive real scalar package and explicit quadratic expansion; A07. |
| F26 | Blocker | Ch19.1 and technical state definition | No constructed positive normalized functional; compressed dressed annihilators may have zero joint kernel. Saved two-mode K=1 counterexample. | Construct finite ground state or separate abstract Gaussian algebra; A08. |
| F27 | Blocker | Ch19.8 | s² coefficient misses the opposite c² contraction; free-vacuum variance becomes zero incorrectly. Exact CAR witness is 1/16. | Compute both ordered moments; A08. |
| F28 | Blocker | Ch20.3–20.8 | Undefined D₁/prefactors and exponential semantics; scalar rewrites do not construct fixed-budget duality. | Exact finite observable contract, mapped models and domains; A08/A09. |
| F29 | Blocker | Ch21.4–21.10 | Global spin/charge edge cancellation not automatic; charge parity constraint and shared budget obstruct naive tensor factorization; spin pair residual undefined. | Restricted raw currents, parity sublattice and explicit spin factor; A09. |
| F30 | Blocker | Ch21.13 and gap interpretation | Per-species charge shift is ±1, not ±2. Leakage needs a nonzero witness and is not a gap theorem. | CAR number commutators, explicit leakage premise and separate spectral analysis; A09. |
| F31 | Blocker | Ch08.16, cross-mode case | Scalar BCH exponent omits δ_(m,m'); different-mode operators commute. This is separate from undefined exponential carriers. | Include the contraction factor in a well-defined formal identity; A05. |
| F32 | Blocker | Ch08.8 | `Σ J_m† a_m` is the unweighted number operator, not H_b with the given currents. On X₂ it gives 1 instead of 2. | Use `Σ J_m† J_m`; A02. |

“Blocker” does not mean the whole chapter should be discarded. Often a substantial valid finite theorem survives with a precise domain, normalization, or corrected coefficient. A05 and A07 require a choice of mathematical target before drafting their interfaces.

## Proposed appendix delivery

Nine candidate mathematical appendix notes have been written under [notes/appendices](../../notes/appendices/README.md). They contain repaired statement shapes, supporting lemma chains, design alternatives, and explicit remaining obligations. They are proposals for review, not new axioms to import or a declaration that downstream claims have been proved.

The minimum preparation before chapter 3 is A01 and the carrier convention from A02. Before chapter 7, agree the arithmetic/filtering conventions of A03. Before chapter 11, adopt A04's finite counting and word-margin machinery. Before attempting chapters 13–21, resolve the vertex target, chirality, quadratic model, and state-existence choices; otherwise compiler success could conceal impossible hypotheses.

## Evidence and reproducibility

- `lake env lean -DwarningAsError=true docs/audit/probes/FourierAssumptions.lean`: passes without warnings. Proves the primitive-root/unit-length/nonzero-sum ring counterexample and checks installed DFT API types.
- `python3 scripts/audit/check_reference_counterexamples.py`: exact integer/rational finite calculations for the ring, Sugawara, raising phase, vertex support, free variance, compressed vacuum kernel, and Umklapp charge shifts. These are computational evidence, not Lean proofs of those downstream claims.
- The script verifies the CAR relations of its occupation-basis operators before evaluating the witnesses.
- `python3 scripts/guards/stub_lock.py --check --strict --baseline-ref HEAD` and `core_lock.py --baseline-ref HEAD`: both pass for the existing frozen Core library.
- Source hashes in `reference_notes_inventory.json` cover the 21 numbered files, TOC and chapter 3 suggestion. The appendix/probe additions do not alter these inputs.
- The exact coefficient/sign/zero-mode contradictions are also derived directly in the appendix prose. No build of chapters 3–21 is claimed, and no source-note theorem has been made a Lean axiom.

## External and installed-source checks

The [official Mathlib DFT documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/ZMod.html) describes `ZMod.dft` and its 1/L inverse normalization. The [official primitive-root documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.html) states the domain hypothesis for the geometric-sum theorem. Both were checked against the installed package source and saved compiler probe.

The [von Delft–Schoeller constructive bosonization tutorial](https://arxiv.org/html/cond-mat/9805275), section 2.C, explicitly considers finite spatial size with infinite momentum bandwidth. Therefore its finite-size vertex identity cannot be cited as a proof of the finite-band/input-budget statement here. The counterexamples in this audit are direct finite calculations, independent of that comparison.

## Scope of changes

Original notes, TOC, suggestion files, existing skills/workflows and frozen Core were preserved. The new appendix collection, audit report/inventory, Lean probe and exact finite-witness script are review artifacts; the mathematical proposals remain pending review. An already present Windows `Zone.Identifier` sidecar is unrelated to this audit and was left untouched. No next chapter was started.
