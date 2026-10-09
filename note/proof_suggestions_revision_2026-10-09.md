# Revision guide for the Lean proof suggestions — 2026-10-09

## Scope, evidence, and status

This review covers the three external suggestions in `docs/proof_suggestion/` and `docs/stub_suggestion/`, the inline proof strategies in all 21 chapters and appendices A01–A10, and the historical 1D decimation/SW sketches in `notes/appendices/brainstorm.md`. The brainstorm's proposed future 2D/QED3 program is not mathematically audited here.

The review uses a snapshot captured at **2026-10-09 15:42:50 UTC**. Chapter and appendix revisions continued during this review. Thus the findings below identify problems in that snapshot's suggestions, rather than asserting that every quoted issue remains in the latest mathematical statements. Reconcile the suggestions with the corrected statements before implementing them. The earlier mathematical reviews are separate records: `further_changes_review_2026-10-09.md` and `revision_confirmation_2026-10-09.md`.

The external chapter 1 code was compiled unchanged and failed. The chapter 2 draft first failed on an obsolete import; adapting only two import paths in a temporary copy exposed further elaboration errors and definition placeholders. Chapter 3 is an architectural sketch, not a compilable Lean module. Several useful supporting identities and a Fourier counterexample were separately checked in Lean. None of this constitutes a proof of the later chapters.

The installed compiler is Lean **4.35.0-rc4**. Library facts below were checked against the installed Mathlib source and compiler, not inferred from the suggested names. Native Lean MCP tools are not exposed in this chat; direct compiler diagnostics and local source searches were used. No LSP validation is claimed.

## External draft decisions

### Chapter 1 — Keep the dependency plan, retire the replacement implementation

Source: `docs/proof_suggestion/Ch01LatticeBand_GeminiPro.md`, 287 lines.

**Keep:** arithmetic membership first; quotient/section inverse identities next; transport algebra through the bijection; derive cardinality and Nyquist behavior. This is a sound proof order.

**Reject as ready-to-use code:** the file claims rigorously implemented lemmas but does not compile. Representative failures are:

| Location | Compiler finding | Revision |
| --- | --- | --- |
| Line 107 | `ZMod.val_natCast x` supplies the modulus argument, not the residue argument. | Installed signature is `ZMod.val_natCast (n a : ℕ)`. |
| Lines 118, 203 | Positivity hL does not automatically install `NeZero L` or `Fintype (ZMod L)`. | Install the local instance at the use site; retain the mathematical positivity hypothesis. |
| Line 137 | Rewriting a value inside a dependent conditional yields an ill-typed motive. | Prefer the frozen quotient/section lemmas and integer divisibility bounds; avoid unfolding dependent subtype construction unnecessarily. |
| Lines 185, 192 | `rfl` does not prove the casted zero projection. | Use the established projection/cast equality. |
| Line 208 | Finset cardinality is not definitionally equal to subtype Fintype cardinality. | Use the explicit cardinality bridge already present in Core. |
| Lines 228–284 | Cast expressions and parity witnesses do not match the rewrite targets. | Normalize a single cast boundary and use the approved Core lemmas. |

Many later errors are consequences of earlier elaboration failures; do not treat this as a count of independent mathematical defects. Chapters 1–2 already have frozen Core implementations. Revise the suggestion into commentary referencing those declarations, rather than another module redeclaring their definitions and instances.

The chapter 1 inline recommendation of `ZMod.valMinAbs` has the correct positive endpoint in this installed version: `valMinAbs_mem_Ioc` states `−L < 2*valMinAbs ≤ L`. A closed test at L=2 returns +1. This is a useful library fact, but provides no reason to replace the frozen representative definition.

### Chapter 2 — Mark the draft as superseded by Core

Source: `docs/stub_suggestion/chapter_2_umbral_calculus_core.md`, 77 lines.

The suggested imports `Mathlib.Algebra.BigOperators.Group.Finset` and `Mathlib.Data.Polynomial.Derivative` do not match the installed paths. The corresponding paths used in the scratch adaptation are `Mathlib.Algebra.BigOperators.Group.Finset.Basic` and `Mathlib.Algebra.Polynomial.Derivative`.

After that adaptation, the draft still lacks the finite-lattice instance in `sum_by_parts`, has unresolved scalar parameters in its composition statement, and contains `sorry` in the definitions of `umbralMap` and `polyForwardDiff`. Those definition placeholders violate its own claim that definitions are complete and do not meet Phase A requirements.

Keep the discrete product-rule and finite reindexing ideas, but point to Core's bundled endomorphisms, polynomial maps and proved lemmas. Do not reintroduce the old unbundled function interface or use the weaker domain assumptions merely because the historical draft had them. Use basis extensionality for polynomial maps; `LinearMap.ext_ring` is an extensionality lemma for maps **from the scalar ring**, not a general polynomial-basis theorem.

### Chapter 3 — Adopt the two-stage construction with repaired contracts

Source: `docs/stub_suggestion/chapter_3_fourier_stub_draft.md`, 256 lines.

The unscaled character algebra followed by one complex normalization is still a good design. Repair these points in the draft itself:

- An arbitrary commutative ring plus a primitive root does not imply orthogonality. A practical field layer, or a domain layer with unit-valued characters, is appropriate. A maximal ring version needs the principal-character sum condition explicitly.
- Integer powers require a division structure or a root represented in the unit group. Do not write generic ring `zpow` without that structure.
- Call the second unscaled map synthesis, not an inverse before division by L. Asymmetric algebraic normalization is valid; it is simply not unitary for the two original counting inner products.
- Remove the fractional-power Laplacian formula at line 129. Use `(ζ^k−1)(1−ζ^(−k)) = ζ^k+ζ^(−k)−2`. If an auxiliary square root w is chosen, the equivalent square is `(w−w⁻¹)²`, without a leading minus.
- Use `EuclideanSpace ℂ _` or explicit matrix conjugate-transpose identities for the Hilbert layer. A plain function-space linear equivalence alone does not prove unitarity.

An independent Lean check uses `R = ZMod 5 × ZMod 5`, L=2 and ζ=(−1,1). It verifies that ζ is primitive, 2 is a unit, but `1+ζ=(0,2)≠0`. Thus invertibility of L does not salvage orthogonality in every commutative ring. This agrees with A01's existing warning.

## Recurring proof problems and revisions

### P01 — Replace suggested library names with checked obligations

Chapter 3 names `IsPrimitiveRoot.sum_zpow_eq`, `IsPrimitiveRoot.sum_pow_eq` and `Complex.isPrimitiveRoot_exp_of_ne_zero`; these constants were unknown even under `import Mathlib` in the installed version. Chapter 11's `basisOfLinearIndependentOfCardEqDim` was also unknown. In contrast, `IsPrimitiveRoot.geom_sum_eq_zero`, `AddChar.sum_eq_zero_of_ne_one`, `Polynomial.basisMonomials`, and `LinearMap.adjoint` exist, with specific hypotheses.

For each draft, record the exact import and signature of an adopted library result. A descriptive helper name should be labelled **proposed project lemma**, not presented as an existing Mathlib theorem. Check the required scalar, domain, finite-type and completeness instances before selecting a tactic.

### P02 — Normalize noncommutative words without inventing commutativity

Sources include chapters 4, 16, 18 and 21; A02 and A07.

`ring` cannot generally normalize operator products in `Module.End`. Expand sums/products and scalar actions, apply explicit commutation or CAR lemmas, and then normalize scalar coefficients. `abel` can collect additive terms but cannot reorder multiplication. A fixed ordered product or an API taking pairwise commutativity is needed; a `Finset.prod` does not become available on all endomorphisms because one particular family commutes.

There is a useful exception in chapter 16: `(X+Y)²+(X−Y)²=2(X²+Y²)` holds in an arbitrary ring. Its cross terms cancel without an extra commutativity hypothesis. A scratch Lean proof using `noncomm_ring` passed. Do not require the fields to commute just to prove this identity.

A02's asserted generic four-factor anticommutator identity is not a general ring identity. Setting A=C=1 makes its right side `3[B,D]`, while the left side is `[B,D]`. Use the directly proved CAR bilinear identity instead:

\[
 [c_p^\dagger c_k,c_q^\dagger c_l]
 =\delta_{kq}c_p^\dagger c_l-\delta_{pl}c_q^\dagger c_k.
\]

If a general four-factor helper is wanted, expand and verify it independently. Do not install unconditional swap rules in `simp`: symmetric rules can loop, and a canonical ordering must preserve fermionic signs and contractions.

### P03 — Keep carriers, adjoints and scalar actions explicit

Sources include chapters 4, 7–8, 12–14 and A02/A05/A09.

Use one concrete occupation carrier with its Euclidean basis. Distinguish a configuration label from its ket, a `Basis` from the linear map constructed from its images, and an ambient operator from a map between submodules. Negative charge N must remain an integer; chapter 12's suggested `{N K M : ℕ}` with `N.natAbs` is not the intended interface.

Over ℂ, the weighted polynomial form must be **Hermitian/sesquilinear**, not merely a bilinear form. Its finite-slice adjoints are ordinary finite-dimensional adjoints. Ambient polynomial creation and differentiation are algebraic operators with a proved pairing identity; Mathlib's finite-dimensional `LinearMap.adjoint` does not automatically apply to the entire infinite-dimensional polynomial carrier.

In endomorphism exponentials, use scalar multiples `((j! : ℂ)⁻¹) • A^j`, not division of one endomorphism by another. Resolve the real-to-complex normalization once. For physical CAR, the minimal scalar condition is `L*conj(b)*b=1`; a canonical positive real b is a convenient chosen instance, rather than a necessary hypothesis of the general CAR transport lemma.

### P04 — Use positive boson weights and support-based filtration

Sources: chapter 8 and A02/A03.

The suggestion `Q := Fin M` introduces index zero. If its raw index value is used as m, then A₀=0 and X₀ has weight zero; all its powers lie in a fixed weight slice. The claimed finite-dimensional budget and nonvacuous oscillator relation then fail.

Use `weight i=i.val+1` on `Fin M`, or a positive-mode subtype. Prove positivity once. Define the budget by support of monomials of weighted degree at most K, then prove closure under addition/scalar multiplication, a finite monomial basis, and the grading of X and derivatives. This is easier to reuse than treating a maximum-degree function as an unexplained submodule predicate.

For a positive weight m, a power beyond `⌊K/m⌋` annihilates the lowering restriction. A compressed positive raising phase increases weight by at least one, so its (K+1)-st power vanishes. Prove these bounds from grading; finite dimension by itself does not imply nilpotency.

### P05 — Prove normal ordering on symbols or words

Sources: chapters 8, 16–17 and A02/A07.

The installed argument order is `FreeAlgebra ℂ (Mode ⊕ Mode)`, not the order written in A02. For normal symbols, specify evaluation on every monomial as a fixed ordered creator/annihilator product, then extend **linearly**. Specifying images of variables as an algebra homomorphism from a commutative polynomial algebra would force their images to commute.

Separate the bosonic rewrite `A C → C A + mI` from fermionic CAR swaps. Use a terminating word recursion ordered by word length and inversion count, with an evaluation-preservation theorem. Do not identify four-operator sea normal ordering with subtraction of only the scalar vacuum expectation: partial contractions generally leave lower-degree operator terms.

### P06 — Compute truncated shifts on the actual band

Sources: chapter 9 and A04.

Remove chapter 9's inline replacement band `{-L,…,L−1}`. Keep the frozen positive-Nyquist band. Define partial shifts using **integer label equality**, not addition in the residue lattice. An unsigned enumeration can be used only with a proved label map.

`T_m T_n=T_(m+n)` is globally valid for same-sign shifts on the interval, not arbitrary mixed signs. For a mixed product, retain the intermediate-in-band indicator. Prove that matrix coefficient formula first, then the diagonal and off-diagonal edge formulas. Lift with the CAR bilinear commutator and the linear Lie map dΓ. Do not treat dΓ as a multiplicative/unital algebra map.

Derive the first vacuum norm from orthogonal hop kets or the exact edge occupation formula. Avoid invoking a later scalar CCR whose proof depends on the nonzero action being established.

### P07 — Check margins at the actual commutator application

Sources: chapters 7, 10–12, 14–18 and A03/A04.

The relevant object is the vector on which a restricted scalar commutator is used. A theorem already proving `[A,C]ψ=mψ` on input ψ does not additionally require every intermediate factor to stay in that same subspace. What needs an enlarged margin is a later substitution on a different vector, such as a suffix of a word.

Track operator application order, signed cumulative shifts, and the largest prefix energy. For a written product, the rightmost operator acts first. A sum of all positive shifts is a safe wrapper but often unnecessarily strong. When a rewrite changes word order, certify the suffixes appearing in the rewritten terms as well.

For Gram induction, keep the useful R2 bound `2K+|N|≤h`. At a pull-through step with lowering m and creator n, the right remainder has E≤K−n, hence `m+n+E≤m+K≤2K`. The snapshot's main chapter 11 paragraph now records this improvement, but its earlier strategy still substitutes a whole-prefix estimate and writes `[ρ_m,ρ_-m]=+m`. Correct the sketch to `[ρ_-m,ρ_m]=+m` and use the remainder invariant throughout.

Do not impose `2M+K` in Sugawara merely because its sum runs to M. Terms with m>K annihilate the input on their right. Commute only the retained terms that can act, using the Gram proof's local bounds.

### P08 — Include the projection remainder in every product argument

Sources: chapters 14 and 20–21; A03/A05/A09.

The exact identity is

\[
 P_t A B P_s-P_t A P_m B P_s
 =P_t A(1-P_m)B P_s.
\]

Use it as the starting lemma. The **minimal equality criterion** is that this remainder vanishes. Proving that B maps the source into the intermediate budget is one sufficient way; proving that the final projected A kills the escaped component is another. This avoids requiring every factor to preserve one common cutoff.

Taking adjoints reverses the source/target spaces and the projection order. A typed Klein isometry needs surjectivity/equal basis labels before its adjoint can be identified with its inverse. Do not infer a global operator or CAR identity from equality on a single input budget.

### P09 — Match the whole projected vertex base case

Sources: chapter 14 and A05.

A ground-to-ground coefficient check is necessary but not sufficient for the cyclic induction. With positive output cutoff, `P_out c_x|N⟩` contains excited hole configurations as well. Compute this entire projected vector and match it to the raising exponential on the shifted ground. Then prove the exact typed current/fermion intertwining relation, including edge/projection residuals, and induct on the source partition word.

Proposed dependencies: `projected_fermion_ground_expansion`, `vertex_ground_expansion`, `current_fermion_commutator_with_edges`, and `vertex_intertwining_on_word`. Each should state its actual source/target budgets. Do not conclude uniqueness from only one matrix element, or from irreducibility of a slice on which creators are not endomorphisms.

### P10 — Prove nilpotent exponentials and formal BCH separately

Sources: chapter 8, A05 and the historical brainstorm.

The useful expNil proof is finite: prove power vanishing, cutoff independence, inverse under A↦−A, and adjoint compatibility. Its factorial coefficients require a ℚ-algebra or a suitable characteristic-zero field, not division in the endomorphism ring.

The scalar BCH relation needs the actual central-commutator hypotheses on its chosen carrier. Compressed creators and derivatives acquire boundary terms and do not meet those hypotheses globally. Formal power series with a central parameter, finite nilpotent exponentials, and scalar analytic exponentials are different constructions. `PowerSeries.exp A` in Mathlib takes a coefficient **type A**, not an operator to exponentiate; define the operator-valued coefficients of exp(tT) explicitly or use a verified rescaling/construction.

The brainstorm's finite-slice nilpotency claim for the SW generator is false: `S=[[0,−1],[1,0]]` is anti-Hermitian and has `S²=−I`. Use a nilpotent formal parameter t modulo t³, rather than asserting nilpotency of S.

### P11 — Separate scalar Bogoliubov algebra from current-action identities

Sources: chapter 18 and A07.

The inverse linear transformation needs only real scalars with c²−s²=1; it needs no budget or CCR. CCR preservation is a separate expansion on the permitted inputs. Quadratic diagonalization reorders same-mode products and uses diagonal current CCR; do not give it the stronger all-mode hypotheses automatically.

Correct the sketch's reorder to `ρ_-m ρ_m=ρ_m ρ_-m+mI`. A07's proposed `tanh(2θ)=−v₂/v₁` has the wrong sign for the plus-sign transform and matching `2ucs=v₂`. A construction avoiding inverse hyperbolic functions is

\[
 u=\sqrt{v_1^2-v_2^2},\quad
 c=\sqrt{(v_1+u)/(2u)},\quad s=v_2/(2uc).
\]

Under v₁>|v₂|, prove u>0 and c>0 before cancellation. This covers positive, negative and zero v₂. Establish the matching identities once; downstream operator proofs use their algebraic fields and do not repeatedly unfold square roots.

For the simultaneous-vacuum obstruction, use scalar CCR on the candidate input and s≠0. Do not claim that one density creator has trivial kernel on all finite Fock vectors, or use “cyclicity” as a substitute for that hypothesis.

### P12 — A quantum state is a positive linear functional, not a scalar homomorphism

Sources: chapter 19 and A08.

The suggestion of `StarAlgHom` for the vacuum state is impossible for nonzero scalar CCR: a multiplicative map to ℂ sends every commutator to zero, but normalization sends mI to m. Use a normalized positive complex-linear functional. Its trace-like or multiplicative properties must not be assumed.

A08's contraction strategy also reverses the CCR sign: use `[A_m,C_n]=δ_mn*m*I`, with the negative sign for the reverse order. State the dressed annihilation conditions for the specified family, rather than one unnamed P, and prove positivity and existence of the state separately.

For quadratic moments, the CCR, dressed annihilation conditions, and inverse transform suffice; no extra finite-budget restrictions belong to the abstract CCR theorem. Prove a concrete existence/positivity result separately, for example using the algebraic weighted polynomial representation and its vacuum pairing, then transport the state through the abstract Bogoliubov equivalence. A structure with impossible proof fields would make all subsequent conditional theorems vacuous.

Define abstract Weyl/formal vertex objects before evaluating exponential correlations. The polynomial CCR algebra does not automatically contain such exponentials. A finite expNil calculation cannot be replaced by a scalar Gaussian exponential by applying Wick's theorem without a carrier/evaluation theorem.

### P13 — Build duality and spin decompositions from generators and charges

Sources: chapters 20–21 and A09.

Define the proposed model map on actual generators and prove relation, star and inverse preservation before claiming an equivalence. Preserve phase and zero-mode factors; they cannot be discarded as an unspecified prefactor.

Construct the charge map `(N_up,N_down)↦(Q_c,Q_s)` as an equivalence onto the parity-constrained lattice, with a proved integer inverse. A total-energy budget is a sum over compatible energy splits, not the tensor product of two independently bounded budgets. The draft predicate `Hψ≤Kψ` is not meaningful as an ordinary vector inequality; use coordinate energy support, or a separately defined operator-order statement.

Mixed spin/charge current commutators retain the difference of same-species edge terms outside the common action regime. Cross-species commutativity alone does not eliminate that difference.

### P14 — Formalize SW by coefficients, with only coupled-pair nonresonance

Sources: chapters 17–18, A10, historical brainstorm.

Use a block-adapted eigenbasis of a self-adjoint H₀ commuting with P and Q. Define S₁ as zero on uncoupled pairs, and as V_λμ/(E_λ−E_μ) on nonzero cross-block couplings. Only those latter denominators need to be nonzero. Do not demand that every pair of eigenvalues be distinct or that the spectrum be globally separated when the target theorem only uses connected pairs.

For the second-order result, coefficient triples modulo t³ suffice: expand exp(tS₁) as `1+tS₁+t²S₁²/2`, multiply with H₀+tV and the inverse triple, then project. Required helpers are anti-adjointness, the generator equation, and `P[S₁,V_diag]P=0`. If full block diagonalization through second order is wanted, supply an S₂ equation; S₁ by itself need not remove every second-order off-block term. Preserve the distinction between a projected coefficient theorem and an exact finite-matrix rotation.

The historical decimation sketch also needs an energy-shell decomposition `B_K=B_(K−1)⊕H_K`, not a one-dimensional discarded space ℂ·X_K. At K=2 the shell already contains X₁² as well as X₂. Compression is not a partial trace without a proved factorization. The asserted normal-order vacuum factor `1−1/K` is unsupported (the normally ordered single-mode vacuum expectation is one), and a non-strict norm bound for compression does not imply strict decay or an RG irrelevance theorem. Keep these physical claims outside the finite coefficient proof.

### P15 — Construct a leakage coefficient, not just a charge shift

Sources: chapter 21 and A09.

Under the current computational site-field convention, a useful witness family is available without any CCR margin:

1. Let L=2h with h≥1, K=0 and N_max=0 for all four species. Take the joint half-filled ground configuration S, with occupied momenta −h+1,…,0 in every species.
2. Form T by adding momentum 1 in each L species and removing momentum 1−h in each R species. These modes are admissible and Pauli-allowed. T has charges (+1,+1,−1,−1), hence is outside the charge box.
3. The selected Fourier exponent is `2(1−h)−2=−L`, so the character is one at every site. The spatial sum therefore survives exactly.
4. The matrix element is `σ*g_U/L²`, where σ∈{±1} is the fixed CAR ordering sign. No adjoint Umklapp term has those same target charges, so it cannot cancel this component.

An exact Gaussian-rational check at L=4, with species order L-up, L-down, R-up, R-down, gives **−g_U/16**. In hexadecimal occupation masks, S=0x3333 and T=0x2277. This is an independent coefficient check, not a Lean proof of the general family.

Propose `umklapp_selected_coefficient` followed by `umklapp_leaks_zero_charge_box`. If the physical left field is redefined with a different Fourier convention, recompute the selected exponent and witness before adopting it. Do not impose the current CCR margin on this direct CAR coefficient proof.

## Supporting-lemma packages and useful criteria

These are proposed project obligations; their names do not assert that the declarations already exist. Avoid duplicates where frozen Core already supplies the result.

| Package | Supporting obligations | Hypotheses to retain; unnecessary restrictions to avoid |
| --- | --- | --- |
| Fourier | Representative independence; character addition/negation; finite sum transport; orthogonality; synthesis compositions; conjugation and scalar normalization | L>0; a valid character cancellation assumption; invertible L only when dividing. No global CharZero requirement for the generic field identities. |
| Occupation CAR | Insert/erase sign counts; basis action; adjoint matrix coefficients; CAR; diagonal number/parity; bilinear commutator | Finite ordered labels, proper Euclidean carrier. No requirement that every operator commute. |
| Budget grading | Sorted displacement identities; nonnegative excitation; coordinate projection; homogeneous operator shift; lowering annihilation | Integer charges and excitation labels; admissibility for nonzero ground witnesses. Do not hide negative energy by `toNat` before proving nonnegativity. |
| Current edges | Partial-shift coefficient formula; same-sign composition; exact edge commutators; frozen occupation/hop action; lift to spans | Integer shifts and actual band labels. No false global scalar CCR or global mixed-sign shift composition. |
| Gram and Sugawara | Word energy; suffix pull-through; Gram recurrence; partition/configuration inverse maps; whole-budget basis; termwise energy action | Keep the established sufficient R2 regime and prove its suffix bounds. M≥K for Sugawara; no upper M margin for terms that already annihilate the input. |
| Klein and vertex | Common basis labels; Gram preservation and surjectivity; charge phases; cutoff transitions; full projected ground expansion; typed intertwining | Prove source/target completeness actually used. Do not infer inverse from isometry alone or impose one invariant cutoff on every factor. |
| Projection calculus | Agreement after a map; adjoint reversal; product remainder identity; vanishing remainder criterion | A matching input/output contract. The remainder criterion is weaker than requiring B to preserve the intermediate budget. |
| Bosonic filtration | Positive mode weights; finite monomial slice; creator/derivative grading; nilpotency; weighted Hermitian pairing | Positive weights, scalar factorial inverses where used. Do not infer nilpotency from finite dimension or install an ambient bounded-adjoint API without justification. |
| Bogoliubov | Scalar inverse; parameter existence; same-mode quadratic expansion; input-action CCR | c²−s²=1 for inverse; real/self-adjoint scalars for star; v₁>|v₂| for positive stable parameters. No v₂>0 restriction. |
| States and vertices | Vacuum functional existence/positivity; contractions; Wick recurrence; an actual Weyl/formal exponential evaluation | Linear normalized positive state, correct carrier. No multiplicativity of the state or finite-Fock CCR representation. |
| SW | Adapted spectral coordinates; coupled-pair generator; anti-adjointness; coefficient conjugation; projected second-order term | Nonresonance only where the nonzero coupling is divided. Nilpotent parameter, not nilpotent S. |
| Umklapp | Exact species shift; selected Fourier coefficient; nonzero spatial sum; outside-projection coefficient | h≥1 and g_U≠0 for the stated witness family. No CCR or artificial large-budget assumption. |

Numerical sanity checks help distinguish useful conditions from vacuous ones. A nontrivial uniform current regime is h=4, M=1, K=1, N=0. For a **diagonal** current commutator, h=2, m=1, K=1, N=0 already satisfies m+K+|N|≤h; the stronger all-pair bound 2M+K≤h would reject it unnecessarily. A quadratic same-mode theorem should retain the former when that is all its proof uses. We do not weaken the established Gram regime merely because a smaller toy example happens to pass.

An especially useful nondegeneracy helper follows from `[A,C]ψ=mψ` and C†=A:

\[
 \|C\psi\|^2=\|A\psi\|^2+m\|\psi\|^2.
\]

For m>0, this proves that C is injective on the inputs where that CCR holds. It does not assert global injectivity of a finite-band creator. Establish the first vacuum norm independently to keep the dependency order non-circular.

## Coverage and recommended proof order

| Chapters | Revision focus |
| --- | --- |
| 1–2 | Replace stale replacement modules with references to frozen Core; check imports, local instances and basis extensionality. |
| 3 | Character/scalar contract, then unscaled inversion, then Euclidean unitarity. |
| 4–6 | Concrete basis/sign helpers, CAR/adjoints, diagonal parity, word spans and matrix units. To prove the global algebra is full, first recover momentum generators by inverse Fourier, then construct matrix units in the already chosen occupation basis. |
| 7–10 | Coordinate grading/projections, partial shifts and dΓ, exact edge action before scalar CCR. |
| 11–12 | Suffix pull-through and rectangle bijection before Gram/completeness; whole-budget basis before Sugawara extension. |
| 13–14 | Typed basis maps and phases; full projected ground matching before vertex induction. |
| 15–16 | Additive operator-valued difference, exact character collapse and normal symbols. Do not apply chapter 2's commutative coefficient interface directly to End. |
| 17–18 | Settle the physical/computational dictionary first; scalar matching and diagonal expansion separately; SW on an actual baseline. |
| 19–20 | Construct the chosen abstract state and vertex carrier before exponential moments and duality. |
| 21 | Parity charge map and restricted spin currents; singlet paths; direct CAR leakage coefficient. |

Appendix coverage: A01 maps to P01/P03 and the Fourier package; A02 to P02–P05; A03 to P03/P07/P08; A04 to P06/P07 and Gram/Sugawara; A05 to P08–P10; A06 to P02/P03 and exact field differences; A07 to P02/P05/P11; A08 to P12; A09 to P08/P13/P15; A10 to P14. The historical brainstorm's reusable ideas must be reconciled with P10/P14, not imported as proved facts.

The suggested proofs should use this dependency order instead of starting every later goal with a large CAR expansion or repeated scalar square-root manipulation. Prove basis action and grading once, reuse typed composition lemmas, and keep each expensive combinatorial argument local to its package.

## Acceptance criteria for a revised proof draft

1. It identifies the exact target declaration or clearly labels a proposed helper. A helper cannot replace the desired result with a stronger hypothesis unnoticed.
2. Its objects, domains, adjoints, scalar casts and exponent meanings elaborate under the repository's actual settings. Definitions contain no placeholders.
3. Its rewrite rules preserve noncommutative order, signs, projections and contraction terms. A local scalar CCR remains an input-action theorem.
4. Each required margin is attached to the commutator input where it is used. State both the local contract and an optional simpler sufficient wrapper.
5. It supplies a ground/nonzero-action witness and a counterexample outside the intended regime where useful. Free interaction parameters, zero coupling and negative admissible charges remain supported when the result allows them.
6. It does not assume the existence of the state, isometry inverse, duality or exponentiation carrier that the proof is supposed to construct.
7. Claimed executable code has a recorded compiler result. A successful build with `sorry` is not proof completion; Core promotion requires zero warnings/placeholders and the standard axiom audit.
8. New helpers in frozen interfaces remain proposals until reviewed and locked. The present task does not change any Lean baseline.

## Checks performed and auxiliary cleanup policy

Seven scratch Lean examples passed with warnings treated as errors: composition of restricted agreement, the exact projection remainder identity, the noncommutative square identity, the positive Nyquist value, and the primitive-root/unit/nonzero-sum components of the product-ring counterexample. The original and import-adapted suggestion failures above are recorded as failures, not repaired proofs. Exact finite calculations also checked the Umklapp coefficient and the nonnilpotent SW matrix.

Both freeze checks passed before cleanup: 52 statements and 54 frozen commands, and two complete Core files. No full build or proof completion is inferred from those checks.

Following the user's subsequent cleanup instruction, visible correction comments were added in A02, A05–A09, and `brainstorm.md`. They mark the false generic CAR identity, complex-pairing and scalar-action issues, the Bogoliubov/CCR sign errors, the ill-typed vector energy predicate, and the unsupported decimation/SW claims.

Commit **79b3a2d**, `docs(notes): checkpoint auxiliary notes before issue cleanup`, preserves the previously uncommitted A02/A06 versions before deletion. The brainstorm was already committed. Removed material consists of obsolete historical criticisms about the Chapter 8 weight/normal-symbol definitions, the Chapter 15 gradient, and the Chapter 16 factor/total-Sugawara definition, plus one verified duplicate SW section and two timeout artifacts. Their replacements were checked in the current source notes. No unsolved theorem was deleted or declared proved; “issue solved” in the cleanup commit refers to these source/editorial repairs.

The cleanup commit contains only the seven affected auxiliary files and this report. For A05/A07/A08/A09, only the newly added comments are staged; their existing user revisions remain unstaged, as do the chapter revisions. The earlier review notes remain audit records rather than being deleted wholesale as if every historical finding were resolved.

## Execution of this guide — current revision follow-up

The original findings above refer to the 15:42:50 UTC snapshot. On the later user-authorized review, incoming chapters/appendices/reviews and the updated formalizer guidance were checkpointed as **d3770c1** before applying the guide. See [current revision verification](current_revision_verification_2026-10-09.md) for the C01–C13 reconciliation, attachment corrections, exact counterexamples, task attribution, and remaining contracts.

The three external suggestions are now revised: Chapters 1–2 reference frozen Core rather than redeclare it; Chapter 3 retains character algebra and unscaled inversion before complex isometry. Affected inline strategies in the chapters and A01–A10 now apply P01–P15. The original code and old review findings remain available in Git; their historical line numbers are not locations in the revised drafts.

| Guide | Applied revision |
| --- | --- |
| P01 — Library names | Checked basis, derivative, adjoining, character-sum, primitive-root, finite-adjoint, and DFT APIs; removed guessed names from active strategies. |
| P02 — Noncommutative algebra | Explicit CAR/CCR substitutions, fixed factor order, no unconditional symmetric swap simp set; scalar normalization separate. |
| P03 — Carriers/coercions | Euclidean Hilbert basis, integer charges/band labels, typed Fourier directions, Derivation.toLinearMap. |
| P04 — Grading | Positive Fin-mode weights, coordinate/support budgets, nilpotency from grading, inactive Sugawara terms zero. |
| P05 — Normal ordering | Word/symbol carrier, fixed ordered linear evaluation, contractions and evaluation preservation; raw quartic reduction pending. |
| P06 — Densities | Integer-label filtered pairs, retained mixed-shift indicator, direct occupation-hop first norm proof. |
| P07 — Margins | Right-remainder Gram invariant and actual suffix inputs; no unnecessary same-budget premise on a proved commutator. |
| P08 — Restricted products | Exact projection remainder retained, typed intermediate budgets, actual compressed adjoints. |
| P09 — Vertex base | Full projected ground vector required; ground scalar and numerical margin alone insufficient. |
| P10 — Exponentials | Factorial scalar action, formal coefficient carrier, no unsupported parameter evaluation or compressed scalar BCH. |
| P11 — Bogoliubov | Algebraic real witnesses, correct plus-sign reordering, scalar inversion separate from CCR; ψ≠0 in obstruction. |
| P12 — States | Normalized positive linear functional and existence obligation; no multiplicative scalar map. |
| P13 — Duality/spin | Charge-compatible map still pending, integer parity inverse, compatible total-energy splits. |
| P14 — SW | Both off-block terms, piecewise coupled-entry denominators, actual adjoint equations, exact identity-rotation special case. |
| P15 — Leakage | Nonzero outside component, proper-box inward counterexample, useful zero-charge witness family. |

### Checked Lean 4 patterns

The current compiler, not a generic style claim, establishes the following APIs. All 17 references were checked together with four proof examples through `lake env lean --stdin`, without modifying project Lean files. The initial inverse-DFT name guess was corrected before the successful final run.

| Purpose | Installed API / contract |
| --- | --- |
| Occupation basis | `EuclideanSpace.basisFun ι ℂ`, then `.toBasis` |
| Construct a map from basis images | `b.constr ℂ images`, where b is a `Module.Basis` |
| Equality on a basis | `Module.Basis.ext` |
| Polynomial monomial basis | `Polynomial.basisMonomials R` |
| Polynomial partial derivative | `MvPolynomial.pderiv i : Derivation …`; use `.toLinearMap` |
| Creator map | `LinearMap.mulLeft ℂ (MvPolynomial.X i)` |
| Generated algebra / monotonicity | `Algebra.adjoin`, `Algebra.adjoin_mono` |
| Basis from independence and count | `basisOfLinearIndependentOfCardEqFinrank'`; supply finite dimension and cardinality=finrank |
| Canonical complex primitive root | `Complex.isPrimitiveRoot_exp L hL`, hL:L≠0 |
| Nontrivial-character sum | `AddChar.sum_eq_zero_of_ne_one`; finite additive group and domain codomain |
| Primitive-root geometric sum | `IsPrimitiveRoot.geom_sum_eq_zero`; actual order>1, not automatically L for ζ^m |
| Hilbert adjoint | `LinearMap.adjoint`; finite-dimensional inner-product source and target |
| Raw word algebra | `FreeAlgebra ℂ (Mode ⊕ Mode)` |
| Complex DFT | `ZMod.dft`; inverse is `.symm`, with `ZMod.invDFT_apply` |
| Real-cast conjugation | `Complex.conj_ofReal` |

Each helper name proposed elsewhere remains a project proposal until elaborated. These examples illustrate recommended construction and proof patterns; they are not new project declarations or chapter proofs:

```lean
import Mathlib

example {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ι : Type*}
    (b : Module.Basis ι ℂ V) (v : ι → W) (i : ι) :
    b.constr ℂ v (b i) = v i := by
  simp

example {A : Type*} [Ring A] (X Y : A) :
    (X + Y)^2 + (X - Y)^2 = 2 * (X^2 + Y^2) := by
  noncomm_ring

example {V : Type*} [AddCommGroup V] [Module ℂ V]
    (Pt A Pm B Ps : Module.End ℂ V) :
    Pt*A*B*Ps - Pt*A*Pm*B*Ps = Pt*A*(1-Pm)*B*Ps := by
  noncomm_ring

example {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c s : ℝ) (h : c^2 - s^2 = 1) (X Y : V) :
    c • (c • X + s • Y) - s • (s • X + c • Y) = X := by
  rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
  have h1 : c*c - s*s = 1 := by nlinarith [h]
  have h2 : c*s - s*c = 0 := by ring
  calc
    (c*c) • X + (c*s) • Y - ((s*s) • X + (s*c) • Y) =
        (c*c - s*s) • X + (c*s - s*c) • Y := by
          simp only [sub_smul]; abel
    _ = X := by rw [h1, h2]; simp
```

The projection identity is exact without any range hypothesis. To replace the projected product by the ambient product, prove its right-hand side is zero. This is weaker and more useful than requiring every factor to preserve one shared cutoff.
