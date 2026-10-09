# Issue review: spatial boundary twists versus graded locality

Date: 2026-10-09. Status: **additive Ch06Ext Phase A drafted; interface review pending**. Baseline: `9f56510` (CH01–CH06/A01/A02 frozen; A03/CH07 Phase A unlocked). This report reviews the user's pasted note and the current, locally edited CH01/A05/CH14 sections. Those source edits are preserved; this report does not approve their new claims as implemented mathematics. Frozen sources and locks are preserved. The separately authorized extension now has complete staging data and unproved review contracts; see the addendum below.

## Finding and scope

The current Lean implementation is periodic. `Ch01.Lattice L` is `ZMod L`; `Ch05.positionAnnihilation` is the integer-character Fourier sum with no flux parameter. `Ch06.twisted_locality` is the graded disjoint-region exchange sign. It establishes neither spatial translation covariance nor nontrivial holonomy around the ring. A05 and CH14 have proposed twist prose but no Lean implementations. The statement that the existing graded net already implements physical APBC is false.

The positive Nyquist representative makes the quotient enumeration exact and complete. It does not turn periodic fermions into anti-periodic fermions, nor produce reflection-symmetric integer representatives. Spatial holonomy and graded exchange are independent data. A local CAR algebra without chosen transport around the ring cannot distinguish the external boundary phase.

A CH06 covariance extension is appropriate if spatial transport is to be part of the net's specification. It is additional scope, not a repair of the already proved graded-locality theorem. Preserve frozen CH06; use a separate reviewed supplement with its own A–B–C cycle. First supply the twisted field/character contract beside CH01/A01/CH05, then prove optional local-net covariance from it. A05/CH14 must consume the same contract in their zero modes. Postponing every twist obligation until the vertex chapter would leave its physical comparison field unspecified.

## Verified literature convention

Primary source: [von Delft–Schoeller, cond-mat/9805275v3](https://arxiv.org/pdf/cond-mat/9805275). Relevant anchors are Eqs. (2), (3), (5), (62)–(64), and (67)–(69), rather than the supplied subsection numbering.

Their momentum label is n−δ_b/2, their annihilation Fourier sign is negative, and boundary holonomy is exp(iπδ_b). δ_b=0 is periodic; δ_b=1 is APBC. Their linear-dispersion charge energy is N(N+1−δ_b)/2. The repository uses the positive Fourier sign, so translating parameters requires tracking chirality/sign. For positive-kernel fields with momentum offset β, holonomy is exp(2πiβ); β=−1/2 is APBC as well as β=+1/2 modulo integers. Use β=−1/2 to keep the current finite band labels and get centered physical half-integer momenta.

Separate primary teaching reference for the spin-chain issue: [Lamacraft, Jordan–Wigner and Bosonization](https://austen.uk/courses/tqm/jordan-wigner/), section “Solving the XY Model.” Periodic spins produce periodic fermion Hamiltonians in odd-number sectors and APBC in even-number sectors under the displayed convention. This is a consequence of the Jordan–Wigner boundary string, not of an integer-charge full-period exponential. The model and string convention must be specified before exporting that sector rule.

## Corrections needed in the current prose

1. **CH01 §1.5:** replace the claim that CH06 graded locality implements the spatial twist with the implementation inventory above. Retaining +h addresses residue representatives only. Core characters/operators have complex scalar carrier ℂ; they are not implemented as a separate ℚ(ζ_L) scalar field. Rational twists can require an enlarged root field if a cyclotomic coefficient restriction is later imposed.
2. **A05 twist subsection:** for integer N, exp(2πiN)=1. Thus exp(2πi(N+β))=exp(2πiβ): the boundary phase of a fixed-flux fermion is independent of N. A Klein lowering changes the position-dependent phase by exp(−2πix/L), but does not change its full-period holonomy. Jordan–Wigner parity dependence needs its own sector rule.
3. **CH14 Definition 14.2:** a nontrivial twisted field cannot be a representative-independent scalar-valued function on `ZMod L`, because [x+L]=[x]. Use integer lifts with quasi-periodicity or a field in a flat line bundle with specified transport. Evaluating a phase on x.val defines a fundamental-domain section; the seam transport still needs to be declared.
4. **Fractional notation:** ζ raised to a fractional power must not be treated as an ordinary integer `zpow` or unspecified complex-power branch. Use a selected per-site unit r with r^L=τ, or explicitly exp(2πiβx/L). A chosen L-th root is more information than holonomy τ alone and determines the trivialization.
5. **Matching the physical field:** Z_β cannot be matched to frozen c_x merely by inserting β into the source exponent. Its comparison field must also be twisted. For source charge N and an admissible target N−1, the one-species ground coefficient is L^(-1/2)(−1)^(h+N−1)r^xζ^(Nx) for the proposed twisted field. The empty endpoint N=−h has no admissible lowered ground ket and the annihilation action vanishes. Source-before-Klein ordering remains necessary, but a mistaken target phase is a position-dependent factor, not a change of boundary holonomy.
6. **Oscillator versus full boson:** same-species densities with unit holonomy have cancelling phases. Oscillator fields built with integer density modes are periodic. A full boson including its charge winding need not be periodic. Cross-species bilinears with unequal twists need separate phase accounting.
7. **Scope of APBC benefits:** a half-integer shift removes a zero label for linear chiral dispersion and permits a centered half-integer finite band. It does not generally eliminate Umklapp, all finite-band edge artifacts, or Fermi-level degeneracies of arbitrary dispersion. A cosine lattice dispersion and a linear chiral spectrum must not be conflated.

These are proposed corrections for the three locally edited notes, not changes already applied to them. The earlier F17 boundary sign is an error relative to a periodic comparison field; it can be intended APBC only after changing that comparison contract consistently.

## Concrete additive contract proposal

Keep the existing mode index `Band L`, site quotient, occupation space, CAR, and Core proofs. Supply a unit complex number r (conjugate r times r is one), with external holonomy τ=r^L. Define an integer-lift field by

    c_r(n) = r^n • Ch05.positionAnnihilation L ([n]),  n ∈ ℤ.

The creation field is its actual adjoint, with conjugate phase. Required new contracts:

- c_r(n+L)=τ • c_r(n), its adjoint analogue, and the periodic/APBC specializations.
- Canonical CAR on the chosen L site representatives, plus a lift-aware CAR formula across the seam.
- Same-species density invariance under the full-period shift; scalar phase-rescaling preserves each local algebra and its grading.
- A consistent positive-kernel Fourier expression with shifted physical momenta. APBC may use the inverse primitive 2L-th root for r, preserving integer exponents; generic rational offsets have an explicit root choice.

If one-step covariance is included, construct a unitary T_r on the actual momentum-occupation Fock space, not just an arbitrary `Module.End` with no inverse. A concrete diagonal candidate is

    T_r δ_S = r^(−#S) ζ^(−Σ_{k∈S}k) δ_S.

Its intended action is T_r c_r(j) T_r†=c_r(j+1) within the chosen domain, and T_r c_r(L−1) T_r†=τ c_r(0) at the seam. Its L-th power acts on δ_S as τ^(−#S). For APBC this is the actual occupation parity operator; for general τ it is the corresponding charge-gauge unitary. Conjugation gives an actual star-preserving algebra automorphism and transports region algebras to shifted regions. The automorphism after L steps multiplies annihilators by τ. These are proposed proof obligations, not implemented declarations.

The existing CH06 local algebras generated by c_x and c_x† are unchanged by nonzero scalar rescaling at each selected site. Therefore graded locality alone cannot detect τ. Holonomy becomes visible only when the net is equipped with this extra translation/transport family. This distinguishes the need for a covariant-net supplement from the correctness of frozen CH06.

For A05/CH14 use a source-sector phase

    Z_r(n)|N⟩ = r^n ζ^(nN)|N⟩.

It has the same holonomy τ. The physical field and candidate vertex must share r and orientation, with source/target Klein typing and the full projected-ground-image obligation retained. A matching boundary phase is necessary, not sufficient for the still-conditional finite-band vertex equality. A parity-dependent spin-chain model requires a separate parity-sector Hamiltonian dictionary and a careful treatment of odd fields mapping between those sectors.

## Effect on A03/CH07 before freezing

Their current energy is the periodic linear-label convention. With the same integer labels and sea S_0, shifting every one-particle label to k+β gives

    P_β(S)=P_0(S)+β N(S),
    t_β(N)=N(N+1)/2+β N,
    e_β(S)=P_β(S)−t_β(N(S))=e_0(S).

Thus coordinate excitation budgets, admissible charges, sorted integer-label displacements and frozen occupation margins can be reused after proving this bridge. At centered APBC β=−1/2, t_β(N)=N²/2, which is not always an integer. Do not overwrite `groundEnergy : ℤ` or claim it is the physical APBC charge energy. Add a rational/real physical-energy layer with the integer excitation preserved. This cancellation assumes a uniform linear momentum/energy shift and the same reference occupations. A nonlinear dispersion or different sea is a different problem.

A03's generic support/projection calculus is independent of the boundary phase. CH07's current draft remains a valid proposed periodic reference model; review its physical-energy interpretation before locking. Introducing β directly into all integer arithmetic is unnecessary. Recommended implementation sequence: approve source corrections; draft the additive character/field contract; add the shared-sea physical-energy bridge to the unlocked CH07 scope if desired; optionally add CH06 transport covariance; then use the reviewed contract when drafting A05/CH14. No preexisting frozen module needs rewriting.

## Evidence and limits at the analysis checkpoint

- Current Core sources inspected at `9f56510`; no twist parameter or spatial translation contract found in the field/net definitions.
- Scratch `/tmp/bosonize_boundary_audit.lean` imports `Bosonize` and compiles with warnings treated as errors, empty output. It checks periodicity of the actual CH05 field under an integer lift shifted by L and proves that a nonzero site annihilator cannot equal its negative. This verifies the frozen field cannot simultaneously obey APBC in that lifted interpretation.
- Exact rational finite checks cover 340 configurations for h=1..4 and offsets 0, −1/2, 1/3. They verify P_β=P_0+βN and cancellation of excitation energy using the same sea. They are counterexample screening, not Lean proofs of a future bridge.
- Literature checked from the primary vDS PDF's native text and the cited teaching source. No OCR or source-note edits were used.
- Existing Core hash guard and interface baseline remain intact; the two Phase A drafts remain unlocked. Proposed transport, zero-mode and twist-energy contracts have not been implemented or proved.

## Authorized extension draft

The user authorized a separate CH06 extension. [Ch06Ext](../BosonizeStubs/Ch06Ext.lean) and its [companion notebook](../docs/companion/BosonizeStubs/Ch06Ext.md) now contain 29 complete data declarations and 72 unproved contracts for arbitrary unit phases, integer lifts/winding, Fourier/CAR, covariant transport, holonomy, zero modes, the JW parity dictionary and the real-energy bridge. Both builds and native MCP diagnostics pass with only expected sorry warnings; definitions have no sorryAx dependencies. Eight frozen Core sources and all 271 approved statements/225 commands remain intact against `9734230`. Strict verification rejects the three unlocked Phase A drafts. The earlier implementation inventory describes frozen Core; these new staging statements are not proved yet. The earlier numerical and literature checks remain historical evidence.

Review the extension before locking/Phase B. Source corrections and actual spin-sector intertwiners remain open, and the issue is not resolved by this draft. The bridge is contained in Ch06Ext so existing A03/CH07 interfaces remain available for their own review.
