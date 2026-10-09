# Confirmation of the revised mathematical notes — 2026-10-09

## Decision and scope

The revisions are present, but the claim that all R01–R20 findings have been resolved is not supported by the current files. Several important corrections are sound; several contracts remain incomplete; four direct checks expose false or inconsistent statements. The corpus is **not yet sufficient for the requested transition to a full proof-draft review**.

This is a read-only verification of the mathematical statements in all 21 chapters, appendices A01–A10, their indexes, and the supplied completion log. It compares them with `note/further_changes_review_2026-10-09.md`. It does not evaluate the Lean tactic suggestions or the external proof/stub drafts. A statement marked “addressed” below means that the requested correction is present in the mathematical text; it does not mean that a Lean proof has been supplied or that every downstream use has been verified.

At review time, HEAD is `4b13d5d`. Git reports 33 modified tracked Markdown files: the 21 chapters, ten appendices, TOC, and appendix README. The earlier review note is untracked in `note/`. No tracked Lean sources, scripts, or workflows differ from HEAD. This confirmation adds only this new note.

## Verification of the original 20-item list

| Finding | Status | Confirmation and remaining work |
| --- | --- | --- |
| R01 — Characters and polynomial difference | Addressed | Representative-independent residue characters and transported band operations are stated; chapter 2 distinguishes polynomial forward difference from the function-space operator. |
| R02 — CAR adjoint compatibility | Addressed | The abstract representation now includes genuine adjoint compatibility on an appropriate finite Hilbert carrier, and the concrete occupation construction is identified as its instance. |
| R03 — Sectors, ground states, projections | Partial | Admissibility, ground configurations, diagonal observables, and labelled projections are substantially repaired. The new charge-shift commutator has the opposite sign to its claimed output sector; C01. |
| R04 — Hermite sign and bosonic adjoints | Addressed | The Haldane form, raw-current adjoints, number/energy operators, and positive-sign polynomial recurrence are now specified. |
| R05 — Margins and excursions | Partial | The uniform current margin and additional-excursion convention are explicit. Chapter 11 still replaces the two-mode M2 bound by a one-mode bound without justification; C02. |
| R06 — Whole-budget basis | Addressed | The direct sum over energies and union of partition bases are stated before the extension of Sugawara to the whole budget. |
| R07 — Klein maps and four budgets | Partial | The phase and raising commuting square are improved. The definition and isometry argument still need a consistent completeness contract for the multispecies basis; C03. |
| R08 — Vertex ordering, adjoint, carrier | Partial | The source phase now precedes charge lowering, and the adjoint factor order is corrected. The actual compressed maps, cutoff transitions, and numerical margins are not defined; C04. |
| R09 — Field cutoff and error kernel | Addressed | Chapters 15–16 introduce independent M, no-aliasing, total Sugawara, and a more accurate error-kernel statement rather than asserting that only ground states are annihilated. |
| R10 — Oriented interaction dictionary | Not resolved | The claimed left creator conflicts with the earlier current CCR and vacuum. The raw interaction still yields hopping in the stated computational convention; C05. |
| R11 — Current weights and zero modes | Partial | Extra outer m factors are removed, and the Bogoliubov vacuum shift now matches raw-current normalization. The sea-ordering and chemical-potential conventions needed to derive the zero-mode terms remain unspecified; C06. |
| R12 — Finite states versus abstract CCR | Not resolved | The distinction is now explicit in chapter 19, but the new finite-Fock obstruction theorem is false and its vacuum-moment condition uses the creator; C07. |
| R13 — Parameters and duality | Partial | The formulas for u, g and its reciprocal are corrected. The models, charge/budget correspondence, and duality equivalence are still asserted rather than defined; C10. |
| R14 — Order parameters and exponential scope | Not resolved | Outer projections and the CAR/CCR warning are useful. Both displayed product phases fail a ground-state test; abstract CCR evaluation still uses finite-CAR operators without a defined abstract counterpart; C08–C09. |
| R15 — Two singlet Klein shifts | Addressed | The specific replacement by two different Klein products is present. This does not independently validate the surrounding exponential/product identity, which needs the R14 carrier contracts. |
| R16 — SW baseline and gap | Partial | A10 now requires a self-adjoint block-diagonal baseline and nonresonance on coupled pairs. Its matrix-element definition needs a zero-coupling branch and a block-adapted eigenbasis; C11. |
| R17 — SW order of validity | Addressed | The second-order expression is explicitly modulo t³, with a concrete warning against an exact conjugation identity. |
| R18 — Energy shell versus mode shell | Addressed | The revised decomposition distinguishes removing an energy shell from removing a mode factor, including the K=2 example. |
| R19 — Leakage, RG and gap | Partial | KT flow, thermodynamic gap, and lifetimes are largely separated as physical motivations. Chapter 21 still does not supply the claimed leakage witness; C12. |
| R20 — Indexes, references, status | Partial | Main references and appendix inventory are updated. Some historical criticisms remain in present tense, and the TOC promotes unresolved targets as established results; C13. |

Count: **8 addressed, 9 partial, 3 not resolved**. Partial findings include both small specification gaps and substantive errors; the counts are not an estimate of implementation effort.

## C01 — Reverse the charge commutator, or reverse the output charge

Locations: chapter 7, lemma 7.6, line 111; A03, “Ambient action and budget maps,” line 37.

The text states `[A, N̂] = q A` and concludes that A maps charge N to N+q. With the commutator convention used throughout the notes, `[A,N̂]=A N̂−N̂ A`, this instead gives

\[
 \widehat N A\psi=(N-q)A\psi.
\]

The minimal correction is **`[N̂,A]=q A`** while retaining the target `B(N+q,K+d)`. Alternatively retain the written commutator and change the target to N−q. Apply the same convention in both files.

An exact occupation-basis check confirms the sign: a fermion creator raises the particle charge by one, but `[c†,N̂]=−c†`. Chapter 21's `[N,c†]=c†` convention already agrees with the recommended repair.

## C02 — Supply the joint remainder bound needed by R2

Locations: chapter 11, lines 59–65; chapter 10, theorem 10.4, lines 67–73; A04's Gram contract.

Chapter 11 cites M2 as `M+K_int+|N|≤h`. Chapter 10 requires `|m|+|n|+K_int+|N|≤h` for two unequal modes. The separate facts m≤K, n≤K and K_int≤K yield a conservative 3K bound, not 2K. The current justification therefore does not establish the advertised R2 regime.

This is **not a counterexample to the intended Gram theorem**, and increasing R2 to 3K should not be the first response. Record the stronger, relevant joint bound: when commuting a lowering mode of weight m through a creator of weight n, the commutator acts on the remainder to that creator's right. If this remainder has energy E≤K−n, then

\[
 m+n+E\le m+K\le2K.
\]

State the remainder invariant for every term of the recursive expansion, and handle diagonal M1 separately. Replace the incorrect one-mode M2 citation with this joint argument. The total energy of a whole prefix alone is not the required accounting.

## C03 — Complete the multispecies Klein construction contract

Locations: chapter 13, definition 13.4, lines 48–54; commuting square, line 68; isometry, line 76.

Definition 13.4 uses an unrestricted bosonic partition basis after requiring only charge admissibility. Such a basis is not available for every finite-band charge/cutoff pair. The isometry paragraph cites only the affected species' charge margin, yet claims completeness of the entire multispecies basis.

For the stated unrestricted-partition construction, impose source and target completeness for every species, for example

\[
 \forall\eta,\quad 2K+\max(|N_\eta|,|N_\eta-\delta_{\nu\eta}|)\le h.
\]

Use the corresponding enlarged K+m condition for the raising square. Put these hypotheses in the construction as well as the later lemmas.

An alternative is to construct the map on the affected species and tensor it with identity maps on the others, using their actual finite-band bases. That may need weaker spectator margins, but requires a different explicit construction. The present unrestricted-partition argument does not supply it. The new ground phase and charge-sector anticommutation paths are useful corrections.

## C04 — Define the actual compressed vertex factors

Locations: chapter 14, lines 43–59, 68–78 and 90–95; A05.

The order `E_- E_+ F Z` and reversed adjoint order are repaired. However, saying that every exponential carries explicit cutoffs and a nilpotency bound does not provide those definitions. `expNil_out(W^-)` is still multiplied with a factor acting on the input cutoff without an identified transition map. The phase sums retain h−1, and the main equivalence assumes “verified prefix margins” without a numerical predicate.

Specify, at minimum:

- the sector and cutoff on which each compressed W is an endomorphism;
- the inclusion or projection between the cutoffs after the lowering exponential and before the raising exponential;
- the retained mode cutoff and the nilpotency index of each factor;
- the enlarged budgets and explicit margins used by the matrix-element theorem;
- the corresponding source/target reversal and transition adjoints in the adjoint theorem.

For example, lower on the shifted-charge input budget, project/include into the shifted-charge output budget, then apply the output compressed raising exponential. This is a proposed typing architecture; its equality with projected CAR still needs justification. If K_out<K_in, projecting before the lowering factor can discard states that should first lower into the output budget.

## C05 — The left-branch relabeling does not derive pairing

Locations: chapter 17, raw interaction (17.2), line 22; orientation paragraph, line 36; pairing equation (17.3), line 38; A07, “Two different quadratic models.”

Chapters 9–13 use positive-index density as creator and negative-index density as annihilator, with `[ρ_-m,ρ_m]=mI` on the permitted inputs. Chapter 17 instead labels `C_L=ρ_-m,L`, `A_L=ρ_m,L`. Under the earlier definitions this gives `[A_L,C_L]=−mI`, and the newly named creator annihilates the sector ground state. A07 itself first uses the original positive-index creator and later endorses the incompatible relabeling.

The raw formula still transfers computational k to k+m on R and p to p−m on L. It therefore groups into

\[
 C_R A_L+A_R C_L,
\]

with the original current definitions. Declaring a physical orientation does not change this product into `C_R C_L+A_R A_L`.

An exact check at L=4, h=2, m=1, N_R=N_L=0 gives

\[
 (C_RA_L+A_RC_L)\Omega=0,\qquad
 (C_RC_L+A_RA_L)\Omega\ne0.
\]

A viable repair is to retain the computational left creator `ρ_m,L`, define physical left momentum as the oppositely oriented label, and rewrite the raw physical transfer in computational variables. For a pairing interaction, the computational left transfer must then have the appropriate same-sign shift. Define the physical-to-computational character and transfer maps explicitly and derive the displayed raw formula from them. Alternatively rebuild the left sea/energy/current representation consistently; that entails more changes. Until one dictionary is complete, the hyperbolic diagonalization is a theorem about a separately defined pairing model, not the reduction of the displayed raw interaction.

## C06 — Determine zero modes from a fixed normal-ordering convention

Locations: chapter 17, lemma 17.4 and (17.6), lines 51–73; A07.

The removal of extra outer m factors is correct, and the chapter 18 vacuum shift now has the corresponding single sum of m. The retained m=0 interbranch charge term is also explicit.

The raw quartic sea-ordering operation and the value of μ₄ are still not defined sufficiently to derive the proposed zero-mode expression. State the ordering relative to the chosen sea, the precise subtractions, the relation between μ₄ and μ, and whether the vacuum constant has been removed. Then calculate the charge polynomial from that raw convention. Introducing an unspecified chemical potential does not by itself verify the factorization.

## C07 — The new finite-Fock obstruction theorem is false

Locations: chapter 18, theorem 18.8, lines 89–93; TOC chapter 18 entry.

The theorem quantifies over the entire finite Fock space and forbids a common nonzero bare/dressed vacuum when s≠0. The empty occupation ket δ_∅ is a counterexample. Every nonzero density is a sum of `c†_j c_k`, and each summand annihilates δ_∅. Thus both positive and negative densities, and every dressed linear combination, annihilate this nonzero ket. The fully occupied ket supplies another boundary example.

The intended obstruction can be stated on a **nonvacuous current-action regime**. Require at least one retained m>0, s≠0, and scalar CCR on the candidate input. If bare and dressed annihilators kill it, the Bogoliubov relation forces the relevant creator to kill it too; applying `[A,C]ψ=mψ` then gives ψ=0. The current-action hypothesis excludes the empty/full boundary sectors. The theorem cannot be globalized to finite Fock.

Also replace the abstract vacuum condition written in line 93. Positive-index `tildeρ_m` is a creator; `ω(tildeρ_m† tildeρ_m)=ω(A C)=m`, not zero. The lowering vacuum condition is

\[
 \omega(\tilde\rho_{-m}^{\dagger}\tilde\rho_{-m})
 =\omega(C A)=0.
\]

Chapter 19's two-sided annihilation conditions use the correct lowering convention and should remain the reference.

## C08 — Both chapter 20 ground phases need correction

Locations: chapter 20, lemma 20.2, equations (20.3)–(20.4), lines 24 and 27.

With chapter 14's corrected source phase, annihilation in sector N contributes ζ^(Nx), while creation from sector N to N+1 contributes ζ^(-(N+1)x). Consequently the ground-to-ground character of `c_R† c_L`, with the Klein product kept in the written order, is

\[
 \zeta^{(N_L-N_R-1)x},
\]

whereas (20.3) has ζ^((N_L−N_R)x). For `c_R c_L`, the character is

\[
 \zeta^{(N_R+N_L)x},
\]

whereas (20.4) has the opposite sign. Any differently oriented physical left field must first be explicitly distinguished from the computational `c_(L,x)` in definition 20.1; it cannot be substituted silently.

An exact occupation-number calculation checks these differences with L=4, ζ=i, species R before L, and band order −1,0,1,2. Use ground source and target budgets of cutoff zero, so the displayed normally ordered phase exponentials have ground coefficient one:

| Product at x=1 | Source charges | Target charges | Actual CAR coefficient | Coefficient from displayed formula |
| --- | --- | --- | --- | --- |
| CDW | (0,0) | (1,−1) | i/4 | −1/4 |
| SC | (1,0) | (0,−1) | i/4 | −i/4 |

The chapter 13 Klein signs are included on both sides. These are phase failures, independent of the separate question of full excited-state exponential identities. Correct the source/target zero-mode action first; then rederive the ordered oscillator factors and any contraction constants. Do not assume that changing these two characters alone proves the entire lemma or its later correlators.

## C09 — Define abstract CCR/Weyl order parameters separately

Locations: chapter 20, definitions/theorem 20.1–20.4, lines 7–55; A08, line 98; chapter 21's bosonized products.

Definition 20.1 defines operators in the finite CAR representation. Theorem 20.4 evaluates those same symbols with a functional on an abstract CCR algebra. The warning distinguishing finite CAR from abstract CCR is correct but does not define an operator in the functional's domain.

Introduce separately named finite-CAR and abstract vertex objects. Choose the abstract carrier: polynomial CCR words, formal series with a coefficientwise evaluator, or a specified Weyl algebra with its Gaussian state. A polynomial word algebra does not automatically contain exponential vertices. A finite polynomial exponential is not automatically a scalar Gaussian exponential; repair A08's sentence claiming such an evaluation.

Give the required state, zero-mode/Klein extension, exact C₀ and C₀′ definitions, and a normalization at coincident points. Then formulate the abstract vertex correlator there. State any finite-model comparison as a separate result with its own projections and errors. Restricted CAR identities alone do not supply that comparison or the state extension.

## C10 — Construct the dual models and map

Locations: chapter 18, definition 18.5; chapter 20, theorem 20.5, lines 71–78; A09.

The reciprocal parameter identities are sound: `(c−s)(c+s)=1` gives `(c−s)²(c+s)²=1`. However, saying “we define” a model equivalence does not specify its action or inverse.

Define what a model contains, including the carrier, orientation, charges, cutoffs, Hamiltonian zero-mode convention, and state when correlators are included. Specify the transformation of the fundamental generators, the charge lattice and parity constraints, the source/target budgets, and the inverse. Prove that it respects the chosen relations and adjoint. Only then state the Hamiltonian and order-parameter identities on those actual objects. This does not require finishing all proofs before reviewing tactics, but it does require a definite target rather than an undeclared equivalence.

## C11 — Finish the SW generator's piecewise definition

Locations: A10, lines 35–74; completion log's “if and only if” assertion.

A10's new baseline and second-order scope are substantial improvements. Its nonresonance assumption applies only to nonzero coupled pairs; an uncoupled cross-block pair may have equal energies. The displayed ratio is nevertheless prescribed for every cross-block pair, allowing 0/0. Define its value as zero when the coupling is zero and use the ratio only for nonzero coupled pairs. Also select an eigenbasis adapted to P⊕Q; commuting projectors allow this choice even when eigenspaces are degenerate.

The document correctly states the implication `PVQ=QVP=0 ⇒ S₁=0 ⇒ zero correction` for its off-block generator. The pasted log claims an “if and only if” which is neither in A10 nor generally valid for the second-order projected correction. For example,

\[
 H_0=\operatorname{diag}(0,-1,1),\quad
 P=\operatorname{diag}(1,0,0),\quad
 V=\begin{pmatrix}0&1&1\\1&0&0\\1&0&0\end{pmatrix}.
\]

All nonzero cross-block couplings are nonresonant. The two opposite energy denominators cancel in `P[S₁,V]P`, making that correction zero despite nonzero PVQ. Retain the forward implication. Vanishing of all higher-order corrections is a different claim and is not established by this cancellation.

## C12 — Supply the leakage witness or state a conditional criterion

Locations: chapter 21, theorem 21.7, lines 85–91; A10, line 127; TOC chapter 21 entry.

The revised theorem assumes a witness at the charge boundary whose matrix elements survive both Pauli exclusion and the spatial sum, but does not give that configuration, its parameters, or its coefficient. The pasted completion log's claim to have proved an explicit witness is therefore unconfirmed.

Choose an admissible h, K and charge box, specify occupations S in the box and T outside it, and calculate a nonzero coefficient `⟨T,H_U δ_S⟩`. Include momentum conservation from the spatial sum: a nonzero individual O_U(x) action can disappear after summing x. Alternatively rename the result as a conditional leakage criterion with the nonzero outside component as a hypothesis, and keep witness existence as a separate unresolved lemma.

The separation of KT flow and a thermodynamic Mott gap from finite leakage is correct and should be retained. Nonzero charge shift by itself does not prove leakage from every chosen budget.

## C13 — Synchronize historical notes and validation status

Locations: TOC opening and chapters 18–21; appendix README; A06 line 55; A02's discussion of the chapter 8 normal-ordering carrier.

The TOC opening still promises that all claims are exact identities on finite-dimensional or algebraic spaces, while later targets now deliberately include unspecified Weyl-state and model constructions. Describe the distinction between verified finite targets, abstract targets, and physical motivations without treating all displayed theorems as established.

The README's new reference status is acceptable as an inventory, but should not imply mathematical approval of every interface. Mark unresolved items and use the present confirmation as an audit record. Label remaining critiques of earlier chapter formulas as historical or update them to the actual revised statements. In particular, A06's present-tense statement about missing factors in chapter 15.10 should be checked against the revised formula.

## Evidence and preservation

The direct checks used the finite occupation basis, lexicographic CAR signs, and Gaussian rational coefficients (pairs of rational real/imaginary parts), with ζ=i at L=4. They verified the charge-commutator sign, the empty-ket counterexample, hopping versus pairing on the joint ground, both projected order-parameter ground coefficients, and the 3×3 SW cancellation. These are independent algebraic checks, not Lean proofs.

Both read-only freeze checks passed:

```text
python3 scripts/guards/stub_lock.py --check --strict --baseline-ref HEAD
[stub_lock] Verification PASSED: 52 statement(s) and 54 frozen command(s) verified.

python3 scripts/guards/core_lock.py --baseline-ref HEAD
[core_lock] Verified 2 complete Core source file(s).
```

Guard success verifies the frozen files against their contracts; it does not validate the revised mathematics. No build was needed to check Markdown-only edits, and no new Lean compilation or LSP validation is claimed.

A SHA-256 snapshot taken before this verification covers 35 existing Markdown files: the chapter/index files, all appendix Markdown files including `brainstorm.md`, and the earlier review note. A final comparison verifies preservation of those files. The only new repository file from this review is this confirmation note. Nothing was staged, committed or pushed.

## Next review boundary

First correct the concrete false statements and reconcile the interfaces above. Then recheck the R01–R20 table and ground-state tests. The early Fourier/scalar corrections are useful and do not need to be discarded because later interaction/state statements remain unresolved.

The requested proof-draft review has not begun. Its external inventory currently consists of `docs/proof_suggestion/Ch01LatticeBand_GeminiPro.md`, `docs/stub_suggestion/chapter_2_umbral_calculus_core.md`, and `docs/stub_suggestion/chapter_3_fourier_stub_draft.md`, plus inline strategy sections in chapters and appendices. The inventory is not a content review. After the mathematical gate is met, the separate proof-draft change list should check each draft against the settled statements, carrier/adjoint conventions, actual library APIs, prerequisites, margin lemmas and proof order.
