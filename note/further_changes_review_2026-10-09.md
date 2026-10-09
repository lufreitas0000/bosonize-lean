# Further changes needed after the chapter and appendix revision

Date: 2026-10-09. Reviewed checkout: `3b2f821ae16c36f611316f81ca33001c642593a9`.

## Scope and conclusion

This is a read-only mathematical and interface review of all 21 chapters in `notes/md`, all ten numbered appendices A01–A10 in `notes/appendices`, the TOC, and the appendix index. The appendix files are in `notes/appendices`, rather than `notes/md`. The only repository addition made for this review is this note, in the requested repository directory `note/`.

The review does not assess proof drafts, `docs/proof_suggestion`, or `docs/stub_suggestion`. Inline “Lean 4 Proof Strategy” passages are not used as evidence that a mathematical statement is correct. `brainstorm.md`, earlier refactor proposals, and the previous audit's conclusions are not treated as specifications for the revised text. No chapter, appendix, frozen Core file, workflow, or lock is changed.

Several important repairs are now present: chapter 3 uses field assumptions and separates normalization; chapters 5 and 9 distinguish the bare vacuum energy; chapter 7 uses integer energies; chapters 8 and 14 distinguish ambient and compressed operators; chapter 12 uses an energy-basis route; chapter 15 corrects chirality and the gradient kernel; chapters 19 and 21 restore the missing contraction and the correct species charge shifts.

**Further changes are still needed.** The most consequential issues are the vertex phase/adjoint formulas, interaction normalization and branch conventions, finite-state versus abstract-CCR semantics, spin-singlet Klein factors, and A10's exactness and decimation claims. Some are explicit contradictions; others require a complete definition or hypothesis before a Lean signature can be frozen.

“Correction” below means an equation or assertion is false under the written definitions. “Contract” means the intended mathematics may be sound, but the statement is not yet sufficiently specified. “Editorial” means indexing, references, or scope wording need repair. These findings are not new axioms or proved Lean results.

## Coverage of every chapter

| Chapter | Result of this reading | Relevant items |
| --- | --- | --- |
| [1](../notes/md/ch01_lattice_band_geometry.md) | No new blocker in the band equations. The integer band is asymmetric; the even-length convention and its starting chapter need consistent wording. | R20 |
| [2](../notes/md/ch02_umbral_calculus.md) | No new blocker in the written algebraic identities. Distinguish the polynomial forward difference in (2.14) from the function-space operator; scope the trace obstruction to a nonzero carrier. | R01, R20 |
| [3](../notes/md/ch03_fourier.md) | The ring obstruction and Laplacian sign are repaired. Representative-independent characters and the types of negative/difference indices still need an explicit definition. | R01 |
| [4](../notes/md/ch04_CAR_Fock_space.md) | Concrete finite Euclidean Fock construction is viable. The abstract CAR definition needs the adjoint compatibility field and an appropriate carrier scope. | R02 |
| [5](../notes/md/ch05_fermions_lattice_band.md) | Bare and normal-ordered energy are now consistent. State positive even length where h and the sea are used, even though the sea is defined later. | R03, R20 |
| [6](../notes/md/ch06_lattice_AQFT_net.md) | The distinction between odd subspace and even subalgebra is repaired. The even algebra is not always a proper subalgebra, notably for the empty region. | R20 |
| [7](../notes/md/ch07_vacuum_budget_space.md) | Integer energies and frozen margins are appropriate. Admissible sectors, projection labels, charge preservation, and the wording of zero-energy uniqueness need tightening. | R03, R05 |
| [8](../notes/md/ch08_boson.md) | Formal BCH and compressed boundary terms are distinguished. The vacuum Hermite identification is wrong; adjoint conventions and the bosonic energy definitions remain incomplete. | R04 |
| [9](../notes/md/ch09_density_modes.md) | No new blocker found in the nonwrapping shifts, second quantization, covariance, or stated vacuum norms. Use the common admissible-sector contract. | R03 |
| [10](../notes/md/ch10_Heisenberg_algebra.md) | Exact edge formulas remain a sound route. The combined Kac–Moody statement needs explicit margin hypotheses; excursion conventions must agree across chapters. | R05 |
| [11](../notes/md/ch11_Haldane_completeness.md) | Rectangle counting and the Hall Gram target are appropriate. Prove that the particular R2 bound covers the actual prefixes; do not substitute an unrelated uniform bound. | R05, R06 |
| [12](../notes/md/ch12_Sugawara_construction.md) | The cutoff and shifted-output commutator are repaired. A fixed-energy basis at K does not by itself span the whole budget up to K. | R06 |
| [13](../notes/md/ch13_Klein_factors.md) | Sector isometries replace the invalid global unitary claim. The all-mode intertwining and cross-species compositions still lack complete source/target data and a fixed phase. | R07 |
| [14](../notes/md/ch14_Mattis_Mandelstam_formula.md) | Projection is the right replacement target. The displayed zero-mode ordering and adjoint are incorrect, and the phase exponentials are not yet typed consistently. | R08 |
| [15](../notes/md/ch15_dual_fields.md) | Orientation, Hermiticity, and the exact gradient are improved. The full h−1 cutoff is not compatible with the advertised uniform low-energy current regime in general. | R09 |
| [16](../notes/md/ch16_field_Hamiltonian.md) | The factor four is repaired. Define the total Sugawara cutoff; excited states can also lie in the error kernel. Separate Taylor/RG interpretations from exact identities. | R09, R19 |
| [17](../notes/md/ch17_LL_Models.md) | The intended pairing model is named but not derived from the raw interaction. Extra m factors, missing zero-mode terms, and the asserted exact RG fixed line need repair. | R10, R11, R16–R19 |
| [18](../notes/md/ch18_bogoliubov.md) | Scalar stability and transform direction are improved. The written zero-point shift does not match the weighted Hamiltonian, and finite diagonalization does not supply the claimed partition basis/RG step. | R11–R13, R16–R19 |
| [19](../notes/md/ch19_correlations.md) | Both ordered contractions are now included. Choose and construct a state on one actual algebra; an abstract CCR functional cannot simply be evaluated as a finite-Fock state. | R12, R13 |
| [20](../notes/md/ch20_CDW.md) | D1 is now defined and mapped duality is acknowledged. Global vertex-product and scalar exponential equalities remain unsupported as finite-model statements. | R13, R14, R20 |
| [21](../notes/md/ch21_spinful_models.md) | Raw spin/charge currents, parity, and ±1 species shifts are repaired. The singlet needs two distinct Klein shifts; leakage still does not establish KT flow or a Mott gap. | R15, R19 |

## Coverage of all ten appendices

| Appendix | Result of this reading |
| --- | --- |
| [A01](../notes/appendices/a01_fourier_scalars_and_characters.md) | The character/scalar architecture is appropriate. Carry its representative-independence contract into chapter 3; R01. |
| [A02](../notes/appendices/a02_car_hilbert_and_normal_ordering.md) | Weighted monomial forms and symbol-level normal ordering are useful. Chapter 8 must actually select the compatible dagger convention; R02/R04. |
| [A03](../notes/appendices/a03_energy_budgets_and_filtered_maps.md) | Its projection and composition warnings remain necessary. Several chapter formulas still need its explicit mode cutoff and charge-domain data; R03/R05/R07/R09. |
| [A04](../notes/appendices/a04_density_partitions_and_sugawara.md) | The density/counting route remains sound. Add the fixed-energy-to-budget basis assembly and distinguish historical critiques from current statements; R06/R20. |
| [A05](../notes/appendices/a05_exponentials_klein_and_vertex_scope.md) | Projected matrix elements are a credible target, not a proof of the displayed new formula. Ground phases and adjoints still need correction; R07/R08/R14. |
| [A06](../notes/appendices/a06_chiral_fields_and_lattice_kernels.md) | Explicit M, no-aliasing, and separate asymptotics are good contracts. Chapters 15–16 have not fully adopted them; R09/R19. |
| [A07](../notes/appendices/a07_interactions_and_bogoliubov.md) | It correctly distinguishes hopping and pairing and computes the per-mode vacuum constant. Chapters 17–18 still disagree with those contracts; R10/R11. |
| [A08](../notes/appendices/a08_states_and_correlations.md) | It correctly warns against an impossible compressed vacuum and against replacing finite exponentials with scalar exponentials. Chapters 19–20 still mix those layers; R12/R14. |
| [A09](../notes/appendices/a09_duality_spin_and_umklapp.md) | Its charge-lattice, Klein, leakage, and gap warnings remain relevant. The revised singlet and KT theorem do not yet satisfy them; R13/R15/R19. |
| [A10](../notes/appendices/a10_discrete_rg_and_schrieffer_wolff.md) | The block decomposition is a useful starting point. Its chosen baseline, gap claims, exact second-order equality, mode-decimation interpretation, and physical conclusions need substantial revision; R16–R19. |

## Findings and proposed changes

### R01 — Make characters and the polynomial difference fully typed

**Contract.** Locations: chapter 3, lines 19–40 and equations (3.3)–(3.6); chapter 2, (2.14); A01, lines 15–28.

`x ∈ ZMod L` is not an integer exponent. Also, integer `−k` and `k−k′` need not belong to the centered band. The displayed notation is conventional, but a Lean declaration needs one precise meaning. Define a residue character, or define the pairing on integer representatives and prove invariance under adding L to either exponent. Distinguish ordinary integer subtraction from transported band subtraction. Keep the existing frozen band type and its positive Nyquist convention.

In (2.14), explicitly name the polynomial operator `p(X) ↦ p(X+1)−p(X)`. The function-space difference and this polynomial map are distinct typed objects. This is a documentation/interface bridge, not a request to rewrite frozen Core.

### R02 — Abstract CAR needs adjoint compatibility

**Contract.** Location: chapter 4, Definition 4.1, lines 36–43, and Lemma 4.6; A02, lines 7–36.

The three anticommutation identities alone do not make a pair of independently supplied maps actual Hilbert adjoints. Add `c†_i = adjoint(c_i)` to the representation data, or define the creator by adjoint. Algebraic CAR pairs can be conjugated by a nonunitary invertible map and retain CAR while losing adjoint compatibility.

For a general infinite-dimensional Hilbert V, arbitrary algebraic endomorphisms need not admit Hilbert adjoints. Restrict this abstract definition to finite-dimensional Euclidean V, as the concrete construction already does, or use bounded operators with their proper adjoint structure. State explicitly that the concrete occupation operators satisfy all three CAR identities and instantiate this representation, rather than relying on the representation definition as an assumption.

### R03 — Finish the sector, ground-state, and projection definitions

**Contract / editorial.** Locations: chapter 7, lines 55–84 and 109–110; A03, lines 5–41; later occurrences of `B(\vec N,K)` and `\mathcal B_{K,\vec N_{max}}`.

Specify h > 0, `−h ≤ N ≤ h`, and the actual ground configuration `S_N = {k ∈ Λ* : k ≤ N}`. Outside that charge range, declare the sector zero and avoid claiming a nonzero ground ket. A sorted configuration should use one indexing convention: `s_i`, `g_i = −h+1+i`, with `0 ≤ i < #S`.

The zero-energy assertion concerns a unique **configuration** in each admissible sector; the zero-energy vector space is the one-dimensional span of its ground ket, not a unique vector. Fixed-energy spaces with distinct E are orthogonal, but H(N,E), B(N,K), and the charge-box budget are nested/related spans, not three mutually orthogonal spaces.

Label projections by their full retained subset: `P_{N,K}` or `P_{K,Nmax}`. Define the multi-species excitation convention explicitly—total `Σν eν ≤ K` versus independent per-species cutoffs—and carry that choice into all later margins.

An energy-shift condition alone does not preserve N. Lemma 7.6 must assume charge preservation, or give a target charge `N+q`. Define the diagonal excitation observable `Ê δ_S = e(S) δ_S` and the relative-charge observable once; distinguish them from the scalar functions e(S), N(S).

### R04 — Correct the Hermite statement and choose one adjoint form

**Correction / contract.** Locations: chapter 8, lines 19–27 and 73–78; A02, lines 66–81 and 97.

With `a = D` and `a† = X`, `(D+X)^2 1 = X²+1`. The probabilists' Hermite polynomial is `He₂(X)=X²−1`. Thus the Wick coefficient formula can remain, but its vacuum identification is incorrect. Define `P_n=(D+X)^n 1`, with recurrence `P_{n+1}=X P_n+P_n′`; its formal generating function is `exp(Xt+t²/2)`. If genuine probabilists' Hermite polynomials are wanted, use `(X−D)^n 1` and the corresponding signed contraction formula. The sign convention agrees with the [NIST Hermite generating function](https://dlmf.nist.gov/18.12.E16).

The factorial form makes D adjoint to X. The Haldane form `w(r)=∏m m^{r_m}r_m!` instead makes `mD_m` adjoint to `X_m`. Under the latter, writing both `a†=X` for a=D and `J†=X` for J=mD as genuine adjoints is inconsistent for m>1. Select the form explicitly and rename purely algebraic creation labels where necessary.

Restore explicit energy and number definitions required downstream: `N_b=Σ X_m D_m` and `H_b=Σ m X_m D_m=Σ C_m A_m`, with `C_m=X_m`, `A_m=mD_m` in the current convention. These definitions are described by the roadmap/appendix but absent from the revised chapter's main definitions.

### R05 — Put margins in the theorem statements and unify excursions

**Contract.** Locations: chapter 7, (7.6); chapter 10, (10.7)–(10.8); chapter 11, (11.5); A03, lines 56–79.

The displayed all-mode Kac–Moody equation (10.7) needs its actual hypotheses: M1 for opposite modes and M2 for the unequal opposite-sign case, or an explicit uniform `2M+K+|N| ≤ h` for retained modes. The unrestricted endomorphism identity is false by the finite edge formula itself.

Define the excursion as either the additional upward shift beyond the input K, or the maximum absolute intermediate energy. Chapter 7 writes `2M+K_excursion+Nmax ≤ h`, while chapter 10 adds both K and K_excursion. Both conventions can work, but cannot be used under one undefined symbol.

For the Gram theorem, derive each word-prefix bound from its partition energy. Do not claim that R2 automatically implies an unrelated bound `2M+K+excursion ≤ h` after replacing M by K and adding an extra K. This is a needed supporting lemma, not evidence here that the intended R2 theorem is false.

### R06 — Assemble the whole budget basis before Sugawara extension

**Contract.** Location: chapter 12, lines 30–50; chapter 11, Theorem 11.5; A04, lines 85–97.

Partitions of K span H(N,K), not the entire B(N,K). For K=1, B(N,1) also contains the sector ground ket, which is orthogonal to every energy-one partition state.

Use the disjoint union of partition bases over `0 ≤ E ≤ K`. First prove `B(N,K)=⊕_{E=0}^K H(N,E)`, then evaluate Sugawara at energy E and extend to the union. R2 at K implies the required R2 bounds at each E≤K, and M≥K covers all these states. The repaired shifted-output commutator in Corollary 12.4 can then use this budget theorem.

### R07 — Klein intertwining must specify four sector budgets

**Contract.** Locations: chapter 13, lines 48–67 and 80–84; A05, lines 36–54.

Define `F_{ν,\vec N,K}` with an explicit phase and explicit admissibility proof. “Same-species ground-ket phase” in (13.5) is a placeholder for mathematical data, not a definition.

For a raising density of weight m, (13.6) needs a commuting square involving both K and K+m, in both charge sectors `\vec N` and `\vec N−eν`. The F at cutoff K is not defined on an arbitrary density output. Include the required margins for all four spaces; lowering uses the corresponding integer target cutoff. Matching partition labels alone does not establish intertwining outside the proved action regime.

For cross-species anticommutation, also require the intermediate sectors `\vec N−eν`, `\vec N−eν′`, and the final `\vec N−eν−eν′` to be admissible. Fix the finite tensor/Fock identification and its lexicographic signs before comparing the maps.

### R08 — Repair the vertex zero mode, adjoint, and carrier order

**Correction / contract.** Locations: chapter 14, equations (14.3)–(14.6), lines 27–86; A05's replacement target.

Products act right to left. With the written `Z F`, F first takes N to N−1, so Z contributes `ζ^{x(N−1)}`. The physical ground-to-ground matrix element is

\[
 {}_0\langle N-1|c_x|N\rangle_0
 =L^{-1/2}(-1)^{h+N-1}\zeta^{xN}
\]

for one species with the fixed occupation order. A source-charge-dependent constant Klein phase cannot repair an extra x-dependent factor. For h=2, N=0, both cutoffs zero, ζ=i and x=1, the physical coefficient is −1/2, whereas the displayed ZF with the matching ground sign gives i/2. At these cutoffs both phase exponentials are identities. The ground sectors satisfy the completeness conditions. If a proposed all-mode prefix condition excludes even this test, it needs a separate non-vacuity repair.

For the ground coefficient, `F Z` with Z acting on the source gives the correct phase; alternatively define Z on the target with eigenvalue `ζ^{x(N_target+1)}`. Neither option by itself proves the full vertex theorem: choose one and prove ground matching before the cyclic-basis argument.

The adjoint in (14.5) also swaps the wrong phase labels. Writing `E_- = expNil(W^-)`, `E_+ = expNil(W^+)`, we have

\[
 (E_-E_+ZF)^\dagger
 =F^\dagger Z^\dagger E_+^\dagger E_-^\dagger,
 \quad E_+^\dagger=\operatorname{expNil}(-W^-),
 \quad E_-^\dagger=\operatorname{expNil}(-W^+).
\]

The chapter instead places `expNil(-W^+)` before `expNil(-W^-)`. These factors need not commute. This failure is visible with two-by-two nilpotent raising/lowering matrices and does not depend on a BCH assumption.

Finally, F is applied before the “in” phase in (14.4), so that phase must be defined on the shifted charge sector with the source energy cutoff. Give every exponential its charge, cutoff, inclusion, projection, and nilpotency proof. Specify whether K_out may be below K_in; discarding components before a lowering phase can change the final matrix element. These definitions are prerequisites for freezing (14.6).

### R09 — Use an explicit field cutoff and describe the error kernel correctly

**Contract / correction.** Locations: chapter 15, (15.1)–(15.5); chapter 16, (16.5)–(16.8); A03, lines 66–75; A06, lines 38 and 99–126.

Chapter 15 retains m=1,…,h−1, while A06 uses an independent M with current margins. Under the advertised uniform pairwise condition, the chapter choice requires `2(h−1)+K+Nmax ≤ h`, impossible for h≥3 even at K=Nmax=0. Do not freeze a field theorem under these empty hypotheses. Choose a smaller M and a nonempty budget, or prove a sharper support-specific theorem that actually permits the retained modes. Higher raising modes cannot simply be discarded because lowering modes annihilate the input.

State the field commutators as actions on specified budget vectors, rather than the global identities printed in (15.4)–(15.5). For the spatial square, record the independent no-aliasing condition, e.g. `2M<L`, that removes same-sign Fourier terms. Define the total two-branch `H_sug^(M)` before (16.6), using the same M in the field and reference sums.

The error need not be nonzero on every excited state. With the permitted reference `g0=ε(1)`, all m=1 contributions vanish. An admissible one-mode excitation `ρ_1|N⟩_0` is nonzero but is killed by every lowering mode m>1, so E_error also kills it. Replace the last sentence of Theorem 16.7 with an actual kernel description or a nonzero excited witness whose mode coefficient is nonzero.

Keep the Taylor statement, continuum integral, and RG interpretation outside the exact algebraic theorem; an error estimate with a specified scaling sequence is a separate target.

### R10 — Derive pairing from a defined opposite-branch dictionary

**Correction / contract.** Locations: chapter 17, (17.2)–(17.3); chapter 13, (13.3); A07, lines 22–54.

With the currently defined species densities, the raw opposite transfer in (17.2) factors into

\[
 \frac{g_2}{L}\left[N_RN_L+
 \sum_{m=1}^M(C_RA_L+A_RC_L)\right],
 \quad C_\nu=\rho_{m,\nu},\ A_\nu=\rho_{-m,\nu}.
\]

It does not factor into `C_R C_L + A_R A_L`. Calling the species “Left” does not invert its computational shift. Chapter 15's reversed field character does not silently change the raw transfer formula in chapter 17.

Define the left physical momentum/position/density dictionary and derive its transfer sign, or keep the raw hopping model and use a rotation. If pairing is the target, propagate the oriented dictionary into the raw fermion sums, free energy, position fields, and interaction theorem. A07 identifies this requirement; the new chapter has not yet implemented it mathematically.

### R11 — Remove the extra current weights and determine zero modes

**Correction / contract.** Locations: chapter 17, (17.3)–(17.5); chapter 18, (18.8), (18.11); A07, lines 68–79; chapter 12, (12.1)–(12.4).

For the raw currents `[A_m,C_m]=mI`, `C_m A_m` already has eigenvalue m r_m on a bosonic occupation state. Chapter 12 correctly uses `Σ C_m A_m`. The additional m outside the current products in chapter 17 and chapter 18 changes this to m² r_m. For example, a one-quantum mode-two state has the intended free energy 2 in these integer units, but the newly weighted expression gives 4.

Choose one consistent convention:

- Keep the unnormalized currents and remove the extra m from the interaction and diagonal Hamiltonian sums. This is the square-root-efficient option.
- Define normalized oscillators `b_m=ρ_{-m}/√m`, `b_m†=ρ_m/√m`, and retain the outer m on products of these b operators, not on products of the raw ρ operators.

For one raw mode the Bogoliubov expansion produces `2u s² m I`. With the chapter's extra outer m, the total shift would be `(2π/L)2u s² Σm² I`, not the printed sum Σm. Removing the outer m makes the printed Σm shift compatible again. At u=4, c=5/4, s=3/4 and m=2, these alternatives give 18 versus 9 before the common 2π/L factor.

Also retain or explicitly subtract the m=0 inter-branch term `g2 N_R N_L/L`. Give exact definitions of `E_{4,zero}`, `E_zero`, the chemical potential, and the sea-normal-ordering convention for the raw four-fermion symbol. Naming a correction without defining it does not make (17.4) an exact equality. A02's bosonic normal-order symbols alone do not define fermionic sea normal ordering.

### R12 — Separate actual finite states from abstract Gaussian states

**Contract, with a structural obstruction.** Locations: chapter 18, Theorem 18.8; chapter 19, Definition 19.1 and its note; A08, lines 5–44.

Define the actual star algebra, complex linearity, normalization, positivity, and state existence before assigning vacuum rewrite laws. Chapter 19 starts on an algebra of budget observables but then suggests an untruncated CCR functional “before applying it to finite-Fock evaluations.” Such an application requires a comparison construction; it is not a canonical operation.

There is no unital representation of exact nonzero scalar CCR in a nonzero finite matrix algebra in characteristic zero. Consequently an abstract CCR quotient cannot simply be sent to the compressed finite current algebra while preserving all its defining relations. A08 correctly warns about this obstruction.

Keep two explicit models: a finite Hamiltonian with its constructed ground vector/density matrix and boundary corrections, and an abstract CCR algebra with a constructed positive quasi-free state. Put the corrected mode contractions in the latter, or prove precisely which finite moments agree. Change the title “Ground State Existence” in chapter 18 to a real existence theorem for a specified self-adjoint finite Hamiltonian, or mark its present paragraph as an obstruction/discussion rather than a theorem.

### R13 — Define g, all model parameters, and the duality map

**Contract.** Locations: chapter 18, Definition 18.5; chapter 19, line 50; chapter 20, (20.6)–(20.9); A09, lines 5–13.

The revised chapter 18 defines u,c,s but no formula for g or K_L. Chapters 19–20 use both names. In the stated plus-sign scalar convention, a possible choice is `g=(c−s)²`, with reciprocal `(c+s)²`; prove positivity and derive its relation to v1,v2 before identifying it with the physical Luttinger parameter. Keep this name distinct from the excitation cutoff K.

`H_Lutt(g)` is also underparameterized: u, chemical potentials, zero-mode energies, cutoffs, and the model carrier matter. Define the parameter record and a transformation of that full record. Construct the proposed duality on actual generators and mapped charge/energy domains, checking whether each order parameter maps to the other, its adjoint, or a signed variant. A field-name exchange does not define that map.

### R14 — Projected fermions do not justify the global CDW formulas

**Correction / contract.** Locations: chapter 20, equations (20.3)–(20.7), lines 21–57; A03, line 60; A08, lines 93–101.

The revised chapter 14 supplies a projected matrix-element target, but chapter 20 again writes global vertex equalities with unspecified exponentials. Inserting intermediate projections into a product changes it unless the discarded part is proved unable to return: `P A P_mid B P` need not equal `P A B P`. Give the composition budgets and define all exponential carriers. Formal BCH in an auxiliary parameter cannot be evaluated at t=1 without an evaluation/convergence theorem, and compressed expNil does not inherit scalar BCH.

A concrete finite free-model check shows why adding an unspecified constant C0 is insufficient. Take the current identical-species CAR realization with L=4,h=2, both seas {−1,0}, s=0, and `O(x)=c_R†(x)c_L(x)`. Direct eight-mode occupation-basis evaluation gives

\[
 \langle\Omega|O^\dagger(0)O(0)|\Omega\rangle=\tfrac14,
 \qquad
 \langle\Omega|O^\dagger(1)O(0)|\Omega\rangle=-\tfrac18.
\]

For the proposed free g=1, M=1, ΔN=0 formula, the coincident value fixes C0=4, while the next-site prediction is `e^(−2)/4`, positive and different. This tests the written finite fermions, not a separately defined oriented/infinite CCR model. Changing the left dictionary or the state requires an explicit new comparison; even the magnitudes need verification.

The scalar Gaussian exponential may be an appropriate theorem in an abstract vertex/Weyl model with all phases and zero-mode expectations fixed. It is not established as the exact finite CAR observable by the present definitions. Compute C0 and C0′ from specified Klein/zero-mode states, rather than choosing them to absorb an arbitrary discrepancy.

### R15 — The singlet needs two different Klein charge shifts

**Correction / contract.** Location: chapter 21, equations (21.5)–(21.6), lines 44–54; A09, line 61.

The first singlet term lowers `(R↑,L↓)`; the second lowers `(R↓,L↑)`. These outputs have different species-charge vectors. The single factor `K_SSC=F_{R↑}F_{L↓}Z_{R↑}Z_{L↓}` has only the first shift. Spin density exponentials preserve every species charge, so a difference of those exponentials cannot supply the missing second shift.

Retain two terms with their own Klein products and phase orders. Alternatively define Ψ_spin to include a rigorously constructed zero-mode shift converting one target sector to the other; then it is not merely the stated difference of spin-field exponentials. Define this residual operator completely. Carry the total-energy constraint and parity sublattice into the charge/spin carrier decomposition.

### R16 — A10 needs a valid solvable baseline and a proved spectral gap

**Correction / contract.** Locations: A10, lines 26–51; chapter 18's budget-only diagonalization.

The interacting pairing Hamiltonian is not diagonal on the bare Haldane partition basis. Its `C_R C_L` term sends the bare joint ground ket to a nonzero two-branch excitation whenever the coupling is nonzero and the band permits it. A scalar Bogoliubov identity on selected inputs does not construct a global eigenbasis of the compressed Hamiltonian. Therefore A10 cannot take `H0=H_Lutt` and simultaneously assume its eigenvalues on those bare partition labels.

Define a self-adjoint H0 with proved `PH0=H0P`, a real eigenbasis, and nonresonance between connected P and Q eigenstates. The denominator equation is valid under that contract and self-adjoint V; its nonzero gap is not automatic from the excitation shell when charge-dependent energies or different velocities are present. At a cross-block degeneracy, `[S,H0]=-V_off` can be impossible: H0=I and nonzero V_off is an immediate two-dimensional witness.

The physical gaps `(2πu/L)(E−E′)` are real, not generally rational. They may be algebraic in a chosen scalar parameter after rescaling units, but rationality is an additional assumption. A positive single-step gap also does not give a regulator-independent lower bound as L increases.

### R17 — The second-order SW formula is not an exact conjugation identity

**Correction.** Locations: A10, lines 42–63; chapters 17 and 18's RG conclusions.

Solving `[S1,H0]=-V_off` supplies the first-order generator. For `H(t)=H0+tV`, the exact conjugation has higher nested commutators. A10's equality

\[
 H_{eff}=PH0P+PVP+\tfrac12P[S,V]P
\]

is generally a second-order expression, not the entire effective Hamiltonian. Cancelling the linear off-diagonal term is correct; it does not cancel all higher orders.

An exact formal coefficient witness uses

\[
 H0=\begin{pmatrix}0&0\\0&1\end{pmatrix},\quad
 V=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
 S1=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\quad
 P=\begin{pmatrix}1&0\\0&0\end{pmatrix}.
\]

Here `[S1,H0]=-V` and S1 is anti-Hermitian, but

\[
 P e^{tS1}(H0+tV)e^{-tS1}P=(-t²+t⁴+\cdots)P.
\]

The remaining off-diagonal coefficient at order t³ is −4/3. The second-order expression supplies only −t²P. At t=2/3 the exact lower eigenvalue of H0+tV is −1/3, whereas the second-order value is −4/9.

For a purely algebraic target, state an exact equality **modulo t³** in a truncated formal-parameter algebra. For an actual finite-matrix approximation, define the matrix exponential and prove a remainder estimate with gap and coupling bounds. For exact block diagonalization, construct the full transformation/spectral subspace map instead of using only S1. A nonzero anti-Hermitian finite matrix is not nilpotent on a positive Hilbert space, so expNil is not a generic substitute for its exponential.

This distinction between exact SW and its perturbative expansion is also made in the primary [Bravyi–DiVincenzo–Loss paper](https://arxiv.org/abs/1105.0675); the counterexample above establishes the issue directly for this review.

### R18 — An energy shell is not a mode-decimation shell

**Correction / contract.** Locations: A10, lines 11–19; chapter 17, Theorem 17.6; chapter 18, Theorem 18.9.

`B_K=B_{K−1}⊕H_K` is an energy-shell decomposition, with K≥1 and a fixed charge-domain convention. It does not mean “delete the highest mode K.” For weighted boson modes 1 and 2 at K=2, B₂ has basis `{1,X1,X1²,X2}`. The energy projection to B₁ keeps `{1,X1}`; deleting mode 2 keeps `{1,X1,X1²}`. These are different subspaces and different projections.

Define the RG map, currently named E_K but not constructed. If the goal is mode-factor decimation, identify an actual factorization and specify the state/projection on the removed factor; a total-energy budget is generally not that tensor product. If the goal is energy-shell SW, prove the needed blocks and do not call it mode decimation.

An exact no-correction theorem is available under the explicit assumption `PVQ=QVP=0`: the off-block perturbation vanishes, so its SW correction vanishes. Quadratic syntax alone does not establish those conditions for the selected finite budget. A fixed-line statement also requires a parameter map and a comparison/rescaling convention across steps.

### R19 — Leakage and a second-order commutator do not prove KT flow or a gap

**Correction / contract.** Locations: chapter 21, Theorem 21.7, lines 81–83; A10, lines 70–82; chapter 16, lines 87–96; A09, lines 88–95.

Species charge shifts are now correct, but they do not imply that every boundary vector leaks: Pauli exclusion can kill a term, couplings can vanish, and a sufficiently large budget can contain the entire finite carrier. Supply a specific nonzero witness, nonzero coupling, and a no-cancellation argument for the spatial sum.

Failure of invariance under the chosen budget projection does not forbid another block diagonalization. A finite Hermitian Hamiltonian is diagonalizable. Its exact finite level gap is also not by itself a thermodynamic Mott gap.

To claim KT flow, define the running parameter space, the decimation/rescaling map, its controlled truncation order, and the coefficient calculation showing closure or an explicit remainder. A product of vertex operators need not reduce to only quadratic densities; higher words and zero modes must be accounted for. To claim a physical gap, specify the Hamiltonian family, parameter regime, spectral quantity, and the uniform or scaling result being proved. No such theorem follows solely from sector leakage or the displayed second-order matrix commutator.

A10's cubic curvature term, effective interaction coefficients, and plasmon lifetime are likewise not derived. A Hermitian finite Hamiltonian has real eigenvalues; a decay lifetime requires an additional dynamical, limiting, or operational definition. Keep these as research motivations until their contracts and calculations exist.

### R20 — Repair stale references, indexes, and exactness wording

**Editorial.** Locations: TOC, appendix README, chapter 8 line 46, chapter 20 lines 22 and 50, historical critique paragraphs in A04–A09.

- The appendix README still lists nine appendices and omits A10. Its statement that the original chapters were preserved describes the first audit, not the present revised corpus.
- Chapter 20 refers to Theorem 14.7 and Lemma 8.8; the revised projected theorem is 14.5 and formal BCH is 8.5. Chapter 8 refers to Lemma 2.9, absent from the current chapter text; link the actual Core trace result or restore the correct note reference.
- The TOC still promises a fixed-budget AlgEquiv, exact lattice power-law decay, continuous field derivatives, and unrestricted spin/charge factorization despite the revised chapter scopes. Update it to match the actual mathematical targets.
- Label appendix statements such as “chapter 17 currently defines a hopping form” and old equation-number criticisms as historical, or rewrite them against the revised equations. The old audit and source-hash inventory remain historical snapshots, not evidence about the new sources.
- Make the positive-even-length starting point consistent. Chapter 1 says chapter 6 onward, chapter 7 says chapter 7 onward, while chapter 5 already uses h and a half-filled sea. The lattice representatives are not reflection-symmetric.
- In chapter 6, say “even subalgebra,” not “strict/proper subalgebra” without a nonempty-region hypothesis. In the zero-mode obstruction, restrict the delta cutoff so no nonzero multiple of L is counted as another zero residue.
- A purely algebraic formal-series identity is consistent with the foundational scope. Taylor approximations, scalar analytic exponentials, continuum integrals, RG flows, and thermodynamic gap claims need explicit separate status. Descriptive physical intuition must not be promoted to an exact finite theorem merely by naming it “Theorem.”

## Recommended order of further revision

1. Finish the chapter 3 character contract in R01. The two-stage Fourier strategy remains appropriate; this review identifies no reason to discard it.
2. Set one notation/carrier/adjoint convention and the complete sector/projection definitions: R02–R04.
3. Finish margin and budget-basis contracts: R05–R07. These support later theorems without reopening frozen chapters 1–2.
4. Correct and test the vertex ground coefficient, adjoint, and composition domains before freezing chapter 14: R08.
5. Select an explicit field cutoff, physical left-branch dictionary, and one raw-current normalization: R09–R11.
6. Choose the state model and define the full Luttinger parameter record. Then repair order-parameter products, duality, and singlet Klein terms: R12–R15.
7. Rewrite A10 as a precise formal-order or analytic SW construction. Resolve its baseline and shell first; keep KT/gap/lifetime conclusions as separate targets until supported: R16–R19.
8. Synchronize references and the roadmap: R20.

## Evidence and limits

The review used direct algebra and small exact computations: formal rational matrix coefficients through degree four for SW; a rational two-by-two nilpotent-matrix adjoint check; a direct polynomial recurrence; a ground-to-ground CAR phase calculation; an eight-mode CAR CDW calculation over Q(i); and enumeration of the K=2 energy/mode retained sets. These establish concrete failures or distinctions, not Lean proofs of the full revised chapters. The mode-weight correction follows by direct expansion using `[A_m,C_m]=mI`.

No proof draft was validated, no new Lean interface was written, and no chapter build is claimed. Assertions not contradicted in this first reading are not thereby certified. In particular, the detailed Gram/rectangle/vertex induction and future Gaussian-state existence still require their own formal proofs.

SHA-256 comparisons before and after the review verify that all chapter and appendix inputs are unchanged. The checkout began clean; the only new repository file is this review note. No commit or push is part of this read-only analysis request.
