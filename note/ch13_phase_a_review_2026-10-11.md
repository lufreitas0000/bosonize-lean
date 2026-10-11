# CH13 Phase A independent review — 2026-10-11

Reviewer: `/root/ch11_gram_probe`, distinct from author `/root/ch12_phase_a`. Inherited available Codex model fallback; Flash/Pro are not exposed. This reviews Phase A data and mathematical contracts, not completed chapter proofs.

## Source binding and verdict

**PASS for Phase A freeze**, bound to final exact sources:

- A05 SHA-256: `320d0252816ec01dff10de1a6e3d7f76a80c7c9e3276043c3c6ea29c6f04a092`.
- CH13 SHA-256: `5a9b5da4a02b0d879baa47128089fa3c7a3cc6edab9accb0d846d111cb43fd4e`.

All 53 mathematical targets reviewed (28 A05, 25 CH13). Source-bound data audit `note/ch13_phase_a_data_axiom_audit_2026-10-11.json` covers all 42 named data declarations, including eight named local order projections, with standard axioms only and no `sorryAx`. The root independently audited the same declarations/hashes; native diagnostics report no errors. Combined build passed with exactly the 53 expected placeholder warnings. All theorem signatures mechanically match their companion Lean blocks. No theorem proof completion is inferred from these Phase A checks.

No draft, Core, or lock edits made by reviewer. No outstanding mathematical revision requested. Current source has the reviewed minimal kernel assumptions: forward basis action needs source R2 only; inverse basis action needs target R2 only; arbitrary-vector range membership needs admissibility of the output sector only.

## Carrier and instance review

A05 retains the ordinary product `σ × Band (2*h)`, hence the actual CH07 species-budget occupation carrier. Its named complete `speciesOrder` and explicit local order projections provide lexicographic CAR ordering without replacing the occupation carrier. `mode_lt_iff` and `preceding_count_split` expose the ordering obligations. All species are quantified over a finite linearly ordered type; the empty-species A05 case gives a one-dimensional empty-product carrier, while CH13's explicit species argument prevents pretending a Klein operation exists there.

`JointPartitions` is a subtype of species-dependent bounded partitions with summed energy at most K. It describes the full total-excitation budget, not a box of independently admissible K-cutoffs. `jointBudget` is exactly the frozen CH07 actual occupation support submodule. `tensorVector` is complete coordinate product data on that actual carrier. Its ket, inner-product, same-species hopping, density action, and creator-word equality are explicit proved targets; they are not supplied as coefficient certificates or assumptions.

## Gram and completeness feasibility

The product Gram weight is `∏ν z(λν)` and contains no charge dependence. Feasibility rests on actual tensor inner factorization and actual word factorization, followed by frozen CH11 single-species Gram. Constructive total-budget spanning expands each admitted occupation fiber in `Ch11.fixed_energy_basis` at its nonnegative local excitation eν. The total-energy condition gives Σeν≤K, and local R2 follows from eν≤K. Tensor expansion then yields exactly admissible summed-energy labels. Linear independence and spanning establish the requested actual joint subtype basis.

Independently compiled scratch `/tmp/Ch13ConfigurationEquiv.lean` gives both configuration/fiber inverse identities, and `/tmp/Ch13SpeciesProbe.lean` constructs the complete algebraic finite tensor-product equivalence plus its pure-ket image. Both passed `warningAsError=true`, with no placeholders. These are feasibility evidence, not completed draft theorem proofs.

## Klein maps, domains, and phases

The kernel is an explicit finite sum of rank-one operators with inverse Gram weights. The inverse uses the conjugate SOURCE phase and reverses rank-one factors. Norm, budget mapping, both inverse identities, adjoint, and a typed surjective `LinearIsometryEquiv` are separate contracts. No ambient unitarity is asserted. Cutoff consistency is restricted to the actual smaller source budget.

The integer phase exponent is preceding actual occupation `Ση<ν(h+Nη)` plus same-species top-annihilation exponent `h+Nν−1`, each once. The exact ground-top CAR action and ground-field coefficient retain these phases and the source Fourier exponent x*Nν. Boundary data remain species-specific external twist families. A single ground-field coefficient is not claimed to prove a full vertex identity.

`pairMargin` controls both source and lowered sectors. Raising and lowering squares use the enlarged K+m margin, and every arrow is a typed actual map with a pointwise identification. The m>0 assumptions are essential: at m=0 the same-species density has eigenvalue h+N, which changes across the Klein shift. Four-sector anticommutation includes all intermediate and final margins and uses the explicit charge-update commuting identity.

The number-shift equation has the correct +δ term on the target observable. Generic ground nonzero targets prevent zero-map isometry certificates. The added `double_kernel_ground_nonzero` target records nonzero successive ground action under all four sector margins. It also correctly permits ν=η when the doubly lowered sector satisfies the stated margin, exhibiting the absence of a universal F²=0 claim. The concrete Fin2,h2,K0,Ns0 witness has opposite nonzero final-ground coefficients in the two distinct-species orders.

## Source fidelity and limits

Reviewed chapter 13 and appendix A05. Drafts implement their finite low-energy Klein scope and preserve the stated same-species phase and four-budget domains. They do not introduce exponential, analytic convergence, full vertex, or Clifford-square claims. The appendix's finite-band vertex obstruction and separate cyclic criterion remain distinct future obligations. Frozen Core modules, including new CH12, are untouched.

Root's exact-integer finite oracle (1384 ground-phase cases and 2176 cross-phase cases) supports checks at small admissible parameters, including negative charges. It is numerical review evidence only, not a universal Lean proof or a completion claim.

Live quota at review: 39% five-hour and 75% weekly remaining; no reset or credits spent.
