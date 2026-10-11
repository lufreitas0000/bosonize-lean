# CH12 integrated Phase B proof review and Phase C migration review

Date: 2026-10-11. Verdict: **PASS**, with no unresolved mathematical/interface findings. Promotion is approved in principle subject to execution checks below. This report reviews the final integrated staging source; it does not assert that promotion or pedagogical synchronization has already occurred.

Reviewed source: `BosonizeStubs/Ch12Sugawara.lean`.

SHA-256: `24bd8be1167243715b3c4b50d55917581599facdfabf3b53111669b32619bcab`.

Counts: 26 lemma/theorem declarations, three complete definitions, two abbreviations; zero `sorry`/`admit` tokens. No additional top-level proof helpers or weakened headers were introduced. The module status comment now accurately describes completed finite proofs.

Reviewer disclosure: this delegated agent drafted Phase A and supplied the six relative/physical energy proof bodies. It separately reviewed the final integration, including the twenty proof bodies supplied by other agents/root, and performed fresh full-file compiler/axiom checks. Its review of its own six proofs is a second pass, not independent authorship. The parent retains independent integration oversight; this disclosure prevents overstating reviewer independence.

## Compiler and preservation evidence

- Fresh `lake build BosonizeStubs.Ch12Sugawara` completed successfully, 3397 jobs; zero warnings/errors.
- Fresh imported `#print axioms` audit of **all 26 theorem declarations** completed with exit 0. Every declaration reports exactly the permitted set `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or custom axioms. This includes the Sugawara corollaries whose scratch-only dependencies previously contained placeholders.
- `python3 scripts/guards/stub_lock.py --check --strict`: passed 703 statements and 526 frozen commands. Thus headers/data/imports remain the independently reviewed committed `f631d5b` interface.
- `python3 scripts/guards/core_lock.py`: verified all 18 old Core modules. Independently compared the current Core manifest with `f631d5b:docs/spec/core_locks.json`: identical. Recomputed every recorded old source digest: all match.
- `git diff --check`: passed.
- Root additionally reports direct warning-as-error compilation with empty output and completed native Lean MCP diagnostics with empty items/no failed dependencies; those native calls are root evidence, not independently repeated by this reviewer.

## Mathematical scrutiny

**Actual operator and order.** Lines 15–17 define the literal Icc 1 M sum of rho(m)*rho(-m), on the frozen concrete complex Fock carrier. Composition makes the lowering factor act first. Adjoint reversal uses actual CAR adjoints. The inner-product identity exhibits each summand as the squared action of rho(-m), without replacing the operator by a diagonal certificate or assumed positive state.

**Inactive modes and arbitrary cutoff.** `inactive_mode_zero` uses exact grading to force rho(-m)v=0 when m>K. `sugawara_cutoff_budget` (line 71) compares Icc sums and removes only these inactive terms. There is no R2 hypothesis on cutoff stability, no upper-M margin, and no false M≤h−1 restriction. K=0 and M=0 are included when their hypotheses hold.

**Natural zero word entries.** `density_bilinear_word` (line 93) proves its local lowering recurrence for all natural heads n, including n=0. It invokes the actual frozen signed current-action theorem with `m+n+sum(remainder)+|N|≤h`, established by the right-remainder bound and m≤K. For n=0, m>0 ensures the contraction coefficient is zero. No invalid call to the frozen positive-list helper is made. The induction's remainder sum stays ≤K; no constraint on the already traversed left prefix is added. Matching occurrences are restored via global nonnegative-mode commutativity/word erasure, and absent m gives zero multiplicity. This handles words with rho_0 factors without falsely identifying rho_0 with zero or identity.

**Weight and eigenvalue.** `positive_word_weight` (line 144) explicitly separates zero heads, whose weighted contribution is zero. Nonzero heads satisfy 1≤n≤K from the actual natural sum bound. `sugawara_word_eigenvalue` (line 160) first lowers the cutoff to K, then sums the valid active multiplicity identities. Partition specialization uses CH11's actual list sum. No positivity binder was reintroduced.

**Whole-budget extension.** `sugawara_equivalence` (line 214) rewrites membership using the frozen CH11 whole-budget partition spanning theorem, then extends equality by linearity across those actual vectors. The excitation side separately comes from the frozen diagonal ket observable and fixed-energy membership. This is basis-first and does not derive equivalence circularly from an assumed Sugawara commutator.

**Shifted commutators.** `sugawara_signed_commutator` (line 264) transports input B(N,K) under rho_n to B(N,K+n), then embeds into B(N,J) via the explicit inequality K+n≤J. Source and target each have their own R2 margin and cutoff bound. Equivalence is applied to the actual input/output separately, followed by the already proved excitation commutator. The nonnegative wrapper sets J=K+n, including n=0; the positive reference case follows. No global finite scalar CCR or hidden output margin is asserted.

**Integer and physical shifts.** The relative energy proof retains integer charge, exact same-sea subtraction and the integer ground energy N(N+1)/2. `ground_energy_complex` casts the proved integer double identity, avoiding casts through truncated division. Physical relative energy retains βN. `physical_excitation_cancel` (line 319) subtracts the matching same-sea real charge polynomial before its global cancellation; neither absolute energy nor physical relative energy is asserted independent of β. The final physical Sugawara identity retains `physicalGroundEnergy β N`, with no silently symmetrized charge term or unmatched sea.

**Nonzero witnesses.** `sugawara_excited_witness` (line 350) uses rho_m applied to the actual frozen vacuum; `rho_sea_ne_zero` is grounded in CH09's direct sea norm proof. Grading proves its budget membership, the singleton word theorem supplies eigenvalue m, and positive m plus a nonzero vector makes the energy action nonzero. `sugawara_commutator_witness` (line 376) uses the nonzero vacuum in B(0,0), its nonzero raised vector, and the positive commutator corollary. The hypotheses are inhabited (e.g. h=2, m=n=1, K=M=1 for the excitation witness; M=1 for the ground-input commutator witness), so these are substantive witnesses rather than nonempty-budget proxies.

No unsupported analytic completion, infinite cutoff, continuum limit, arbitrary-dispersion result, or easier conditional replacement was found.

## Exact promotion plan review

**PASS for the proposed byte-identical migration.** The source has only the import `Bosonize.Core.Ch11HaldaneCompleteness`; no staging import needs substitution. Therefore the entire reviewed source, including proof bodies and comments, must retain the SHA above after moving to `Bosonize/Core/Ch12Sugawara.lean`.

1. Move the source byte-identically; retain namespace `Bosonize.Ch12`, every declaration and every proof body. Compare SHA before/after.
2. Move only the v2 manifest key `BosonizeStubs/Ch12Sugawara.lean` to `Bosonize/Core/Ch12Sugawara.lean`. Its complete JSON record must compare equal before/after. No command/header/context digest recomputation is necessary or authorized by this plan; all other records stay identical.
3. Extend the complete-source Core manifest with precisely the new path and reviewed source hash. The old 18 path/hash pairs and actual source bytes must remain identical.
4. Move the companion to `docs/companion/Bosonize/Core/Ch12Sugawara.md`, update its proof status, links and audit evidence; retain its useful source reconciliation and mathematical scope. The companion is documentation, so a byte-identical move is not required.
5. Add the new Core import to `Bosonize.lean`; remove the direct staging import from `BosonizeStubs.lean`, which already imports the Core aggregator. Do not create or target a nonexistent `Bosonize/Core.lean` aggregator.
6. Rebuild both library aggregators, repeat all theorem/data axiom checks through the Core aggregator, and run CI plus both guards and guard tests. Obtain separate pedagogical-sync review before Phase C completion. Check the exact migration delta and committed baseline; preserve historical manifests.

This review authorizes no edits to old Core, no manifest-wide regeneration, and no mathematical source changes during the move. If the reviewed source bytes change before promotion, refresh the exact-source audit rather than reusing this SHA as evidence.
