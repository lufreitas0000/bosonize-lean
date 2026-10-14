# CH17 Phase C synchronization and promotion review

## Proved scope

The accepted Phase B sources contain 37 complete theorem proofs and 70 data declarations: A07InteractionsAndBogoliubov has 18 proofs and 34 data declarations; A10DiscreteSchriefferWolff has 11 proofs and 22 data declarations; Ch17LuttingerModels has 8 proofs and 14 data declarations. These are finite occupation-space and matrix results. Their frozen signatures are retained.

A07 proves sea-normal bilinear and quartic identities, the explicit intra-branch correction, the distinction between hopping and pairing channels, actual adjoints, hyperbolic parameter existence and Bogoliubov expansion/commutators on the stated joint budgets. A10 proves the conditional matrix generator and second-order polynomial identities, exact finite counterexamples and energy-shell projection properties. CH17 proves explicit zero-mode energies, the fermionic kinetic/current identity under the sharp budget margin, the chosen Luttinger model equality and a nonzero pairing-ground witness.

## Evidence

Fresh installed-compiler evidence is recorded in `note/webllm/ch17/phaseB-ch17_cycle_b_e8f6ec96.md`, `phaseB-ch17_cycle_b_80e7982b.md` and `phaseB-ch17_cycle_b_0ed0c297.md`. The final batch audits all 107 declarations with warning-as-error compilation: 52 A07, 33 A10 and 22 CH17. Their axiom dependencies are empty or subsets of `propext`, `Classical.choice` and `Quot.sound`; no production `sorryAx` occurs. The negative verifier fixture containing `sorryAx` is an expected regression test.

The accepted Phase B CI runs pass 69 statement-guard tests and 15 artifact/verifier tests, Core and staging builds, the 872-statement/867-command freeze check and the 27-file Core integrity check. Phase B acceptance commits are `85ab5af` (A07), `07f9226` (A10), and `f8bb8f6` (CH17). Phase C starts at `be2584bacf6831a83180217b75116adfd44c1626`; promotion, new Core locks and root-aggregator checks are pending the runner transaction and must be assessed from its fresh output.

The bounded proof-local quartic elaboration budget changes elaborator resource accounting only. The ordinary CAR proof produces a kernel-checked auxiliary lemma and uses no new axiom, native decision procedure or trust bypass. Its default-command compilation and axiom audit passed before Phase B acceptance.

## Pedagogical changes

This candidate updates only the corresponding chapter and two appendices, together with their exact companions. The original exposition, formulas, citations and later-chapter material are preserved. Added constructive-realization sections explain the finite carrier, sea convention, contraction correction, budget restrictions, actual adjoints, scalar zero modes, matrix coefficient calculation and counterexamples in mathematical prose. Earlier proof-strategy proposals remain visible as proposals.

Independent pedagogical review: **PASS**, `/root/joint_ccr`, 2026-10-14. The reviewer compared the three original notes as exact byte prefixes and the three original companions as verbatim historical suffixes against `be2584b`, read the accepted sources and Phase B evidence, and reviewed all seven Phase C files. Resolved findings distinguish polynomial value from coefficient, internal positive-c construction from the exported existential theorem, low-budget discard from exact-energy-shell fixation, and unweighted pairing from weighted pairing requiring nonzero mixing. The changed passages were reassessed; no deterministic findings remain. Promotion and fresh Phase C compiler/axiom/lock checks remain pending. The runner subsequently migrates the three modules and companions to Core, updates imports and freezes the complete new sources. Existing Core sources are preserved.

## Remaining limitations

The finite hopping channel does not become the chosen pairing channel without an additional physical orientation dictionary. The Bogoliubov commutators are budget-restricted, not global finite-dimensional canonical commutation relations or a unitary implementation theorem. The hyperbolic existence conclusion does not by itself construct the stronger positive-c package.

The matrix BCH result is an exact coefficient polynomial through degree two under its explicit algebraic assumptions, not an analytic exponential identity, convergence theorem or remainder estimate. Generic complementary projectors summing to the ambient identity have not been connected to the actual energy-shell projectors, whose sum is a budget projection. The two-by-two witness proves an exact eigenpair, without an ordering theorem for the spectrum. Continuum limits, finite-cutoff unitary diagonalization, physical channel identification and later chapters remain outside this completed finite scope.
