# CH19/A08 Phase C validation — October 16, 2026

## Scope and source identity

CH19/A08 completed Phase B with 62 theorem contracts in two staging modules. The accepted Phase B source hashes were:

- `BosonizeStubs/A08OscillatorStates.lean`: `ed3ef9f87c9be26460004fd52efbdd7f0a2490b544c990cc89e6178f0a97ee35`.
- `BosonizeStubs/Ch19Correlations.lean`: `cc2eee0d9a5c53cf9a9e7b9a48998fd8de90d4b17f8359003b957bb7214e1687`.

The promoted sources are `Bosonize/Core/A08OscillatorStates.lean` (same bytes and hash) and `Bosonize/Core/Ch19Correlations.lean` (`845e95b619fca515b25c2a103071ba1fa0fdfa46ddd12081440ddfbdae902339`). Direct comparison confirms that the only Lean source change is CH19's import of A08 moving from `BosonizeStubs.A08OscillatorStates` to `Bosonize.Core.A08OscillatorStates`. No theorem or data declaration changed.

## Promotion and lock migration

- `Bosonize.lean` imports A08 then CH19. `BosonizeStubs.lean` removes the two direct staging imports and keeps its import of `Bosonize`.
- The v2 lock entries moved from the staging paths to the Core paths. A08's 35 theorem/header hashes and 30 command hashes are unchanged. CH19's 27 theorem/header hashes are unchanged; its second import command hash and dependent context hashes were recomputed. No other v2 lock entry changed.
- `docs/spec/core_locks.json` adds exactly the two promoted source hashes. The prior 31 Core entries are unchanged.
- The machine record `docs/webllm/chapters/ch19.json` now records `C_complete`, the promoted paths and migration hashes. The accepted Phase B receipt remains at `note/webllm/ch19/phaseB-ch19_cycle_b_b8be9c21.md`.

## Fresh build, placeholder, warning and axiom evidence

- `make ci`: passed. The statement-freeze guard ran 69 tests; strict verification passed with 968 statement locks and 1020 frozen commands. The Core guard verified 33 complete files. The Core build completed 3418 jobs; the staging aggregator build completed 3419 jobs. The Web-LLM verifier/audit suite ran 15 tests and CI ended `CI OK`.
- `make lock-check`: passed; strict v2 verification and the 33-file Core lock both passed.
- A second fresh local `lake build Bosonize BosonizeStubs` after migration passed with 3420 jobs. The historical Phase B receipt separately reports 3419 jobs. The only messages were tactic suggestions from existing frozen Core dependencies (`ring_nf` and `abel_nf`); no CH19/A08 Lean warning was emitted.
- `make audit-axioms TARGETS="Bosonize/Core/A08OscillatorStates.lean Bosonize/Core/Ch19Correlations.lean"`: passed; 90 data/theorem declarations were freshly built and audited. All 62 theorem contracts use only `propext`, `Classical.choice`, and `Quot.sound`. The aggregate observed axiom set is exactly those three standard axioms.
- A separate fresh file importing `Bosonize` and printing every CH19/A08 theorem's axioms passed with warnings treated as errors. All 62 theorem declarations were accessible through the Core aggregator and had only the same permitted standard axioms.
- Both promoted sources contain zero `sorry` and zero `admit` placeholders.

## Pedagogical and independent review

The existing Chapter 19 and Appendix A08 expositions were preserved. Scoped constructive-realization sections now explain the actual oscillator polynomial and finite CAR Fock carriers, the positive dressed functional, the exact ordered finite kernel, the compressed-vacuum counterexample, and the limited comparison result.

The notes state only the scalar equality between the Fock ground density kernel and the free oscillator kernel at zero squeeze. They do not identify the oscillator state with a finite-Fock density matrix. General-orientation contraction tables remain CH19-N2 for CH20b; formal vertices, coefficientwise Gaussian series, power laws and continuum limits remain unproved here.

Independent pedagogy review: **PASS** (2026-10-16). The reviewer checked the four-document note/companion diff against both Lean sources and confirmed the state-carrier, finite-comparison, ordered/symmetrized, compression and analytic-scope statements. An initial evidence-count discrepancy was resolved by recording the fresh 3420-job run separately from the historical 3419-job receipt.

Independent import/path migration review: **PASS** (2026-10-16). The reviewer confirmed dependency completeness, aggregator ordering, unchanged theorem/data declaration hashes, the sole import substitution and the exact dependent lock-context migration.

## Remaining mathematical limits

CH19/A08 Phase C is complete within its reviewed scope. CH19-N2 (general-orientation Gaussian/Wick contractions) remains assigned to the separately scoped CH20b package. No finite interacting-state equivalence, formal-series evaluation at `t = 1`, analytic limit or power-law claim is established by these promoted modules.
