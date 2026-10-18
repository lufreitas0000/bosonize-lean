# V1-S2 accepted local validation — 2026-10-18

**Phase C complete.** S2 is accepted within its reviewed formal-series scope.
S3 has not started. This is local acceptance; no push, GitHub CI or publication
is included.

- Promoted source: `Bosonize/Core/V1S2FormalVertices.lean`.
- Source SHA-256: `17cab3f91f38bc218b18cd7a2fe9e2ec8abf13d487096c3c2fca3fdd5c107020`.
- Phase B acceptance commit: `fcd5b45181cd86f141516b79fcfa200272ec5cf3`.
- 39 approved theorem contracts proved; 80 data/type declarations, 119 total.
- Zero placeholders, added axioms, unsafe declarations, linter suppressions or
  compiler warnings. Fresh aggregator audit uses only `propext`,
  `Classical.choice`, `Quot.sound` in every declaration closure.
- `lake env lean docs/plans/v1-s2/axiom-audit.lean`: PASS;
  [exact output](axiom-audit.txt).
- `lake env lean docs/plans/v1-s2/nonvacuity-audit.lean`: PASS. Explicit
  squeezed gains 1/9 and 9; a nonzero constant correlator coefficient 1/4
  at circumference two, for every cutoff including zero.
- `make lock-check`: PASS, 1153 statements / 1211 commands; 37 frozen Core
  files. S2 source moved byte-identically; its 39 header and 85 command
  records unchanged. All 36 prior Core sources, including both S1 files,
  retain their original hashes.
- Strict manifest SHA-256: `f47a305be49eea48684363b8655babe9c8caea1895019f609f62235476da186d`.
- Core manifest SHA-256: `97abfe83045a0ee401229336aa51a372737612ce97cfda625c25621ad0da80ab`.
- `make ci`: PASS, 69 guard tests, both library builds, 18 verifier tests,
  CI OK; [complete output](ci-output.txt), trailing whitespace normalized.
  The deliberate `Fixture.value` sorryAx tests rejection behavior; it is
  absent from accepted S2 dependencies.
- Independent reviews: all earlier proof batches, final normal-prefactor
  proofs/package and promotion plan PASS; actual migration, pedagogy and
  preservation review PASS. See [final B receipt](phase-b-normal-review-2026-10-18.json)
  and [C receipt](phase-c-review-2026-10-18.json).
- Chapter 20 pedagogical update retains all 17 original display equations and
  original links, adds the constructive S2 explanation, and separates formal
  correlators from pending duality and finite-state comparisons.

The normal-prefactor contracts extract the multipliers used in the definitions,
with a twofold scalar Cauchy product in each correlator. They do not additionally
prove a separate creator/annihilator factorization or BCH theorem. The main
Weyl theorem remains coefficientwise; finite CAR identification, evaluation at
one and analytic/continuum statements require separate results.

Earlier failed worker candidates, compiler logs, bounded diagnoses, accepted
scratch ingredients and review provenance are preserved privately under
`/home/lucas/Projects/.agentctl/sprints/v1-s2-finish-20261018/`.
The preceding resumption archive remains at
`/home/lucas/Projects/.agentctl/sprints/v1-s2-resume-20261017-2318/`.
Only scoped task changes are committed. Pre-existing unrelated worktree changes
are preserved. The consumed one-time continuation automation was deleted.
