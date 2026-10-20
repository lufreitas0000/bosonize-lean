# V1-S5 Phase C acceptance — 2026-10-19

**Status: S5 Phase C complete and accepted.** Phase B is accepted at
`4e79e55`; source promotion is committed at `7f90a30`. All 43 named theorems
are proved. All 65 explicit source declarations are directly audited through
the Core aggregator, with zero placeholders/warnings and standard axioms only.
The historical Phase B direct audit counted 64 non-abbreviation declarations;
the final inventory explicitly adds the `Budget` abbreviation. No source or
mathematical statement changed in making that audit coverage explicit.

## Exact implementation and scope

The carrier is A05's actual fixed-charge total-excitation budget, with isometric
inclusion `i`. The Hamiltonian is exactly Chapter 17's full bosonized pairing
Hamiltonian including charge and chemical-potential terms, compressed as
`i† H i`. A selected unit eigenvector minimizes its Rayleigh form throughout
the budget. The ambient extension `X ↦ ⟨iψ, X iψ⟩` is normalized and positive.
No ambient ground-state minimality or multiplicativity of compression is claimed.

For `K < q*m`, actual grade-lowering proves `rho(-m)^q` annihilates the budget;
ambient products with final compression and powers of compressed currents are
handled separately. The fixed raw oscillator dictionary has moment
`q! (m s²)^q`, yielding a nonzero-squeeze obstruction. S4's transformed-observable
comparison in a free finite sea is preserved.

At zero charges, `h=8`, `K=M=2`, `vF=1`, `g4=32π`, `g2=30π` and canonical mu,
the derived matrix on the complete normalized partition basis has diagonal
`(π/8)(0,17,17,34,34,34,34,34)` and only off-diagonal entries `15π/8` at
`(0,5),(5,0)`. Its complete spectrum is `(π/8)(17±sqrt(514))`, `17π/8` twice,
and `34π/8` four times. The selected ket is
`(vac-eta*pair)/sqrt(1+eta²)`, `eta=15/(17+sqrt(514))`; its minimum is proved
on the whole eight-dimensional budget. Its two ambient-product moments are
`(1-17/sqrt(514))/2` and `-15/(2sqrt(514))`, strictly different from oscillator
`9/16` and `-15/16` under the fixed S1/S4 dictionary.

## Migration and preservation

See `phase-c-migration.json` for complete before/after SHA256 values. Exactly
four sources move from staging to Core, three dependency imports change,
and four imports enter the Core aggregator. The namespaces, definitions,
theorem headers and proof bodies are otherwise byte-preserved. All 39 prior
Core files/hashes and unrelated v2 records remain unchanged. Four lock records
move, three import-command hashes and 31 induced context hashes change; no
theorem-header hashes change. The Core manifest now has 43 files.

## Completed validation and independent review

- Independent reviewer `/root/s5_review`: Phase A, scoped amendments, complete
  proof/mathematical review and final Phase B acceptance PASS; actual Phase C
  source/import/lock migration and additive chapter/companion review PASS.
- `make ci` PASS at the committed promotion reference: 69 guard tests and
  18 artifact/proof-verifier tests; strict v2 and Core guards; Core build
  (3448 jobs, warnings treated as errors) and staging build (3449 jobs).
- `phase-c-axioms.lean` / `phase-c-axioms.txt`: exact 65/65 explicit declaration
  inventory (`phase-c-declarations.json`); only `propext`, `Classical.choice`,
  `Quot.sound` or no axioms. No `sorryAx` in the S5 audit.
- Strict v2 lock: 1311 headers and 1373 frozen commands. Core guard: 43 complete
  sources. Final committed-reference verification is saved with the receipt.
- `phase-c-ci.txt`, `phase-c-migration.json`, `phase-c-preservation.json` and
  `phase-c-artifact-hashes.json` retain reproducibility and exact byte evidence.

The CI verifier tests intentionally exercise a synthetic `Fixture.value`
containing `sorryAx`; that fixture is not a project declaration. The separate
65-declaration S5 audit contains only permitted standard axioms.

The Chapter 20 addition is exactly the independently approved draft SHA256
`02ec94473e4b0ee3f1e2c8376c419370816af3f11e19cc742f7bb4d06e4986e4`;
its entire preexisting chapter (SHA256
`10534a26007235d7924783cb887bc9cd3eb8ed8ae9de5bdb23c2b51496f48717`)
remains a byte-for-byte prefix. Mathematical exposition and exact declaration
mapping are in the promoted companion.

Stop after S5. No S6, particle-hole, A10 application, finiteQMB integration,
physical-field equality, analytic limits, thermodynamic conclusions, push or
release is included in this acceptance process.


The [promoted companion](../../companion/Bosonize/Core/V1S5FiniteInteractingStates.md)
explains the carrier, conventions, actual proofs and source mapping. The
[adaptive roadmap](../../../adaptative_roadmap.md) lists S6 and the remaining
conditional/closure work. Earlier S5 quota and failed-cleanup checkpoints are
historical; they are superseded by this acceptance record.
