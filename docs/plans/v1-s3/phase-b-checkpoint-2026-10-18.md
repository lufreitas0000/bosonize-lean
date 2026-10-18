# V1-S3 Phase B checkpoint — 2026-10-18

**Historical checkpoint:** superseded by the authorized four-header amendment,
complete Phase B proofs and [Phase C acceptance](phase-c-acceptance-2026-10-18.md).
The partial counts and pending decisions below describe the earlier snapshot.

## Result at this checkpoint

The scheduled resumption completed 16 additional contracts, reducing the
remaining placeholder count from 23 to **7**. The canonical module compiles.
Its 62 theorem declarations include 55 without placeholders; the fresh audit
of all 87 public declarations found 80 with only permitted standard axioms
(or none), exactly seven with `sorryAx`, and no other axioms.

Canonical source: `BosonizeStubs/V1S3FormalDuality.lean`.
SHA-256: `dfff5b3e4e9d10e6e54a7e78406664b57ab22b1d1645b8bd6e0e8a63f140b58a`.
HEAD: `e916155601bed78d637d23a432e70d9671d48227`.
The work remains uncommitted, preserving the pre-existing worktree changes.

Completed in this resumption:

- Polynomial parity compatibility for derivatives, creation and general
  oscillator representation, as local helpers in action transport.
- Syntax evaluation compatibility, joint action intertwining, kernel transport,
  represented-series intertwining and multiplication.
- Joint functional, state-family, series and ordered-product covariance.
- Canonical and simplified Klein D/S reflection and degree-zero charge action.
- Both oscillator-field transformations and degree-zero vertex D transport.

The prior syntax and dressed-generator proofs remain in place. The existing
Bogoliubov proof body was preserved.

## Fresh validation and independent review

- `lake build BosonizeStubs`: passed (3424 jobs); seven placeholder warnings and
  existing proof lint/deprecation warnings remain. This is a development build.
- Strict interface guard against HEAD: passed, 1215 statements and 1240 frozen
  commands. No interface or lock records changed.
- Core preservation guard against HEAD: passed, 37 complete frozen sources.
- Full axiom/dependency closure audit: 87 declarations, seven `sorryAx` results
  matching the seven remaining placeholders, no unexpected axioms.
- Independent native reviewer `/root/s3_syntax_review`: PASS for action/kernel/
  series intertwining and both dressed generators at source hash
  `faf372b1e930a0e256c48cafbfd0d0773e7d05d323e33706d953493255333c01`;
  PASS for the remaining new proof bodies at the canonical hash above.
  Later edits only added downstream proof bodies; the earlier reviewed bodies
  were retained. This does not constitute whole-sprint acceptance.

Machine receipts and complete compiler outputs are in
`.scratch/v1-s3-parity-bridge/resumed-evidence.json`, `all-axioms.log`,
`axiom-summary.json`, and `final-staging-build.log`.

## Confirmed mathematical obstruction

The accepted `duality_vertex_D_contract` is false at coefficient 1.
`vertexWeyl` has one multiset entry at each coefficient. On the right,
`vertexSeriesScalarMul` includes the k=0 and k=1 summands. Scaling a charge
word by zero leaves an entry in the multiset, so the zero k=1 scalar does not
remove that summand. The proposed equality would force cardinality **1 = 2**.

The independent diagnosis produced the compiler-checked theorem
`Bosonize.V1S3.vertex_D_cardinality_obstruction2` in
`.scratch/v1-s3-parity-bridge/Obstruction2.lean`. The supervising agent reran
it successfully; `obstruction-verified.log` reports only `propext`,
`Classical.choice`, and `Quot.sound`. It uses no placeholder contract.

The S vertex statement has the same structural defect. The dressed and bare
normal D statements similarly compare cardinalities 2 and 3 at coefficient 1.
The latter counts were independently inspected, but no separate compiled
normal-vertex negation is claimed here.

## Concrete, reviewed proposal; not integrated

The four-header diff in
`.scratch/v1-s3-parity-bridge/interface-repair-proposal.diff` replaces the
outer Cauchy multiplication by the constant phase series with coefficientwise
`Multiset.map (vertexCoeffScale phase)`. It retains literal multiset equality,
the same phase, the same carriers, and all existing data definitions.

The scratch candidate `proposed-interface.lean` elaborates, still with seven
placeholders, at SHA-256
`1574eb8b3e555cbbde324d0f68ac5f04b30cff363859bb2dfa514a3bda85e200`.
Independent statement review: PASS for this proposed interpretation. The
proposal is not a proof of the revised theorems. Its scalar phase agrees with
the already proved canonical Klein reflections and the ordered correlator
phase `phase(x) * star(phase(y))`.

The user was asked for a specific decision before changing the four locked
statements because the original sprint instructions prohibit redesign and
lock regeneration. Canonical statements, S2/Core and lock records remain
unchanged while that decision is pending. This is a mathematical specification
issue, not a missing tactic or search backend.

## Remaining contracts and next decomposition

1. `duality_vertex_D_contract` — refuted in its current form.
2. `duality_vertex_S_contract` — same cardinality defect.
3. `dressed_normal_vertex_D_contract` — same zero-entry defect.
4. `bare_normal_vertex_D_contract` — same zero-entry defect.
5. `duality_ordered_vertex_adjoint_transport`.
6. `dressed_normal_vertex_adjoint_transport`.
7. `bare_normal_vertex_adjoint_transport`.

If the scoped amendment is authorized, integrate only the four reviewed
headers, amend only their scoped lock records under the existing workflow,
and prove coefficientwise oscillator-exponential/dagger transport. Combine it
with the proved Klein identities, lift through real normal multipliers, and
then derive the three ordered functional transports. Re-run all acceptance
checks, independent proof review and Phase C requirements afterward.

The single wakeup automation has been paused after consumption. No paid
provider or reset credit was used. Hamiltonian transport still lacks an
algebra-valued Hamiltonian and covariance proof; no finite-CAR or physical
interacting-state duality is claimed. S4 has not been started.
