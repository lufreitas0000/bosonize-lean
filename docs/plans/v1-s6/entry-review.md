# V1-S6 entry review: physical fields and controlled residuals

Date: 2026-10-20. Status: entry review complete; Phase A interface independently reviewed; a scoped lock is established for Phase B. The two concrete lower-bound proofs remain open.

## Phase A interface re-review receipt

- Reviewer: `/root/s6_theory_review` (independent native diagnosis agent).
- Verdict: **PASS**, limited to the interface, typing, coverage, and data
  nonvacuity; this does not approve proofs or promotion.
- Exact reviewed hashes: Lean staging source
  `932467d4e23cc90dd0824dcfca310efa16c43ca728715cce2461b50e125dae90`;
  companion `9711a23a928cada4d1387b79c7184a2cd4d9f4f8d6d86ece86209a4e1ceed63c`;
  entry receipt `c77f5f2a417e954da2602c406c7c1ea060890e8d322ff98ab9fce5137685e894`;
  revised S0 dictionary `79b3df2401497cb7e285545dda86c6cba6456ed9bf1f1624663a93c263c3ed55`.
- Findings and resolutions: the explicit ambient orthogonal-projection data
  and range-inclusion hypothesis validate the omitted-range term; the exact
  actual-minus-candidate finite dictionary error and the h=3 ground-vector
  lower-bound contract close the earlier mode/error-ledger gap without
  claiming a mode-only cause; state and dispersion errors are absent only for
  the selected fixed-operator comparisons. All terms have the stated finite
  carriers and composition order. No hidden axiom or vacuity defect was found.
- The reviewer confirmed the CH20 `1/4` target from its unique witness
  coordinate. Both concrete lower bounds remain Phase B proof obligations.
- The review preceded proof work. Current Lean source hash has changed and is
  tracked separately below; it is not represented as the reviewed hash.

### Phase B current source identity

The first typed decomposition proof was added after the interface PASS. Current
Lean staging hash: `6e01a5ccf9fd94c4a3da0ad4246cc8649a6d9c5e7f410ffed5d2b81e67cf2e96` (refresh after each substantive proof batch).
The interface approval does not validate proof correctness or unlock promotion.

## Independent review receipt

- Reviewer: `/root/s6_theory_review` (independent native diagnosis agent).
- Scope: S0 physical-field proposal; accepted CH14, A05, CH07, A05FiniteExponentials,
  CH13, CH20, S2, S4 and S5 declarations. The reviewer did not edit sources.
- Reviewed exact hashes are recorded below. The physical-field analysis and
  source definitions were inspected directly; S5 results were checked at the
  declaration/result level.
- Verdict on the proposed `h=2, M=0` full-ground-image obstruction: **PASS**.
  The obstruction is valid. The prose swaps the two hole labels: deleting
  `k=0` gives the target ground configuration, while deleting `k=-1` gives the
  distinct excitation-one state. Both survive `Kout=1`; at `h=2` each
  coefficient has magnitude `1/2` for trivial twist and `x=0`.
- The statement is parameterized over every `h≥2` at `N=0`, `Kin=0`,
  `Kout=1`, `M=0`, `x=0`, trivial twist. The two retained hole coefficients
  have magnitude `1/sqrt(2h)`; both source and lowered-target `r2` margins hold.
- Findings/resolutions: (1) correct the hole labels in the S0 analysis; (2) do
  not infer field equality from margins; (3) preserve the distinction between
  actual `physicalMap`, CH14 `vertexCandidate`, and S2 coefficientwise formal
  `vertexWeyl`; (4) do not claim an `M>0` obstruction from this review.
- Nonempty mode cutoff: not established by this entry review. It remains an
  explicit Phase A investigation item at the time the entry verdict was issued.
  A subsequent independent calculation is recorded below; it must be included
  in the reviewed Phase A statement before it can be locked.

### Exact source hashes in the entry review

| Source | SHA-256 |
|---|---|
| `docs/plans/v1-s0/physical-field-dictionary.md` | `b534a48ef5998dacc051164ef586c8b78b85a60be20ab180926ee531dcfe970c` |
| `Bosonize/Core/Ch14Mandelstam.lean` | `0d3feed562023e5d8a20027021014cc56512d636b58848fa7a8122b61cc320fc` |
| `Bosonize/Core/A05MultiSpecies.lean` | `bb9055adcf9358d5f2274666205d31dc3073716fe53e5f6bf02a983f92335bc2` |
| `Bosonize/Core/Ch07VacuumBudget.lean` | `a33ced1009ba31a3823dfe3e1a922a346e62591d7b5d5c1803f6382fe14944da` |
| `Bosonize/Core/A05FiniteExponentials.lean` | `57d36818adb50f3f981c14191e786efce2d9d1eed872313110f9dd00a392aee5` |
| `Bosonize/Core/Ch13KleinFactors.lean` | `9a4a7ed40e514a5e57345ad731f23c967b4e725e388d5d9b7b6c2d36a65f5c32` |
| `Bosonize/Core/Ch01LatticeBand.lean` | `a88cd251573aa8a5416afa583b0a97b1e575ab09d4742b13a5b0be0e8a16b132` |
| `Bosonize/Core/Ch20CDW.lean` | `00693b1dafb43d59f185143912d8a78a4303708c637afe97eed45404ad74fd7f` |
| `Bosonize/Core/V1S2FormalVertices.lean` | `17cab3f91f38bc218b18cd7a2fe9e2ec8abf13d487096c3c2fa3fdd5c107020` |
| `Bosonize/Core/V1S4FiniteCurrentComparison.lean` | `3f436b970c78bb5126a18ab0ffc4a523bea61dd855f60b491baf410f96770b3e` |
| `Bosonize/Core/V1S5FiniteGroundState.lean` | `5ca1795a6f42d27b4995d51c066adc11e570fb8dfe246fa1f5d24b63752934b3` |
| `Bosonize/Core/V1S5FiniteVectorStates.lean` | `2b1b6ce7eb6694abae1094a93a40b37bfb1cfedb7b659f4a702ce3c851f07822` |
| `Bosonize/Core/V1S5MomentObstruction.lean` | `5084ca9963ef0344f3ef9046a86f7faeb86387dc590d3b07de0f623dfeeea82c` |
| `Bosonize/Core/V1S5SmallInteractingModel.lean` | `b5a60d0c6f62544d1a825cda6e1cc4dd4980d28591fb87fb2c7b0a9019784a79` |

### Follow-up: nonempty mode cutoff

The same reviewer independently continued at the primary agent's request.
For one species with `h=3`, `L=6`, `N=0`, `Kin=0`, `Kout=2`, `M=1`,
`x=0`, and trivial twist, the source sea is `{-2,-1,0}` and the lowered
target sea is `G={-2,-1}`. The source and target `r2` margins hold. At this
position the physical normalization is `1/sqrt(6)` and the Klein phase is +1.
The complete physical image is

```text
(1/sqrt(6)) ( |{-2,-1}> - |{-2,0}> + |{-1,0}> ) .
```

The candidate has `wPlus=-rho(-1)` action zero on `G`, and
`wMinus=-rho(+1)`. Since
`rho(+1)|G>=|{-2,0}>` and
`rho(+1)|{-2,0}>=|{-1,0}>+|{-2,1}>`, its finite Taylor image is

```text
(1/sqrt(6)) ( |G> - |{-2,0}> + (1/2)|{-1,0}> + (1/2)|{-2,1}> ) .
```

All displayed target states lie within `Kout=2`. This is a full-image mismatch
at nonempty oscillator cutoff `M=1`, including an extra component of magnitude
`1/(2 sqrt(6))` and a half-sized coefficient on `|{-1,0}>`. This validates the
theoretical obstruction but is not yet a Lean proof. Follow-up source hashes:
`Ch09DensityModes.lean` `085d890f8c56b7dc8b9bf9ea15fc36a92f7f6ddd81ae6125343c6e567323097e`,
`Ch04CARFock.lean` `8be8dacb9212e7535e1fa7357398bb5b6a7cae6188d6d8643be6548d0ec422e0`,
`A04DensityKinematics.lean` `aa43c291dc33f5eca3e32f24ae416d52f72e7e36d52de8eae524e670a70d9742`;
the other follow-up source hashes are already listed above.

## Exact comparison target

No global field equality is selected. The physical target is the exact typed
product decomposition for actual CAR fields, retaining both the discarded
ambient intermediate channel and any range omitted by an oscillator/partition
embedding. A sharp field-dictionary obstruction is the full-ground-image
mismatch at `h=3, M=1` above (with the parameterized `M=0` family as a second
check). CH14's conditional cyclic/common-residual criterion remains valid and
conditional.

The existing CH20 results already provide the exact typed CDW product split
and a nonzero discarded-channel witness at `h=2`, `Ks=Km=0`, `Kt=1`; the
target-zero witness proves target dependence. S6 must connect these declarations
to the new range decomposition and derive a numerical or sharp nonzero
consequence, rather than duplicate their names.

## Object and convention distinctions

1. **Physical field A:** actual `A05.liftedAnnihilation` with the external
   twist, `L^(-1/2)` normalization, target budget projection and complete
   occupied-momentum hole sum.
2. **CH14 candidate B:** source zero-mode phase first, then projected Klein
   lowering, finite Taylor of lowering `wPlus`, typed cutoff transition, then
   finite Taylor of signed raising `wMinus`; actual adjoints reverse order.
3. **S2 object C:** auxiliary charge-vector tensor oscillator polynomial
   carrier, coefficientwise in a formal parameter. No evaluation at `t=1` and
   no identification with A or B.

The actual CDW operator is `c_R† c_L` and has charge shift `(+1,-1)`; the SC
operator is `c_R c_L` and has shift `(-1,-1)`. Product factor order and Klein
signs remain the source definitions. S4 supplies a selected partition-map
embedding, not full-budget surjectivity. S5's constructed interacting state is
available only with its specified compressed Chapter 17 Hamiltonian; it is not
the S4 free sea and does not imply an interacting-state dictionary error bound.

## Five error obligations for S6

| Error | Exact meaning and carrier | Existing control / selected status |
|---|---|---|
| Intermediate projection | `P_t A (1-P_m) B P_s` on the actual finite CAR Fock carrier | CH20's exact CDW split; nonzero `h=2` witness, plus target-zero case. S6 must derive a quantitative consequence. |
| Mode truncation / omitted range | `P_m-U_m U_m†` for an isometric oscillator/partition embedding into the ambient intermediate budget, plus modes absent from the candidate | Keep as an explicit range term; S4 does not prove onto. Numerical bound is not yet established. |
| Normal-ordering / normalization | Difference among the actual CAR field normalization, CH14's finite Taylor candidate and S2 Weyl/bare-normal/dressed-normal conventions | No rescaling of the physical field. S0's equal-point `1/4` versus formal `1/16` is a sharp obstruction for the proposed full-carrier dictionary; no broader normal-order theorem is claimed. |
| State comparison | Physical vector state versus a specifically selected finite model state and observable dictionary | S5 constructs a ground vector for its compressed Hamiltonian; S4's transformed-observable free-sea moments do not bound this state difference. Exact selected-state error remains conditional. |
| Dispersion / Hamiltonian approximation | Difference between the physical finite dispersion and a selected linearized/current Hamiltonian on a fixed finite particle sector | No dispersion approximation is made in the exact CAR product comparison, so this term is absent there by construction. No ground-state stability bound is claimed. |

## Validation and phase state

At entry, the existing accepted Core modules built with `lake build` (3443
jobs); the replay emitted pre-existing `Try this` suggestions. That dated
entry evidence is superseded by the Phase B receipt below.

## Phase B scoped review and lock receipt

- Independent reviewer: `/root/s6_phase_b_review` (native diagnosis/review
  agent; no source edits).
- Exact reviewed Lean source hash:
  `46e2a22f2f3fd325d7d67dd5d30b03be47aefd734c472c27bcd7ad942aacf2a0`.
- Exact reviewed companion hash:
  `d5cb221ff15751bfed5663a0509a72b3bc352fe87407987a20ffcf425c35ada9`.
- Exact reviewed receipt hash:
  `1a2ae4219889a54b3202c733c965916581aa022db5380ed2a971c06d621fecd7`.
- Review findings and resolution: first returned **REVISE** because the ambient
  range-inclusion hypothesis was unused and the linter reported unused finite
  dimensional instances. Added `rangeProjection_subprojection`, invoked it in
  the exact decomposition, and omitted the three unneeded finite-dimensional
  section variables. The reviewer returned **PASS** on that resolution.
- Follow-up review of the quantitative proof returned **PASS**. It checked the
  typed decomposition use, the split
  `(Ahat - VA) ∘ Bhat + VA ∘ (Bhat - VB)`, and the submultiplicative norm
  bounds. The two concrete lower-bound statements were reconfirmed against the
  CH14 and CH20 definitions and the recorded full-image/witness computations;
  their proofs remain open and were not approved.
- Scoped lock: `BosonizeStubs/V1S6PhysicalFields.lean` was added to
  `docs/spec/stub_locks.v2.json` after the independent PASS. The lock file was
  edited by adding only this S6 entry; prior entries were preserved byte for
  byte. Lock SHA-256 after this addition:
  `18e2a5fa5d240fde700857ebb9f01676f405b046c9a15d465e40bcb68cf32c2a`.
- `python3 scripts/guards/stub_lock.py --check --strict` passes. The reviewed
  staging build completed 3443 jobs with only the two declared concrete
  `sorry` placeholders and no S6 linter warning. These facts establish a
  reviewed interface and proof batch, not Phase B completion.
