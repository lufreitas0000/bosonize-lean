# CH20 finite order parameters and duality — Phase A companion


**Carrier and import ledger.** The code uses `A05.FockSpace σ h` and `A05.Operators σ h` for the uncompressed finite occupation CAR algebra; `A05.jointBudget h Ns K` for each of the three individually typed charge/cutoff spaces; `Module.End ℂ E` for generic algebraic mode families; `σ → ℤ` for charge labels; `ℂ` for Klein/character coefficients; and `ℝ` for the finite logarithmic kernel and hyperbolic parameters. The only direct imports are `Bosonize.Core.Ch14Mandelstam`, `Bosonize.Core.Ch16FieldHamiltonian`, `Bosonize.Core.Ch17LuttingerModels`, and `Bosonize.Core.Ch18Bogoliubov`. No Mathlib umbrella import, staging import, CH19/A08 carrier, locally installed notation, invented Fock star-equivalence, or arbitrary source-independent field map occurs.

**Exact signature and source-to-contract index.** The theorem headers in the single Lean fence are normative proposed signatures (no implicit intended additional parameters). The groups below mirror them and their source anchors:

| Proposed declarations | Origin and dependency | Carrier/hypothesis rationale |
|---|---|---|
| `raiseCharge`, `reflectLeft`, `cdwTarget`, `scTarget`, `cdwShift`, `scShift`; their inverse, application, and involution lemmas | Guidance §D0; `Ch13.lowerCharge`; `A06.Branches.distinct` | Charge labels `σ → ℤ`; no state/representation |
| `fieldOf`, `orderCDW`, `orderSC`, their charge commutators | Guidance §D1, claims c01–c02; A05 finite CAR; N20 (20.1–20.2) | Actual species R≠L, global CAR endomorphisms, `LinearMap.adjoint` of the right field |
| `cdwResidualOp`, `scResidualOp`, `ambient_*_residual` | Guidance §D1 c03; A03 projector-product remainder; N20 (20.3–20.4) | Keep explicit `1-Pm` intermediate excitation leakage at *any* cutoffs |
| `projected_*_residual`; `cdw_creation_factor_eq_budgetAdjoint` | Ch14 `projectedMap`, `projected_map_adjoint`; N20 Lemma 20.2 | Source `(Ns,Ks)` → middle `(Ns-eL,Km)` → target `(Nt,Kt)`; reversed carriers for CDW † |
| `cdwChargeCoeff`, `scChargeCoeff`, `order*_ground_coeff` | Guidance §D2 c05, Ch13 `kleinPhase`, A01 `integerCharacter`, Ch14 `zeroScalar`; N20 after (20.4) | Periodic twist, canonical root, position integer, source Klein phase acts first; boundary conditions on occupied/empty edge modes |
| `concrete_*` in `FiniteWitnesses` | Guidance §D1 c06–c07; N20 after (20.4) | h=2, L=4, R=0, L=1; explicit nonzero coefficient, operator, and residual at Kt=1; contrast Kt=0 |
| `klein_reflect_*`, `*_target_dual`, `*_reverse_*`, `*_charge_duality`, `*_norm` | Guidance §D2 c13–c14, A09 §§charge/Klein; A01 root/conjugation facts | Scalar, label-level adjoint shadow only, with `χ(1,x)` correction; no A08 `D` claimed |
| `dualPair`, `dualParams`, `dualPair_involutive`, `dualParams_involutive`, `luttingerG*_dual`, `dualParams_pair`, `v2Velocity_neg` | Guidance §D3 c10; A07 `HyperbolicParams`; Ch18 `HyperbolicPair`, `luttingerG`, `luttingerGInv`; Ch17 `v2Velocity` | Constructed record with c fixed/s negated, u and v1 fixed, v2 sign reversed; g and gInv exchange |
| `ModeFamily`, `speciesFamily`, `dualFamily`, `dressed*Of`, `pairingModeOf`, bridges to A07, dual family/dressed/commutator/pairing laws | Guidance §D3 c11–c12,c15; A05 `rho`; A07 density pairing/Bogoliubov definitions | Endomorphisms indexed by orientation/mode; `dual_commutator` gives the cross sign, not an unsupported ambient star automorphism |
| `chiralPhaseOf`, `xCDWOf`, `xSCOf`, `dual_chiralPhase_*`, `dual_x*` | Guidance §D3; Ch15 conventions cited in guidance; N20 (20.6–20.7),(20.10) | Finite sums of mode-family endomorphisms, not formal vertices or expectation values |
| `dual_symmetric_zero_mode`, `dual_canonical_mu_zero_mode`, `concrete_linear_mu_counterexample` | Guidance §D3 c15–c16; Ch17 `symmetricZeroModeScalar`, `zero_mode_scalar_canonical_mu` | Symmetry of adjusted quadratic charge scalar only; explicit failure for unadjusted μ |
| `logKernel`, `logKernel_self`, `logKernel_symm`, `logKernel_nonneg`, `concrete_logKernel` | Guidance c08/D3; N20 (20.5) | Truncated real cosine sum; no limit, correlator, or `t = 1` construction |
| `concrete_*` in `DualityWitnesses` | Guidance §D3 c18; Ch18 `concretePair`, `concreteNs`; A07 `pairing_mode_ground_nonzero`; A05 `rho_lowering_budget_zero` | g=1/4→4, nonfixed s, actual nonzero v2 pairing on h=8 sea; no spectral equivalence |

**Dependency and proof order.** First check definitional equalities for updates, `Ch13.lowerCharge`, and the exact R/L order. Next elaborate the finite fields and projection formulas using `A03.projection_product_remainder` and `Ch14.projected_map_apply`; establish the reversed-carrier adjoint using `Ch14.projected_map_adjoint`. Independently derive charge commutators from A05 CAR and the diagonal charge observable. Then prove the two ground matrix coefficients by `Ch14.physical_ground_expansion`/A05 occupation signs, with periodic twist normalization and strict band-edge margins. The explicit `h=2` witnesses are independent checks of signs and projection leakage, *not* substitutes for general proofs. Prove label/Klein scalar duality separately; construct and check the hyperbolic data before working on family/phase and pairing equations. Finally establish kernel elementary properties and the μ counterexample.

**Margin and non-vacuity obligations.** `0 < h` makes `2*h` positive and the canonical root primitive in the scalar theorems. `A05.admissible h Ns` ensures a valid source sea; `Ns R < h` permits the right creation and `-h < Ns L` permits the left annihilation for CDW; for SC both lowering operations require `-h < Ns R`, `-h < Ns L`. There are deliberately no extra budget-margin assumptions on the *residual identities*: those are exact equalities even when budgets truncate the intermediate state. The finite ground-to-ground coefficients `i/4`, SC operator nonzero, and `Kt=1` discarded-channel output are explicit F2 guards. `Kt=0` provides the contrasting cancellation. The dual pairing witness has `h=8`, `m=1`, `v2=15≠0` and admits an A06 positive-mode margin, whereas the parameter witness has `s=3/4≠0`; the kernel example has `h=2,M=1` and nonzero separation. The μ counterexample has different numeric scalar energies `π−1` and `1`.

**Proposals accepted/adapted/rejected.** Accepted: source-carrier CAR order words, canonical Fourier phase, explicit three projected carriers, source-to-middle-to-target residual, scalar Klein convention, constructed parameter sign flip, finite family transformation, and symmetric quadratic zero mode. Adapted: the guidance's `HyperbolicPair.dual` is named `dualPair` in this module so that no foreign Core namespace is extended; there is no unverified `LuttingerParams` field `g`, since `g` is computed from `Ch18.luttingerG`. Concrete witness admissibility is a **named theorem obligation**, not hidden proof data. Rejected: `import Mathlib`, A08/staging imports, field-independent placeholder maps, same-species pairing, any `True` target, a direct CDW→SC exchange without adjoint/root phase, and a finite-Fock star/unitary implementation of `D`.

**Deferred CH20b and CH21 ledger.** CH20b, conditional on a reviewed CH19/A08 uncompressed state carrier, owns formal `W_J` vertices in a defined noncommutative series carrier, Hermitian phase proof, Gaussian/Wick moments, `[X_J(x),X_J(y)]`, coefficientwise correlators and variances (20.8–20.9), tensor-algebra automorphism `D`, the complete adjoint/`ζ^x` identity (20.10), and state pullback/transport (20.11b). Theorem 14.5 single-factor CAR-to-vertex equalities remain independent prerequisites; an analytic `t=1` evaluation, continuum power law, finite-CAR correlator equality, and finite-Fock spectral/T-duality are not inferred. CH21 owns spin/charge separation, parity sublattices, Umklapp charge shifts, and effective Hamiltonians.


## Phase A acceptance record — 2026-10-16

- Lean source: `BosonizeStubs/Ch20CDW.lean`; SHA-256: `77d49a6fe6166d07cdc706a2ab1de0b7a0745882ed0658e6d3ca104cacddb241`.
- Draft artifact SHA-256: `d3b89fbbde18a8f2d6a06a7b6779721cd1eb48749615cd9b4e5ca4ec3ff59272`; packet `ch20_phase_a-20261016T133230Z-dbc49307`, base commit `d555477a75e28da8e75d5e6e88518fdce173c9aa`. The downloaded originals remain unchanged.
- Scope: 27 complete data declarations and 64 theorem/lemma stubs. The accepted boundary is finite CAR order parameters, retained projection residuals, scalar Klein/charge duality, mode-family duality, and finite parameter/kernel witnesses. Formal vertices, Wick/Gaussian series and state transport remain deferred to CH20b.
- Fresh Phase A elaboration: `python3 scripts/webllm/verify_phase_a.py docs/webllm/drafts/ch20_phase_a.md` passed on the exact candidate. It reported 27 audited data declarations and 64 unproved theorem stubs. Placeholder warnings are expected at Phase A; no proof completion is claimed. All audited data dependencies were limited to `Classical.choice`, `Quot.sound`, and `propext` (or no axioms).
- Independent review: `/root/ch20_phase_a_review`, mathematical/interface verdict PASS for the exact source-map-corrected artifact SHA above. Review checked carriers, charge shifts, product order, adjoints, residuals, Klein coefficients, mode-family duality, zero-mode claims and witness hypotheses. It did not prove the theorem stubs.
- Deterministic corrections before acceptance: added `[Fintype σ] [LinearOrder σ]` to both zero-mode duality lemmas after the first compiler run reported missing instances; clarified the packet's empty editable-target hash as baseline metadata and removed it from the source-hash table. The final artifact was re-elaborated and independently re-reviewed.
- Local staging, companion and lock are prepared from this exact reviewed source. The first compiler attempt failed only on those two missing instances; the final fresh run passed.

Phase A interface review and elaboration are complete. All 64 contracts remain unproved; Phase B must prove them under the new lock before any Phase C promotion.

## Phase B reviewed interface correction — 2026-10-16

Restored archive checkpoint `2fecda3711065037f2879f73421f78c86161e0db`
captures the previously uncommitted proof development from detached base
`0cfbf0c0b56ed020be89ac5be6537b994e702c6c`. Source SHA256 before the
remaining nonzero proof integration:
`a7168fd19c5e72c0f7d1371a1b67b83e827030dcbc75e5e544d9a9008b64106d`.

Independent reviewer `/root/audit_locks` compared this exact source with the
accepted Phase A interface. All 64 original contracts and original data remain;
ten headers gain only `omit [Fintype σ] in` to remove redundant section-instance
context. Additions decompose the approved proofs: 47 private helper lemmas,
18 local occupation-order/equality instances derived directly from A05,
three private concrete occupation definitions, four helper sections and a
local type variable. `Mathlib.Analysis.Real.Pi.Bounds` supplies
`Real.pi_gt_three` for the explicit linear-μ counterexample. No mathematical
hypotheses/conclusions or upstream Core sources changed. Review verdict:
scoped additive correction approved, conditional on fresh elaboration/axiom
checks. These changes predated this resumption; the inherited partial manifest
omitted the helpers and therefore failed strict verification.

Fresh installed-compiler elaboration of the exact source plus `#print axioms`
for 158 completed declarations succeeded with no errors and only the single
expected placeholder warning for the remaining
`concrete_discarded_channel_nonzero`. Every audited completed declaration used
only `propext`, `Classical.choice`, and `Quot.sound` (or no axioms). Complete
output: `docs/verification/ch20-phase-b-20261016/reviewed-baseline-axioms.log`.
The incomplete theorem was excluded from this baseline axiom audit and is
not accepted by this record. Existing Core guard passed for 33 complete files.

The correction regenerates only the CH20 record using the guard parser API;
all other manifest records are checked unchanged. This establishes a reviewed
committed baseline before further canonical proof-body edits. Phase B remains
in progress; Phase C is outside this request.

### Remaining witness integration and import correction

Independent proof reviewer `/root/review_proof` approved the unique-coefficient
argument and its adaptation to the canonical ground-vector contract. The
integrated proof keeps every supporting construction as a local `let`/`have`,
reuses the existing expansion and occupation helpers, and leaves the canonical
statement unchanged. The witness removes left mode -1 and creates right mode +1;
its left excitation is one and right excitation zero. Intermediate cutoff zero
rejects it, while target cutoff one retains it. Equality with the witness forces
that unique mode pair, whose coefficient is a product of nonzero normalization,
characters and fermion signs. Thus cancellation cannot destroy this coefficient.

Fresh warning-as-error compiler validation passed on the complete integrated
source. Native canonical Lean MCP diagnostics subsequently returned success=true,
partial=false, timed_out=false, items=[], failed_dependencies=[].

Lake additionally diagnosed a module-system import warning for the newly added
Pi.Bounds import. Independent reviewer `/root/audit_locks` approved removing that
extra import and proving the unchanged concrete μ counterexample using existing
`Real.cos_pi_div_two` and `Real.cos_one_pos`: the derived equality π=2 would force
cos(1)=0, contradicting positivity. The final complete candidate again passed
warning-as-error compilation. This restores the original four Core imports;
only the CH20 lock record is amended. The final source SHA256 is
`00693b1dafb43d59f185143912d8a78a4303708c637afe97eed45404ad74fd7f` (filled from the actual file below). No linter is suppressed.
Final acceptance still requires the full fresh verifier, build and CI receipts.

## Phase B local acceptance — 2026-10-16

All 64 original Phase A theorem contracts are proved. Together with the reviewed
private helpers, data and local instances, the final verifier audited 159
declarations from freshly compiled source. Source SHA256:
`00693b1dafb43d59f185143912d8a78a4303708c637afe97eed45404ad74fd7f`.
The earlier Phase A counts above describe the historical acceptance snapshot,
not the current proof status.

Acceptance evidence is in `docs/verification/ch20-phase-b-20261016/`:
- `receipt.json` binds the final source/lock/log hashes and audited commit
  `b0d3e8a72f219277c709618a596a363b546d9707`.
- `final-verifier.log`: repository `verify_phase_b.py` passed with 159 freshly
  audited declarations, zero forbidden proof tokens, zero warnings under
  warning-as-error compilation, and only `propext`, `Classical.choice`,
  `Quot.sound` (or no axioms).
- `ci.log`: full `scripts/ci.sh` ended `CI OK`: 69 guard tests, strict v2 locks,
  all 33 complete Core hashes, Core build, staging build, and 18 Web-LLM tests.
  The `Fixture.value`/`sorryAx` output is from a deliberate negative verifier
  test; it is not a CH20 dependency.
- Native canonical Lean MCP diagnostics passed with empty items and failed
  dependencies, partial=false, timed_out=false after rebuilding/restarting the
  LSP following worktree restoration. Scratch MCP unavailability was a tooling
  result, not substituted for the subsequent canonical diagnostic result.

The final verifier and CI ran using the required namespace sandbox, with no
network and credential directories hidden, in a separate audit checkout at the
same commit. `WEBLLM_COMPILER_ROOT` selected that exact checkout under the
verifier's same-HEAD check. No baseline gate was weakened. The verifier needed a
reviewed regression fix to recognize Lean's generated private names in fresh
`#print axioms` output; five targeted tests and the full suite passed, including
rejection of missing receipts and nonstandard axioms.

This is local Phase B acceptance from independently reviewed proof development.
No browser finish transaction was invented: CH20 was not started in that runner
and there is no downloaded-response finish receipt. No remote GitHub CI result
or push is claimed. The work is retained on `codex/ch20-phase-b-resume`.

The proved scope remains finite CAR order parameters with explicit compression
residuals, scalar charge/Klein duality, mode-family substitutions, and finite
parameter/kernel witnesses. It does not establish a finite-Fock unitary duality,
formal vertex/Gaussian/state transport, analytic evaluation or continuum
correlators. CH20b and Phase C remain outside this Phase B-only continuation.

Final independent read-only review `/root/audit_locks` bound PASS to the exact
final source hash and audited commit above. It rechecked preserved original
contracts, CH20-only manifest impact, the restored imports, coefficient witness
and cosine proof, unchanged Core/dependencies, and all final validation logs.

## Phase C promotion — 2026-10-16

The canonical source moves byte-for-byte from `BosonizeStubs/Ch20CDW.lean` to
`Bosonize/Core/Ch20CDW.lean`; namespace `Bosonize.Ch20` is unchanged. Its SHA256
is `00693b1dafb43d59f185143912d8a78a4303708c637afe97eed45404ad74fd7f`. All imports already target Core; no import,
statement or proof substitutions are needed. The v2 lock entry changes only
its path key; every declaration and command hash is preserved. The complete
source hash is added to the Core manifest, leaving the existing 33 entries
unchanged. The Core aggregator gains its import; staging inherits it through
`import Bosonize`. Historical Phase A/B paths and receipts above are retained
as provenance. Current companion and source live under `Bosonize/Core/`.

Pedagogical mapping: `notes/md/ch20_CDW.md` retains the reference chapter and
adds the verified finite realization. Charge shifts and residuals map to
`orderCDW_charge_commutator`, `orderSC_charge_commutator`,
`projected_cdw_residual`, `projected_sc_residual`; periodic ground coefficients
to `orderCDW_ground_coeff`, `orderSC_ground_coeff`; cutoff witnesses to
`concrete_discarded_channel_nonzero` and `concrete_discarded_channel_target_zero`;
scalar/family/parameter duality to `cdw_charge_duality`, `sc_charge_duality`,
`dual_xCDW`, `dual_xSC`, `dual_pairingMode`, `dual_symmetric_zero_mode`,
`dual_canonical_mu_zero_mode`; finite kernel to `logKernel_nonneg` and witnesses.
Formal vertices, Wick/state transport and continuum claims remain deferred.
