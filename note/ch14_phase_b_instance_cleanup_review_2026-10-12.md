# CH14 Phase B — independent review of two scalar instance omissions

**Decision: PASS for the exact two-declaration cleanup.**

Reviewer: `/root/ch14_a05_phase_a`, author of the separate generic A05 support, not author of these CH14 scalar proofs. Baseline: `d4cba95dfdd6673e9e40d5623e8293a9d8426dd2`.

Candidate: `/tmp/bosonize-ch14/ch14-phases-cleanup.lean`; SHA-256 `dda7e42b1c50c68b951345b3e13616b7fb54b97c895ef7275dc8a4d75abc603b`.

The proposed change adds `omit [Fintype σ] [LinearOrder σ] in` only to `Bosonize.Ch14.zero_scalar_norm` and `Bosonize.Ch14.zero_scalar_winding`. It removes their implicit finiteness and order parameters. All explicit parameters, the `NeZero (2*h)` instance, the external twist family, integer charge family, position, winding parameter and conclusions remain identical. There is no change to `zeroScalar` or any operator data.

The scalar definition evaluates one chosen species component and multiplies the actual lift phase with an integer Fourier character. It contains no species sum, CAR-order operation or occupation carrier. Thus neither finiteness nor species ordering is required. Unit modulus follows from the actual lift/character norm theorems; winding follows from lift holonomy and integer-character representative independence. Removing these unused instances expresses the actual mathematical scope and resolves their warnings without weakening a required hypothesis.

Independent structural comparison with `stub_lock.parse_lean` confirms:

- Exactly these two lemma records differ.
- All 35 nonlemma command records are identical.
- Every other lemma record is identical.

Independent isolated check: `/tmp/bosonize-ch14/scalar-cleanup-independent.lean`, containing the identical complete scalar definition and both proposed proofs under the two omissions, passes `lake env lean -DwarningAsError=true` with zero warnings and no placeholders. Its fresh `#print axioms` for each theorem reports only `propext`, `Classical.choice`, `Quot.sound`. Fully explicit `#check @...` signatures show neither `Fintype σ` nor `LinearOrder σ` on either theorem.

This review approves only the stated scoped interface amendment. It does not approve broader header changes, alter Core, or itself establish full CH14 Phase B/C completion. The root must apply the exact omissions, update only the two affected lock records under the reviewed amendment, and repeat integrated validation.
