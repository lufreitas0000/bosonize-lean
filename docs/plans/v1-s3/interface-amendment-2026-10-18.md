# S3 constant-phase interface amendment — 2026-10-18

The user authorized the reviewed four-header correction and continued sprint
development after the compiler-checked cardinality counterexample was reported.
The correction applies coefficientwise `Multiset.map (vertexCoeffScale phase)`
in `duality_vertex_D_contract`, `duality_vertex_S_contract`,
`dressed_normal_vertex_D_contract`, and `bare_normal_vertex_D_contract`.

The former RHS scalar Cauchy convolution retained zero-scaled multiset entries.
The corrected literal multiset equalities preserve the intended phase,
coefficient multiplicities and existing data definitions. S2/Core is unchanged.
The degree-zero contract and ordered-functional statements are unchanged.

Independent native statement reviewer: `/root/s3_syntax_review`, PASS for the
exact proposal diff. Reviewed prior source SHA-256:
`dfff5b3e4e9d10e6e54a7e78406664b57ab22b1d1645b8bd6e0e8a63f140b58a`.
Reviewed amended source SHA-256:
`1574eb8b3e555cbbde324d0f68ac5f04b30cff363859bb2dfa514a3bda85e200`.
Scratch candidate elaboration passed; seven proof placeholders remain at this
amendment baseline. This is interface acceptance, not proof completion.

Exactly four `lemmas` records in `docs/spec/stub_locks.v2.json` were amended:
their statement text and hashes changed, while their context hashes did not.
All other manifest records and byte formatting were retained. Strict interface
verification passes at 1215 statements and 1240 frozen commands. The prior Core
preservation check passes for all 37 complete files. The amendment is committed
before subsequent proof work, as required by the scoped-lock workflow.
