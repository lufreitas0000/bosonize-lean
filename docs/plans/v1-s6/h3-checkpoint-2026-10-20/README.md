# S6 h3 proof checkpoint — 2026-10-20

Status: **not accepted**. The production staging source is restored byte for
byte to committed checkpoint `1c3466489d245205e994a17500de11a8f93bba3a`.
Its reviewed CDW proof is intact. The h3 theorem still has its original single
placeholder. No lock amendment or Phase C migration has been applied.

## Verified progress

`standalone-calculation.lean.txt` compiled successfully under the repository's
Lean toolchain (full output in `s6h3.log.txt`). It proves the complete norm
bound at the concrete Type-0 PUnit instantiation. It is an auxiliary scratch
calculation, not acceptance of the locked universe-polymorphic theorem.

`generic-candidate.lean.txt` preserves the integrated candidate. Its final
compiler run is `s6-integrated-reduced.log.txt`. All local mathematical
calculations elaborate, including:

- Exact six-mode enumeration and ground configurations.
- Actual CAR actions rho1 G=H and rho1 H=I+J, with signs.
- Membership of G,H,I,J in target charge -1, budget2 (and G in budget0).
- Source zero mode, projected Klein shift with phase+1, degree-zero lowering
  Taylor, cutoff transition and degree-two signed raising Taylor.
- Physical J coordinate zero, because J contains+1 whereas every erased source
  sea lacks+1.
- Candidate J coordinate normalization6/2, error coordinate -normalization6/2,
  and its exact norm1/(2 sqrt6).
- Ambient normalized-ket Cauchy–Schwarz bound.

Here G={-2,-1}, H={-2,0}, I={-1,0}, J={-2,1}.

## Exact remaining goal

The final `simpa only [err, v, N] using hb` fails to transport the bound on
`‖(err : A05.FockSpace Species 3)‖` to the locked statement's budget-subtype
norm. The full unsimplified mismatch is in `s6-integrated-reduced.log.txt`.
The candidate binds `Species` and `Ns` to the actual target's universe via a
local `run_tac` definitional abbreviation. Its final simplification does not
list these two abbreviations. The next attempt should inspect the explicit
norm instances and use the actual inherited subtype norm equality, including
these abbreviations where needed; `Submodule.norm_coe` was suggested but has
not been tried. No coefficient proof remains mathematically open in this
candidate. No claim is made that a proposed final tactic is validated.

The source theorem is universe-polymorphic, so replacing it with the Type-0
scratch result would alter the locked contract. Earlier concrete-universe
transplants failed at this boundary. Generic `simp inner_sum` also failed to
fire and caused costly elaboration; the final candidate uses an explicit
`inner_sum_six` lemma via the actual inner semilinear map and `map_sum`.

## Independent review and resource wrapper

Reviewer `/root/s6_h3_diagnosis` reviewed the sparse mathematics and the ordered
candidate reduction positively, **conditional on integrated compilation and
fresh audits**. No unconditional integrated proof acceptance exists. The
reviewer made no repository edits.

The reviewer approved a narrow theorem-scoped heartbeat wrapper as a resource
amendment: `set_option maxHeartbeats 1600000 in`. Default command checking hit
200000; proof-local options do not cover the final declaration check. The
wrapper belongs before the theorem doc comment (a doc comment immediately
before `set_option` is a parser error). It changes only the h3 lock entry's
`hash` and `text`; other command and theorem records compare identical.
This amendment has NOT been applied to the repository lock. Before accepting
it, re-review the final exact source/hash, modify only that reviewed record,
and commit the amended baseline. The final saved candidate hash is
`e92d1710218d6fa7ecd9a91797e8164c327f580223868953ffd0e52a7bd015d6`.

## Documentation and stopping condition

The two pending pedagogical additions are reviewed mathematical drafts only.
They are saved separately and have not been applied to the notes. After
acceptance, replace CH20's stale 'Physical-field and residual norm comparisons
remain S6 work' sentence with a pointer to the S6 realization. Preserve the
reference prose and all five error distinctions.

Live Codex usage reached92% used (8% remaining) in the300-minute window;
weekly usage14%. The formalizer skill's10% stop guard required saving this
checkpoint and stopping new proof work. The reported five-hour reset is
2026-10-20 15:36:59 America/Fortaleza. No provider switch, purchase, automation,
push, release or other sprint was started. Recheck live allowance on resume.
