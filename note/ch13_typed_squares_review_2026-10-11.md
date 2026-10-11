# CH13 typed density squares: independent review

Date: 2026-10-11. Reviewer: inherited Codex fallback; Flash/Pro providers unavailable.

**Scoped result: PASS.** This review covers `klein_raising_square` and `klein_lowering_square`, their frozen headers, actual codomains, pointwise operator identities, and composition directions. It does not certify final chapter axiom closure or authorize promotion before the final gates.

The reviewed source is `/tmp/bosonize-ch13/resume/ch13-squares.lean`, SHA-256 `3353adebbe01992c4b479c98364c1bcbb7fbb735722efea1a226d0394ef353ce`. Only these two bodies were copied into the then-current complete source scratch `/tmp/bosonize-ch13/ch13-squares-independent.lean`. The copied headers match the frozen source. Independent compiler exit was 0 with no errors or new warnings; untouched placeholders were still present at that review checkpoint. Evidence: `/tmp/bosonize-ch13/ch13-squares-independent.log` and `/tmp/bosonize-ch13/ch13-squares-independent-review.json`.

`F0` and `F1` are actual budget `LinearIsometryEquiv` values obtained at cutoffs K and K+m. The smaller source and lowered-target margins follow monotonically from the stated larger margins. Raising `R0`/`R1` are codomain restrictions of the actual density rho(+m) composed with the corresponding source subtype; their codomain is K+m by the signed actual species-budget grading theorem. Lowering uses rho(-m) on K+m, whose signed output cutoff simplifies to K. The pointwise density identities are definitional and introduce no projection.

The raising composition is F1 after R0 = R1 after F0. The lowering composition is F0 after R0 = R1 after F1. After subtype extensionality, the proofs use the matching actual kernel intertwining theorem at exactly those margins. No carrier, phase, sector, or margin substitution was found.

At review time the final dependencies through raising and A05 hopping/rho still required integration and a fresh all-declaration audit. Final proof closure must be recorded separately; successful body compilation against those contracts is not that closure.
