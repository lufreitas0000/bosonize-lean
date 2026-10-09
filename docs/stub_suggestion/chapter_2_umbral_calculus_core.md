# Chapter 2 stub suggestion — superseded by frozen Core

Revision: 2026-10-09. The original draft is preserved in Git at `d3770c1`. Use [Ch02UmbralCalculus.lean](../../Bosonize/Core/Ch02UmbralCalculus.lean) and its [companion notebook](../companion/Bosonize/Core/Ch02UmbralCalculus.md). The historical unbundled draft had obsolete imports and definition placeholders; it is not an alternative approved interface.

Reuse the bundled shifts, inverse shift, identity, finite differences, falling factorials, polynomial shift/difference, umbral map, and position multiplier. The proofs use:

- Pointwise expansion and ordered product identities for discrete Leibniz rules.
- Exact translation reindexing on `ZMod L` for periodic summation by parts.
- The commuting binomial theorem for the Newton expansion.
- Monomial-basis equality for `umbralMap.comp Polynomial.derivative = polyForwardDiff.comp umbralMap`.
- Pointwise scalar calculation for the Heisenberg pair, and the finite-dimensional trace obstruction with its nonzero-carrier hypothesis.

Preserve the approved additive domain assumptions. `Polynomial.derivative` is already bundled as an R-linear map. For new polynomial map equalities use `Module.Basis.ext` on `Polynomial.basisMonomials`; `LinearMap.ext_ring` concerns maps from the scalar ring.

The frozen `identity_apply` uses `omit` to prune unused section assumptions. Keep warnings resolved at their cause; do not suppress the linter or edit locked Core. The nonzero difference witnesses are part of the existing interface.
