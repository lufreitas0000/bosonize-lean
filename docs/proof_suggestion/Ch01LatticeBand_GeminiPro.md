# Chapter 1 proof suggestion — superseded by frozen Core

Revision: 2026-10-09. The original suggested module is preserved in Git at `d3770c1`. It failed compiler checks and duplicated the approved implementation. The maintained implementation is [Ch01LatticeBand.lean](../../Bosonize/Core/Ch01LatticeBand.lean), with its [companion notebook](../companion/Bosonize/Core/Ch01LatticeBand.md).

Use these dependencies when reading the proof:

1. Integer band membership and its finite enumeration.
2. Quotient projection and the centered representative with the positive Nyquist endpoint.
3. Left/right inverse laws, then the band/lattice bijection and cardinality.
4. Transported addition and negation, followed by the wrap and Nyquist lemmas.

Reuse the frozen declarations for downstream chapters. Do not redeclare the band, add a competing group instance, or unfold dependent representative conditionals when a proved quotient/section law applies. Positivity hypotheses and local `NeZero L` instances have different elaboration roles; install the instance where required.

The [proof revision guide](../../note/proof_suggestions_revision_2026-10-09.md) preserves the original compiler findings. Retiring this draft resolves the duplicate implementation issue; it makes no claim about the proof status of later chapters.
