
The complete chapter-by-chapter review is in [reference_notes_lean_audit.md](/home/lucas/Projects/Lean/bosonize-lean/docs/audit/reference_notes_lean_audit.md). The [appendix index](/home/lucas/Projects/Lean/bosonize-lean/notes/appendices/README.md) links all nine proposals.

**Your two-step Fourier construction is a good solution.** I recommend keeping it, with these corrections:

1. Prove character orthogonality and the unscaled identities `TS = L·I` and `ST = L·I` first.
2. Introduce `1/√L` only in the complex Hilbert layer, proving its scalar normalization once.
3. Tighten the generic assumptions. A primitive root in an arbitrary commutative ring does **not** guarantee orthogonality—even when `L` is invertible. I proved a counterexample in Lean using `ZMod 15`.
4. Check library reuse before building the inverse ourselves. Mathlib already provides an unscaled `ZMod.dft` with a `1/L` inverse; we can transport it to the centered band and add the unitary normalization. [Official Mathlib DFT documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/ZMod.html).

The suggestion’s prohibition on asymmetric normalization is too broad: it is valid for algebraic inversion, though it does not directly give the physical unitary CAR change of basis. Its half-power Laplacian formula also has an incorrect sign and unspecified fractional exponents. These points are developed in [Appendix A01](/home/lucas/Projects/Lean/bosonize-lean/notes/appendices/a01_fourier_scalars_and_characters.md).

The most consequential downstream findings are:

- **Budget restrictions need composition rules.** Creators generally leave the input budget. Repeated products, adjoints, and commutator rewrites require bounds on intermediate states.
- **Polynomial exponentials need a precise carrier.** `exp(βX)` does not act on polynomials. Projecting creators makes them nilpotent but introduces boundary corrections that invalidate the ambient scalar BCH argument.
- **The chapter 14 vertex equality fails as stated.** At `K=0`, the physical fermion creates hole components absent from the proposed truncated vertex. I recommend first targeting equality between specified source and target budgets.
- **The dual-field formulas need mathematical corrections.** Identical right/left chiral signs give the wrong commutator pattern. Forward differences do not exactly cancel `1/m`, and a periodic difference kernel cannot equal a nonzero constant times a delta kernel whose sum is one.
- **Chapters 17 and 18 describe different quadratic models.** The written number-conserving mixing form has coefficients `v₁±v₂`; the proposed hyperbolic transformation belongs to a pairing form. We should choose the intended model before freezing either interface.
- **State existence and observable formulas need repair.** A compressed dressed vacuum need not exist; the density correlator omits the opposite-ordered contraction; and the Umklapp shift is **±1 per spin species**, not ±2.

For square-root efficiency beyond Fourier, the appendices propose **weighted, unnormalized monomial bases**, raw spin/charge currents, and scalar parameter structures. These keep most operator proofs algebraic without changing normalization silently.

Validation includes a warning-free Lean Fourier probe, exact finite CAR/rational counterexamples, and both committed Core freeze guards. The mathematical appendix proposals themselves remain unproved.
