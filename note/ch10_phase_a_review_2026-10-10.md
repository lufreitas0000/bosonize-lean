# CH10 and A04 restricted-current Phase A independent review

Date: 2026-10-10. Verdict: **PASS for initial interface locking and Phase B**.
This is a statement/interface review, not proof completion. The requested Flash/Pro
providers were unavailable; this independent review used the inherited available
Codex model. No guarded Core file or interface lock was edited by the reviewer.

## Exact reviewed sources

| Staging source | SHA-256 | Lemmas | Placeholders | Data definitions |
| --- | --- | ---: | ---: | ---: |
| `BosonizeStubs/A04CurrentMargins.lean` | `fd9f539abd4e4026531e007ee79f7c9f88e3a13f6b67c522bda26563f19356d2` | 16 | 16 | 3 |
| `BosonizeStubs/Ch10Heisenberg.lean` | `3da47f8454feb3921b446433ced39712f1e5b010635f298d3f9f779fd55ed2dc` | 21 | 21 | 3 |

Each theorem body contains exactly one `by sorry`; definitions contain none.
Companion source snapshots match these files byte for byte. These counts were
independently read from the final files; there are 37 theorem stubs across the pair.

## Mathematical findings

- Chapter 10 §§10.1–10.5 and the density-support portion of A04 are represented
  faithfully. Partitions, Gram identities, completeness and Sugawara equivalence
  are explicitly deferred, rather than inferred from current algebra alone.
- The carrier is the existing finite CAR Fock space over the signed integer band.
  Integer-truncated shifts retain the finite matrix edge terms, and the existing
  CAR Lie lift is used without asserting that second quantization is multiplicative.
- Opposite currents have bottom occupation minus top occupation. The convention
  gives `[rho(-m),rho(m)] = +m` on valid inputs, and the arbitrary signed coefficient
  is `-m` when `m+n=0`. The zero-transfer normal-order subtraction is central.
- The useful diagonal M1 margin is `m+K+|N|≤h`, without an unnecessary `2m`.
  The unequal mixed M2 margin is the genuine two-mode `|m|+|n|+K+|N|≤h`.
  Both source and target edge support are retained. A full bottom target blocks
  only an off-diagonal hop (`p≠k`); an empty top source blocks every hop.
- Signed negative budgets are zero by existing Core. A proof of signed M1 must
  split this case before deriving `m≤h` or casting `K` to a natural budget.
  Thus apparently large modes in a negative-budget branch cause no false claim.
- Words are listed in application order; a written product is reversed before
  tracking excursion. The exact signed prefix target is `K+prefix.sum`, followed
  by the maximum upward cumulative excursion wrapper. Restricted CCR is applied
  at the actual suffix input; neither commutator factor is required to preserve
  the original budget. Reordered future words need their own suffix checks.
- Arbitrary twist is explicit in the reconstructed-current theorem and eliminated
  through the already proved matching inverse-Fourier dictionary. Cyclic site
  Fourier coefficients are excluded because their wrap remainder is real.
  The same-sea integer excitation convention is retained; no claim about changing
  physical seas or twist-independent absolute energy is introduced.
- Nonvacuity is explicit: admissible nonnegative budgets have nonzero ground kets.
  The instance `h=1,m=1,N=K=0` satisfies M1 and has nonzero scalar action on that
  ground. Empty occupation gives a nonzero full-carrier ket killed by the current
  commutator, ruling out unrestricted scalar CCR for every `m>0`, including `h=0`.

The historical P06/P07 reconciliation and current A03/A04/CH04/CH07/CH09 APIs
support the stated proof decomposition. No unresolved mathematical defect or
substantive ambiguity was found.

## Validation and limits

Independent classical enumeration of all occupations for `h=1..5`, all charges,
budgets `K=-1..h`, and nonnegative shifts `0..h+1` passed 617 applicable diagonal
M1 and unequal mixed M2 edge checks. These are finite sanity checks, not Lean proofs.

The draft agent and orchestrator report successful installed-compiler elaboration
with exactly the expected sorry warnings, native CH10 diagnostics without failed
dependencies, and fresh audits of all six data definitions restricted to standard
axioms. This reviewer inspected the exact interfaces and existing proved support;
no Phase B theorem is represented as proved. Phase B must still eliminate all
37 placeholders, resolve warnings, and audit fresh theorem dependencies before
Phase C promotion.
