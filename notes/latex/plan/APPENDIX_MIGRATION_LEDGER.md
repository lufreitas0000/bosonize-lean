# Appendix-to-chapter migration ledger

This ledger tracks the pedagogical ownership of the material in the assembled
book. The organizing rule is to introduce an idea and its working proof where
the reader first needs it; appendices may retain longer verification details,
alternate derivations, and material that interrupts the main argument. A build
or a Lean proof does not by itself establish that an argument is pedagogically
complete. This is an active editorial record, not a claim that every row has
passed an independent review.

| Appendix | Main-text owner / first use | Main-text coverage now | Appendix material to retain or migrate | State |
|---|---|---|---|---|
| A01 Fourier characters | Chapter 3; Chapter 16 for spatial collapse | Character convention, field hypothesis, zero-divisor counterexample, representative independence, orthogonality, inversion, and lattice dispersion are developed in Chapter 3; Chapter 16 applies the same finite Fourier calculation | No A01 topic remains appendix-only; its technical source is retained outside the assembled book | Migrated to main text |
| A02 CAR Hilbert carriers | Chapters 4–5 | Abstract and concrete CAR, occupation basis, signs, adjoints, and parity are developed in the main sequence | The appendix now contains only the Clifford/Fock spin representation, an advanced connection referenced at its point of use in Chapter 4 | Main-text migration done; orthogonal representation topic retained |
| A03 Energy budgets | Chapters 7 and 10, with applications in later chapters | Rank, charge-sector ground states, margins, budget subspaces, filtered operators, word excursions, and compression are treated at their first use | No A03 topic remains appendix-only; its technical source is retained outside the assembled book | Migrated to main text |
| A04 Density partitions | Chapters 9–11, with Sugawara application in Chapter 12 | One-particle shifts, edge formulas, current margins, rectangle bijection, Hall--Gram metric, and basis completeness are developed in sequence | No A04 topic remains appendix-only; its technical source is retained outside the assembled book | Migrated to main text |
| A05 Finite exponentials and Klein factors | Chapters 13–14 | Multispecies CAR, joint budgets, typed Klein maps, nilpotent finite exponentials, the projected vertex, adjoints, and the open-vertex obstruction are explained at first use | No A05 topic remains appendix-only; its technical source is retained outside the assembled book | Migrated to main text |
| A06 Chiral fields | Chapters 15–16 | Current-algebra transport to joint budgets, cross-species and chiral commutators, zero-mode kernel normalization and obstruction, gradient coefficients, normal-order contractions, and field-Hamiltonian symbol calculations are now explained at their first use | No A06 topic remains appendix-only; the source is retained outside the assembled book for traceability | Migrated to main text |
| A07 Interactions and Bogoliubov algebra | Chapters 17–18 | Chapter 17 now proves the sea-Wick contraction at first use; Chapter 18 now derives the real hyperbolic parameters and explains inverse/adjoint identities | Full transfer summation and extended CCR/Bogoliubov case proofs. Retain as supplementary verification after checking each cross-reference points backward to an explained result | In progress |
| A08 Algebraic states and correlations | Chapters 19–20 | Polynomial oscillator carrier and positive vacuum, dressed state, both ordered contractions, coefficientwise vertices/correlators, and the compressed common-kernel example are developed in the chapter sequence | No A08 topic remains appendix-only; the source is retained outside the assembled book for traceability | Migrated to main text |
| A09 Duality, spin and Umklapp | Chapter 20, Section 20.3 for algebraic duality; Chapter 21, Sections 21.1–21.3 for parity and Umklapp | Charge reflection, Klein signs, and formal vertex exchange have their derivation in Chapter 20.3; spin/charge parity and the CAR Umklapp/leakage arguments are in Chapter 21 | No A09 topic remains appendix-only. The source file is retained outside the assembled book for traceability | Migrated to main text |
| A10 Discrete RG and Schrieffer–Wolff | Chapter 21, Section 21.4 | Shell distinction, projectors, Sylvester equation, second-order polynomial, intermediate-state formula, remainder, matrix examples, and limits of the finite construction are presented in sequence | The old appendix source is retained as an archival duplicate but excluded from the assembled book | Migrated to main text |

## Changes made in this pass

- Chapter 17 now supplies a CAR-based explanation of the quartic sea-Wick
  contraction, including why the intermediate contraction survives normal
  ordering and why the repeated-mode term vanishes.
- Chapter 18 derives the stable hyperbolic parameters in place and explains
  the algebra behind the inverse and adjoint statements.
- Chapters 16 and 21 point to the chapter sequence as the primary exposition;
  the appendix is described as a home for longer verification details.
- Chapter 15 now gives a concrete admissible instance of the zero-mode
  obstruction, with the uniform-mode explanation.
- The A09 charge duality, parity arithmetic, Umklapp shift, and leakage
  material are already developed in Chapters 20.3 and 21.1–21.3; A09 is
  removed from the assembled appendix sequence.
- A10 is removed from the assembled appendix sequence because its substantive
  treatment is already in Chapter 21.4; its source file remains for traceability.
- A01, A03, and A04 are removed from the assembled appendix sequence after
  confirming that their substantive results and explanatory proofs are already
  in Chapters 3, 7/10, and 9–12, respectively.
- A02 is reduced to the Clifford/Fock spin representation supplement; the CAR
  carrier, sign, and parity exposition remains in Chapter 4.
- A05 is removed from the assembled appendix sequence after its finite
  exponential, Klein-map, and projected-vertex arguments were checked against
  Chapters 13–14.
- A06 is removed from the assembled sequence after its joint-budget current
  transport, chiral commutator, kernel-sum, ground-state witness, and
  normal-order symbol arguments were moved into Chapters 15–16.
- A08 is removed from the assembled sequence after checking its polynomial
  state, contractions, formal correlators, and compression counterexample
  against Chapters 19–20.

## Review boundary

This ledger is a migration map, not a completed chapter-by-chapter audit. In
particular, A07's detailed interaction and Bogoliubov proofs still need
systematic relocation or an explicit justification for remaining supplementary.
The Chapter 20 duality remains a
proposed formal-algebra construction, and the Chapter 21 spinful claims remain
outside the promoted Lean Core. Do not delete another appendix section until
its claims, proof, labels, citations, and first main-text use have been
accounted for.
