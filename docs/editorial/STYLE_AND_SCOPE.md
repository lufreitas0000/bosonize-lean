# Editorial direction for the pedagogical monograph

This book is a pedagogical rederivation of results from the bosonization
literature using explicitly specified finite-lattice and finite-budget models.
It is not presented as a frontier discovery or an improvement over the literature.
Its choices make some constructions accessible and algebraically explicit, and
also impose limitations. Say both plainly. Do not contrast our supposed rigor
with other authors' supposed carelessness or dismiss analytic methods as mere
heuristics. Attribute established ideas where they are introduced, and distinguish
an expository choice, a checked identity, a conditional comparison and an open
construction.

The reader knows undergraduate quantum mechanics and linear algebra. Introduce
any further algebra, combinatorics or functional analysis before using it. Explain
the question, the objects and assumptions, then give a readable mathematical
argument and a concrete example. Describe what a result lets the reader do and
what it does not establish. Keep a calm, direct tone; humility means accurate
claims, not repeated apologies or self-deprecation. Avoid repetitive adjectives
such as exact, rigorous, strict, novel or fully constructive where an explicit
hypothesis and equation already make the point.

## Scope that prose must preserve

- Lattice sites, finite CAR Fock spaces and fixed-budget subspaces are finite.
  An ambient polynomial algebra with bounded mode count can still have unbounded
  degree and infinite dimension. Distinguish the carriers every time it matters.
- A global nonzero scalar CCR cannot hold for finite matrices. A protected-budget
  identity, an ambient polynomial CCR and a compressed operator are different.
- Nilpotency of a lowering map does not prove that every exponential of a sum of
  creation and annihilation maps terminates. Preserve the actual hypotheses.
- Finite identities are not a continuum limit, thermodynamic limit, completeness
  of the literature, a general interacting-state identification or a gap theorem.
- A positive algebraic state, a finite vector/density-matrix expectation and a
  coefficientwise formal-series evaluation are not interchangeable.
- CH01–18 implemented Lean is promoted; CH19/A08 Phase B is accepted and Core
  promotion remains open; CH20–21 chapter Lean is unimplemented. The current PDF
  includes CH01–11 and CH19–21, with A01–A04; CH12–18 LaTeX drafts remain private.
  Identify narrative gaps rather than assuming those chapters are in this edition.
- Compiling LaTeX validates document mechanics, not mathematical truth or faithful
  source coverage. Lean proof coverage applies to actual declarations and their
  hypotheses, not automatically to every sentence or displayed formula nearby.

## Uniform notation and continuity

Produce a ledger before global replacements. Record each symbol's object, carrier,
units, sign/order convention, first definition and inconsistent uses. In particular
check lattice length versus physical circumference; mode counts and positive/negative
Fourier orientation; momentum versus spatial fermions; raw and normal-ordered
currents; the order/sign in CCR; charge labels, ground and excitation energy;
ambient versus projected products; hyperbolic parameters and coupling names;
finite versus abstract expectations; formal versus evaluated exponentials; and
raw versus normalized spin/charge currents. Do not choose a convention by majority
vote or silently change a mathematical definition. Mark unresolved choices for
comparison with the exact source/Lean hypotheses.

Each chapter should say what previous results it uses and what question it answers,
and end with a short bridge to the next step. Avoid repeatedly teaching the same
prerequisite. Move appendix arguments into their first main-text use only with one
assigned owner, preserving useful content and labels, then replace redundant
appendix exposition with a reference where appropriate.

## Example of the intended tone

"We follow the standard bosonization program, keeping the lattice size and the
energy restrictions explicit. At fixed size, the fermionic constructions use
finite-dimensional spaces and finite sums. Some bosonic identities are most
naturally expressed on an ambient polynomial space; we state separately when
those identities apply to a finite budget. This presentation is intended to make
the algebra and its assumptions accessible. It does not by itself establish a
continuum limit or replace the broader analytic treatments in the literature."

This paragraph is an editorial example, not an approved replacement for the preface.
The first Jules pass writes a review report only. It must not rewrite chapters,
change notation, modify Lean, run proof searches or alter the verification pipeline.
