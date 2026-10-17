# Chapter 20 completion questions and independent web-chat prompts

Date: 2026-10-17. Status: preparation for theoretical review only. No new Lean
interface, proof batch, external dispatch or mathematical acceptance is created.

## What CH20 and CH20b mean

CH20 has one numbered place in the book. Its accepted finite theorem package is
`Bosonize/Core/Ch20CDW.lean`: 64 original contracts, Phase C complete. It covers
actual finite CAR order parameters, charge/adjoint/projected-product identities,
an explicit nonzero discarded channel, and qualified scalar/phase duality results.

CH20b is a working label for the still-open Chapter 20 completion bridge, including
A08/A09 support and comparison issues inherited from CH14/CH19. It is not a new
book chapter or a claim that the already accepted finite proofs are incomplete.
Sections 20.2 and 20.3 now contain mathematical draft constructions of formal
vertices and model duality. Those drafts do not supply Lean acceptance. Some
proposed stronger finite-CAR identities may be false and require corrected targets.

Thus: finite CH20 package complete; broader Chapter 20 research program open.
Finishing that program requires reviewing the theoretical targets, constructing
what is possible, and recording obstructions or explicitly agreed exclusions.
A finite CCR trace obstruction cannot be solved by more proof search.

## Send one complete file to each independent chat

Each prompt repeats the common mathematical baseline and its own question.
Copy the complete file into a fresh chat, or attach that single Markdown file.
No local filesystem access is assumed. These are discussion prompts, not JSON
ingestion packets; save the full response with the prompt filename and date.
No additional attachment is needed for the stated mathematical question. If the
reviewer needs implementation-specific details, supply the exact requested source
from the hash manifest rather than an invented API.

| Question | Self-contained prompt | Expected theoretical result |
| --- | --- | --- |
| Can the existing positive algebraic state support a complete ordered Wick theorem? | [01-wick-moments.md](01-wick-moments.md) | Ordered Wick/moment theorem or explicit missing hypotheses |
| Which formal charge/oscillator vertex correlator is actually justified? | [02-formal-vertices.md](02-formal-vertices.md) | Charge phases, formal Gaussian correlator and normalization audit |
| Can the actual finite CAR field be identified with a bosonic candidate? | [03-finite-field-dictionary.md](03-finite-field-dictionary.md) | Physical finite field dictionary or a counterexample/corrected criterion |
| What finite interacting state exists, and what can be compared with ωP? | [04-finite-interacting-state.md](04-finite-interacting-state.md) | Constructed finite state and a precisely typed comparison |
| What is the precise algebra/state duality, and can it act on finite CAR? | [05-duality-and-state-transport.md](05-duality-and-state-transport.md) | Algebra/state family transport and separate finite implementability verdict |
| What controlled finite comparison would close the Chapter 20 program? | [06-comparison-and-residuals.md](06-comparison-and-residuals.md) | Controlled finite residual/comparison target and bounded closure proposal |

Questions 1 and 2 concern the uncompressed/formal construction. Questions 3 and 4
concern the physical finite comparison and can expose obstructions independently.
Question 5 must separate formal duality from finite implementation. Question 6
integrates the available results into a finite comparison target; send earlier
answers as labeled, unverified proposals when available, never as accepted facts.

## Decision gate before implementation

For each answer record its exact claims, carrier, hypotheses, proof argument,
counterexamples, unresolved assumptions and source anchors. Obtain independent
review of the reconciled proposal. Choose which constructions, obstructions and
finite comparisons define version-1 Chapter 20 completion before freezing any
new interface. The user retains substantive scope decisions.

The finite-AQFT critique in the user's Obsidian inbox remains a research agenda.
Its assumed unconditional field equality, finite-budget interacting vacuum and
completed CH21 leakage are not accepted baseline facts. Coupled wires, entropy,
RG and quench programs do not become version-1 dependencies by appearing there.
The private critique itself is not copied into the public repository.

Version 1 remains standalone. After its agreed CH20 scope, finite CH21 through
Phase C and the closure/release audit, version 2 may begin as a complete refactor
built on finiteQMB. No finiteQMB dependency or migration work begins here.
