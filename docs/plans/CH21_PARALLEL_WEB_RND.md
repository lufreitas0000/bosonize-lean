# CH21 implementation proposal and parallel web-LLM prompts

Status: proposed R&D only, 2026-10-16. No CH21 Lean interface is accepted or frozen
by this document. CH20 is complete in Core; CH20b is a separate dependency scope.

## Recommended implementation

Build the finite spinful chapter in `BosonizeStubs/Ch21SpinfulModels.lean`, namespace
`Bosonize.Ch21`, with its companion. Keep A09's spin/charge and Umklapp material
here; do not create a second duplicate A09 interface. Cite existing A10 results.
Start with one reviewed staging interface; split into domain modules only if a
reviewed dependency design justifies it before locking, rather than during proofs.

Existing guidance `docs/webllm/guidance/ch21_phase_a_sources.md` is advisory and
dated: its statement that CH19/20 cannot be imported is superseded by their Core
promotion. Check the live verifier and exported APIs. CH20 exposes `orderSC`,
not the guidance's speculative `orderParamSC`. Reuse its projected SC residual
identity for the two singlet channels where the exact types fit. Its private
helpers are not a public dependency API. Do not assume its two-species witnesses
prove the four-species spatial-sum Umklapp witness.

Use a generic finite linearly ordered species type with four distinct labels,
represented as two A06 branch records plus cross-distinctness proofs. Concrete
species order is L-up=0, L-down=1, R-up=2, R-down=3 in Fin 4; ascending momenta.
Raw currents are sums/differences without sqrt(2), so self-CCR coefficient is 2m.
Mixed charge/spin commutation is restricted by both species' explicit A06 margins;
globally retain the difference of edge commutators. The integer charge/spin image
is the parity sublattice, with a proved inverse and the excluded pair (1,0).

The singlet is c_Rup c_Ldown - c_Rdown c_Lup, with distinct orthogonal target
sectors and separate middle budgets. Retain both projection remainders. Umklapp
is c†_Lup c†_Ldown c_Rdown c_Rup, with species shifts (+1,+1,-1,-1), and
H_U=(g_U/L) sum_x(O_U(x)+O_U(x)†), real g_U and L=2h. A leakage theorem needs a
nonzero outward SPATIAL SUM outside the box; nonzero total H_U psi is insufficient.
The proposed general witness coefficient -g_U/L² must be independently derived,
including signs, momentum uniqueness, and cancellation of the site character.
Begin its proof engineering with h=2, g_U=1 and expected coefficient -1/16;
keep the general h>0 family as an explicit contract if accepted in Phase A.
Never replace it by the numerical example after freezing.

### Phase A: parallel research, then one authoritative interface

Send the common prompt below to independent web chats with roles A1–A4.
They return proposals and counterexamples, not competing canonical source edits.

| Role | Owned research | Required output |
|---|---|---|
| A1 | Carriers, labels, raw currents, margins, parity lattice, quadratic block/velocity statements | Complete proposed data; exact contracts; dependency map; equal-velocity and off-margin checks |
| A2 | Two singlet channels, target orthogonality, CAR/Klein phases, CH20 reuse | Exact typed residual contracts; source/middle/target ledger; phase calculations and nonzero examples |
| A3 | Multispecies charge commutators, Umklapp, charge boxes, leakage, explicit coefficient | Fully specified witness; sign/Fourier derivation; cancellation/Pauli counterexamples; proof-risk report |
| A4 | Adversarial review, independent of A1–A3 | Counterexamples or PASS/REVISE findings with source anchors; check normalization, hidden assumptions and vacuity |

A4 first derives its checks from the same sources independently, then reviews the
other three outputs. One integrator reconciles their proposals into ONE module
and companion, preserving a claims ledger. Recheck exact APIs locally. Require
complete data, one `by sorry` per theorem, fresh Phase A elaboration/data-axiom
checks, independent review of exact hashes, then an atomic scoped lock commit.
The number of contracts is determined by that reviewed artifact; do not inherit
a historical "47" count. Before freezing, include required helper contracts for
the expensive witness so later proof workers need fewer new declarations.

### Phase B: parallel work only after the common lock exists

| Batch | Ownership and dependency order |
|---|---|
| B1 | Raw-current algebra, adjoints, parity/inverse, quadratic block/velocity claims; independent of CAR witness expansion |
| B2 | Multispecies number/field commutators, Umklapp charge shifts, self-adjointness, sector compression |
| B3 | Singlet target orthogonality, exact two-channel residual, ground CAR/Klein phases; use Core CH20 and accepted B2 helpers if needed |
| B4 | Explicit Umklapp witness: occupation membership, ordered signs, unique coefficient, site-character sum; then leakage and projection noncommutation using B2 |

B1/B2 and the dependency-free parts of B3/B4 can run together. Contracts depending
on a new helper wait for its accepted proof or carry it as an explicit UNPROVED
interface assumption in research only. Never claim downstream acceptance while
an imported proof still uses sorryAx. Workers own disjoint declaration lists;
one local integrator merges proof bodies sequentially against the locked baseline.
Do not send four complete-file replacements to overwrite the same canonical file.
Independent review comes from a chat that did not author that batch.

## Common Phase A prompt — copy into each independent chat

```text
You are independent CH21 Phase A researcher ROLE=[A1/A2/A3/A4] for Bosonize-Lean.
Your assigned research is the matching row of CH21_PARALLEL_WEB_RND.md.
Work only from the attached source bundle, identified by BASE_SHA and SHA256
manifest. If required material is absent, name the exact missing source instead
of inventing APIs. State whether code is locally compiled or an unverified proposal.
Do not call paid APIs or other agents. Do not edit or weaken existing Core.

Read notes/md/ch21_spinful_models.md; the spin/charge and Umklapp sections of
notes/appendices/a09_duality_spin_and_umklapp.md; relevant A03/A06/A10 material;
docs/webllm/guidance/ch21_phase_a_sources.md; the exported Core signatures and
reference excerpts included in this packet. Treat guidance/sketches as candidates.
CH19 and CH20 are now Core; verify exact exports. Do not depend on CH20b formal
vertices or infer a finite-CAR unitary from parameter substitutions.

Respect Fin4 order (Lup,Ldown,Rup,Rdown), raw currents, A06 commutator sign and
both-species margins, parity-constrained integer labels, exact adjoints, separate
singlet target/middle budgets, all projection residuals, real gU/L normalization,
and a nonzero outward spatial-sum leakage hypothesis. No KT flow, Mott-gap,
analytic exponential or continuum completion claims.

Return: (1) source-anchored mathematical scope and conventions; (2) complete
proposed data and exact one-sorry theorem contracts for your assigned area;
(3) dependency/proof sketch for each contract; (4) explicit non-vacuity witnesses;
(5) counterexamples/edge cases and unresolved questions; (6) exact proposed
editable declaration ownership. Do not change another role's interface silently.
A3 must derive the full -gU/(2h)^2 coefficient independently, not quote it as fact.
A4 initially derives its adversarial tests without reading A1–A3 conclusions,
then issues source-anchored PASS/REVISE findings on their exact artifacts.
Do not describe this research output as accepted Phase A.
```

## Phase A integrator/reviewer prompt

```text
Reconcile A1–A4 into ONE proposed Ch21SpinfulModels module and companion.
Resolve conflicting conventions explicitly; retain exact source provenance.
Freeze no interface until independent review and fresh local elaboration/data
axiom checks pass. Every def/instance is complete; each theorem has exactly one
by sorry. Include leakage/sign/character and singlet helper contracts before
locking where necessary. Return the exact target files in the packet's required
response envelope, with packet_id/base_sha preserved. Never invent an envelope.
An independent reviewer must inspect the exact final source hash, carriers,
margins, parity image, target types, signs, normalization, nonzero spatial sum,
Pauli blocking and source fidelity. Compiler success with sorry is elaboration,
not proof acceptance. Report unresolved findings rather than silently weakening.
```

## Common Phase B prompt — copy once per disjoint batch

```text
You are CH21 Phase B proof worker BATCH=[B1/B2/B3/B4].
Use the attached locked packet BASE_SHA, packet_id, lock digest, source hashes,
Core closure and ASSIGNED_DECLARATIONS list. Your output is a candidate until
fresh local compiler, warning, lock and transitive-axiom audits pass.

Prove ONLY the listed frozen declarations. Preserve names, binders, conclusions,
definitions, imports, namespaces, options and attributes. Use local have proofs;
new top-level helpers require a separate concrete proposal and independent scoped
review, not a regenerated lock. Do not use sorry/admit, extra axioms, native_decide,
or linter suppression. Do not edit another batch's proof bodies.

Return exact proof replacements with declaration anchors, or the packet's required
full-file envelope if the verifier demands it. In the latter case preserve every
unassigned byte from the supplied baseline; the local integrator extracts only
owned replacements. Include a dependency ledger marking each used staging helper
PROVED/UNPROVED, the mathematical argument, and complete diagnostics if available.
Do not fabricate local Lean execution. After three failed attempts at the same
unchanged goal, retain candidate/goal/full diagnostics and request independent
bounded diagnosis. Do not bypass the obstacle by weakening the statement.

B4: distinguish h=2 engineering evidence from the general h>0 theorem. Check all
four prior insertions/erasures, odd total 8h-1, unique momentum support, constant
site character, opposite-charge adjoint exclusion, and gU≠0. Leakage must concern
the actual spatial sum, not an arbitrary nonzero site or total H_U psi.

An independent reviewer should check exact proof artifacts and the frozen
contract. Final local integration requires zero warnings/placeholders, permitted
axioms only (propext, Classical.choice, Quot.sound), strict committed locks,
fresh module/dependency builds and required CI. Stop at Phase B; do not promote.
```

## What to attach to every web chat

Export a hash-bound flat packet from the CURRENT committed main. Include the
owned source/contract list, chapter and relevant appendix sections, source
corrections, exact Core signatures/definitions with their dependency closure,
selected reference excerpts from the guidance's cited paths, compiler version,
and response format. Check reference files actually exist before dispatch.
If literature excerpts are unavailable, record the gap; do not claim source review.
After Phase A acceptance, re-export Phase B packets from its new lock/base.
Return responses through the existing preview/ingest/sandbox verifier, with full
compiler feedback on retries. Independent web chats are operated by the user;
this proposal does not dispatch provider calls or claim their results.
