# CH15/A06 Phase A independent review — 2026-10-13

Reviewer: independent agent `/root/ch15_independent_review`, separate from the staging integrator `/root`. Scope: the actual imported browser draft and the exact staged modules. Verdict: **PASS for Phase A mathematical contracts and source-preserving staging**. This is not proof completion; all 23 theorem bodies remain `sorry`.

## Exact reviewed sources

| File | SHA-256 |
|---|---|
| `/home/lucas/Projects/.packets/worktrees/ch15_phase_a-20261013T120725Z-0a118a80-a1577336/docs/webllm/drafts/ch15_phase_a.md` | `275a433fa43203b7574e26d69b7ba4783433bb898be0d30389e0b5a1edd003d0` |
| `BosonizeStubs/A06ChiralFields.lean` | `f65574faa2ee8591476c1a9c9a9dba634aa4bd82397e0bd277c1d027f9aaafa1` |
| `BosonizeStubs/Ch15DualFields.lean` | `778a972ff2cd909c25e83f4f6e266af2ddacfee2d71d150391549a3c0e38d903` |
| `scripts/audit/ch15_phase_a_oracle.py` | `a8544e23428f4e462d97718d85c616ec8d08cc11cf5020cb1c3062e9281efca2` |
| `note/ch15_phase_a_oracle_2026-10-13.json` | `88a2f452b82cabbcb111f679f5546453151ca7aa2fccf4895e9ee92fadfbf4a7` |

Exact comparison executed against the artifact's sole Lean fence: `A06ChiralFields.lean` equals the original text through `end Bosonize.A06`, ignoring only final newline whitespace. `Ch15DualFields.lean` equals the original CH15 namespace block with the added import `BosonizeStubs.A06ChiralFields`. This split changes no definition, theorem header, assumption, conclusion, instance, namespace or proof placeholder. The earlier `import Bosonize` remains in A06 and is available transitively in CH15. Existing Core sources were not edited by this reviewer.

The staged source contains 16 A06 theorem/lemma placeholders and 13 A06 data declarations, plus 7 CH15 placeholders and 2 CH15 data declarations. The integrator reports both modules built with exactly 23 expected `sorry` warnings; this reviewer checked source mathematics and exact extraction, rather than rerunning that compiler invocation. Acceptance still requires the integrator's direct elaboration/data-axiom evidence and scoped lock verification.

## Mathematical evidence

1. **Actual joint-budget CCR transport.** `A05.jointBudget` is `Ch07.speciesBudget`, defined by species charge constraints and a total excitation bound. For `h>0`, `Ch07.excitation_nonneg` implies each individual excitation is bounded by total excitation and hence by `K`. Each allowed occupation ket factors through `tensor_kets`/`joint_species_configuration`. `A05.rho_tensor` transports the existing `Ch10.rho_signed_ccr` to one species at the stated margin. Coordinate-space span induction extends the action identity to every actual joint-budget vector. This does not assume a product budget and remains a Phase B proof obligation.
2. **Signs and normalization.** Core coefficient is `schwingerCoefficient m n = if m+n=0 then -m else 0`. Positive retained `m` gives `[rho(-m),rho(m)]=+m`. Expanding the field coefficients, including `i^2=-1`, yields the positive orientation kernel `S(x-y)` and negative orientation `-S(x-y)`. Distinct species commute globally. Thus both self-commutators cancel on the common input, and the mixed commutator is `2S(x-y)` with no missing normalization factor. The sine formula needs a canonical root and is not asserted for arbitrary primitive roots.
3. **Margins and carriers.** `2M+K+|Ns nu|<=h` bounds every current pair by the frozen single-species sufficient margin. Intermediate current products may leave the input budget; ambient endomorphisms are appropriate. No global scalar CCR is claimed.
4. **True adjoints.** `A05.rho_adjoint` exchanges signed current modes. Character conjugation exchanges signed spatial modes and conjugates `i` to `-i`; the full field is self-adjoint under `LinearMap.adjoint`. No hypothetical star algebra is required.
5. **Periodic characters and differences.** Primitive-root periodicity makes residue representatives compatible with spatial shifts and negative exponents. Additive forward differences need no commutative operator multiplication. Translation permutation implies the finite difference spatial sum is zero.
6. **Dirichlet statements.** At zero separation every exponent is zero, giving cardinality `2M+1`, even for arbitrary complex `zeta`. Under primitive-root/no-alias assumptions only retained mode zero survives the spatial sum, giving one. `2M<2h` is sufficient; it is stronger than the minimal `M<2h` needed solely for that sum.
7. **Zero-mode contradiction.** Summing the proposed pointwise equation over the periodic lattice gives zero on the commutator side and `c` times the ground ket on the Dirichlet side. `c!=0` and the frozen `ground_ne_zero` contradict this. This is a genuine nonzero-vector obstruction, not a statement restricted to a potentially zero subspace. It does not rule out a zero-mode-subtracted kernel.
8. **Concrete witnesses.** `h=4,M=1,K=0,Ns=0` and distinct `Fin 2` indices satisfy admissibility, `1<=M`, no alias and both margins. Frozen `ground_mem_budget` and `ground_ne_zero` support membership/nonzeroness. The witness assertions remain stubs until proved in Phase B.

Some hypotheses are redundant for individual results: positivity/no-alias on cancellation theorems and CCR margins on the obstruction are stronger than necessary. They do not invalidate the contracts. Retain them for this reviewed baseline; any later cleanup is a documented scoped interface amendment if required by warnings or intended minimality.

## Independent reproducible numerical check

Run `python3 scripts/audit/ch15_phase_a_oracle.py --output note/ch15_phase_a_oracle_2026-10-13.json`. The standard-library script reconstructs finite hopping/CAR signs in the occupation basis, independently of Lean implementation and without external dependencies. Parameters are `h=4,M=1,K=0,Ns=0`, two species and `zeta=exp(2*pi*i/8)`. It checks 64 spatial pairs for the two self-commutators, mixed commutator, differentiated mixed commutator, and spatial kernel/difference sums on the nonzero ground input.

Fresh result: PASS with maximum operator residual `3.552713678800501e-15`, kernel sum residual `3.3306690738754696e-16`, threshold `1e-10`. At `x=1,y=0`, mixed ground action coefficient is `2.82842712474619 i`, nonzero and equal to `2S`. These are numerical finite-ground-input checks, **not Lean proofs, exhaustive validation, or evidence for other cutoffs/charges**.

## Approved boundary

Freeze the reviewed A06/CH15 finite declarations after direct compiler/data-axiom checks. Reserve Hamiltonians, normal-ordering, spectral derivatives, continuum limits, inverse kernels and unconditional CH14 field identifications for separately reviewed work. Mathematical source meaning is supported; the actual Lean proof obligations, especially joint-budget transport and finite root orthogonality, remain Phase B work.
