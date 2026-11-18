# Prompt 03 — physical finite field dictionary analysis

Date: 2026-10-17. Status: focused local analysis complete; independent review and
scope decision pending. This is not a dedicated reply from an external reviewer,
and it is not an independent second review of itself.

## Verdict

Choose **B: a counterexample to unconditional physical-field equality, with the
corrected target being a typed restricted comparison or explicit residual theorem**.
The result does not disprove CH14's conditional criterion. It shows that the
criterion's full-vector ground premise is substantive and is not supplied by
the numerical current margins. The exact CH14 candidate cannot be declared equal
to the actual finite field from its selected ground coefficient, a formal Gaussian
correlator, or a finite current-moment theorem.

The separate Section 20.2 Weyl-type formal vertex has an additional immediate
equal-point obstruction: its algebraic `W(x)*W(x)=L⁻² I` does not match the
non-scalar physical bilinear product on the full CAR carrier. That is a distinct
candidate and must not be conflated with CH14's finite Taylor candidate.

## Exact actual maps and conventions

The source is [Ch14Mandelstam.lean](../../../Bosonize/Core/Ch14Mandelstam.lean)
and [Ch20CDW.lean](../../../Bosonize/Core/Ch20CDW.lean); their companions are
[CH14](../../../docs/companion/Bosonize/Core/Ch14Mandelstam.md) and
[CH20](../../../docs/companion/Bosonize/Core/Ch20CDW.md). The actual single field
is `A05.liftedAnnihilation`, with normalization `A01.normalization (2*h)` and
the explicit species `Ch06Ext.twistedCharacter`. Its typed map is
`physicalMap : jointBudget Ns Kin → jointBudget (lowerCharge Ns ν) Kout`.
It retains the actual target projection.

The finite candidate `vertexCandidate` has the ordered composition

```text
source zeroMode (twist lift × ζ^(Nν x))
  → projected Klein lowering Ns to lowerCharge Ns ν
  → finite Taylor of projected wPlus on the shifted sector
  → typed identity/cutoff transition Kin to Kout
  → finite Taylor of projected wMinus on the target sector.
```

Rightmost factor acts first in Lean composition. The source phase precedes the
Klein shift. For `m=1,…,M`,

```text
wPlus  = Σ ζ^(+m x) rho(-m) / m
wMinus = -Σ ζ^(-m x) rho(+m) / m
wPlus† = -wMinus,   wMinus† = -wPlus.
```

Thus `wPlus` is the lowering series; `wMinus` is the signed raising series.
The exterior minus sign is part of the definition and cannot be dropped by
calling it a conventional creation exponential. The physical field lowers charge
by `eν`; CDW `c_R† c_L` shifts `(N_R,N_L)` by `(+1,-1)`, and SC `c_R c_L`
by `(-1,-1)`. Adjoint reverses the actual CAR factor order.

## Entire ground image

The source proves `physical_ground_expansion`: on the actual sector sea, the
physical field image is the complete sum over every occupied momentum `k` of

```text
L^(-1/2) × twistedCharacter(k,x) × fermionSign(k, source occupation)
  × targetProjection( erase(source occupation,k) ).
```

Distinct hole configurations are distinct basis vectors. The target projection
may retain or remove each separately. The theorem `klein_zero_ground` establishes
only that the Klein kernel sends the source zero-mode times the sea to its
phase-weighted shifted sea under `pairMargin`; it is not the whole physical field
image. `orderCDW_ground_coeff` and `orderSC_ground_coeff` compute selected
ground-to-ground coefficients, not the full field vector.

### Concrete full-image counterexample

Take one annihilated species with `h=2`, `L=4`, source charge `Nν=0`, source budget
`Kin=0`, target charge `Nν-1=-1`, and target budget `Kout=1`. The band is
`{-1,0,1,2}` and the source sea occupies `{-1,0}`. The two occupied modes produce
different target hole configurations after annihilation: removing `k=0` gives
the target sea `{-1}`, while removing `k=-1` gives `{0}`, a distinct
one-excitation hole state.
At any fixed position each has a nonzero coefficient of magnitude `1/2`, and
the distinct basis vectors cannot cancel.

Set the candidate cutoff `M=0`, which the CH14 definitions explicitly permit as
an empty sum. Then `wPlus=wMinus=0`, both Taylor factors are identities, and the
candidate ground image is just its Klein-kernel target sea. It has no component
along the second hole state. Therefore the full ground-vector equality fails,
although the selected ground coefficient can agree. The source and lowered
target `r2` conditions at `K=0` are `|0|≤2` and `|-1|≤2`, so this is not a
failure of the zero-mode/Klein margin. A cutoff of zero is sufficient to falsify
the universal claim that margins alone imply the full ground identity.

The nonempty-cutoff obligation is substantive too. For one species take
`h=3`, `L=6`, source charge `N=0`, `Kin=0`, target charge `N=-1`, `Kout=2`,
`M=1`, `x=0`, and periodic twist. The band is
`{-2,-1,0,1,2,3}`; the source sea is `{-2,-1,0}` and the target sea is
`G={-2,-1}`. Both pair margins hold. The physical ground expansion is

\[
\frac1{\sqrt6}\left(|\{-2,-1\}\rangle-|\{-2,0\}\rangle+
|\{-1,0\}\rangle\right).
\]

At `x=0` the source phase and Klein phase are both one. On `G`, `wPlus`
annihilates, while `wMinus=-rho(+1)`. The actual current action is
`rho(+1)|G>=|{-2,0}>` and
`rho(+1)|{-2,0}>=|{-1,0}>+|{-2,1}>`. Thus the candidate ground image is

\[
\frac1{\sqrt6}\left(|G\rangle-|\{-2,0\}\rangle+
\tfrac12|\{-1,0\}\rangle+\tfrac12|\{-2,1\}\rangle\right).
\]

All displayed states are retained by `Kout=2`. The extra state and the
half-sized `|{-1,0}>` coefficient prove full-vector mismatch for this
nonempty oscillator cutoff. This exact calculation was independently checked
against the current source definitions in the S6 entry review; it is not yet a
Lean theorem. No statement here identifies the candidates for arbitrary `M`,
charges, twists and budgets.

## What the margin hypotheses do and do not prove

`A05.r2(h,K,N)` is the per-species inequality `2K+|Nν|≤h`. CH11 uses it for
partition Gram/completeness and controlled current actions. CH13 `pairMargin`
requires it in both source and lowered-charge sectors for Klein-kernel formulas.
These are exact useful hypotheses, but they say nothing about:

- equality of the full retained hole sum with the finite Taylor candidate;
- cyclicity of an arbitrarily selected family `G_i` on the chosen source budget;
- the actual physical field recurrence and the candidate recurrence having the
  same residual map for every generator;
- vanishing of an intermediate discarded channel.

CH14's `field_vertex_of_common_residual` asks for all four independent facts:
full cyclic span, full-vector ground equality, physical recurrence, and candidate
recurrence with the same residual. Its theorem `cyclic_common_residual` is sound:
the two residuals cancel on every cyclic word. It does not manufacture the
hypotheses. `projected_recurrence_residual` explicitly contains source and target
excursions. The accepted `Ch20CDW.concrete_discarded_channel_nonzero` shows that
one such channel can be nonzero; the target-zero companion witness shows the
outcome depends on the chosen target cutoff.

## Product and normalization obstructions

For actual ambient CAR fields, the exact product split is

```text
P_t A B P_s = P_t A P_m B P_s + P_t A (1-P_m) B P_s.
```

The last term is an actual operator and is nonzero in the accepted CH20 witness.
No global exact product dictionary may discard it. This is independent of the
source-ground counterexample above.

For Section 20.2's Weyl-type formal vertex, `W_J(x)*W_J(x)=L^(-2)I` on its
auxiliary carrier. In the `L=4` translation-invariant product Slater example,
the physical CAR values are `⟨O_CDW† O_CDW⟩=1/4` and
`⟨O_SC† O_SC⟩=1/4`, rather than `1/16`. More strongly, the physical products
`n_L(1-n_R)` and `n_R n_L` are not scalar operators on the full CAR Fock space,
whereas the formal equal-point product is scalar. This rules out a global
star-preserving identification of those exact normalized operators on the full
carriers. It does not rule out another restricted dictionary with a justified
normalization.

## Corrected mathematical target

The V1 target should keep the actual physical field unchanged and establish one
of these reviewed statements:

1. an exact restricted equality on a specified source subspace, with the full
   ground image, cyclic generators and matching residuals proved;
2. a selected matrix-element or moment identity with explicit source/target
   charges, twists, mode set, total-energy bounds and right-suffix margins; or
3. a controlled finite comparison whose intermediate-projection, omitted-mode,
   normal-ordering, state and dispersion terms are individually named and
   calculated/bounded, with unknown terms left explicit.

Formal Gaussian correlators and the free-sea finite-current theorem can support
individual terms in such a result, but cannot replace an operator dictionary
and state comparison. The corresponding finite-interacting ground state must
be constructed from its specified compressed Hermitian Hamiltonian; it is not
`omegaP` by definition.

## Anchors and validation evidence needed

- [CH14 Lean source](../../../Bosonize/Core/Ch14Mandelstam.lean): `wPlus`,
  `wMinus`, adjoint lemmas, `physical_ground_expansion`,
  `projected_recurrence_residual`, `field_vertex_of_common_residual`.
- [CH20 Lean source](../../../Bosonize/Core/Ch20CDW.lean): actual `orderCDW`,
  `orderSC`, projected residual declarations and the nonzero/target-zero witnesses.
- [Section 20.2](../../../notes/latex/chapters/sections/20.2.tex): physical
  projected products are separated from formal vertices; the equal-point example
  and positive SC formal exponent are current source facts.
- [A08 appendix](../../../notes/latex/appendices/app_a08_states_correlations.tex):
  uncompressed state and coefficientwise formal correlator scope.

Entry review: `/root/s6_theory_review` independently checked the `h=2`, `M=0`
argument, the parameterized `h>=2`, `M=0` family and the `h=3`, `M=1`
full-image calculation against the exact current sources on 2026-10-20. The
review corrected the two h=2 hole labels above. Its evidence and reviewed
hashes are recorded in [the S6 entry review](../v1-s6/entry-review.md). These
obstructions refute equality under margins alone; they do not refute CH14's
conditional criterion or decide every restricted physical comparison.
