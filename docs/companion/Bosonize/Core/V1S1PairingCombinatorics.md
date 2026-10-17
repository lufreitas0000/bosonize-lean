# V1-S1 finite pairing combinatorics

This additive helper supports the oscillator-only ordered Wick theorem.
Its generic finite ordered labels are original word positions; coefficients
are complex numbers. Namespace: `Bosonize.V1S1.Pairings`.

The 14 declarations are `R`, `Good`, `symm`, `no_self`, `erase_inc`,
`erase_good`, `insert_R`, `insert_good`, `extendPair`,
`extendPair_bijective`, `sumOn`, `sumOn_first`, `sumOn_as_sum`, and
`sumOn_empty`. `R` records undirected incidence of canonically oriented
edges. `Good V P` requires edges with increasing endpoints, incidence exactly
at vertices in V, and a unique partner for every incident vertex.

For x smaller than every label in S, `extendPair` inserts the edge from x
to y∈S in a residual pairing on S.erase y. The bijectivity theorem proves
injectivity using the unique partner at x and erasing the inserted edge;
surjectivity selects x's partner and removes its edge. Thus each perfect
matching occurs once. The weighted sum identity factors that edge with its
ordered weight C(x,y), using `Fintype.sum_equiv` and `Finset.prod_insert`.
The empty vertex set has exactly the empty matching and weight one.

Independent source/proof/amendment/migration review by
`/root/s1_interface_review` passed for exact helper SHA-256
`33fefe1fafbdde6c544925a641ac8cdec496ce571f3036558500a53ddb0ddeff`.
The helper moved to Core with no byte changes. The reviewed lock amendment
added only this helper and the main module's import, preserving old contracts.
The complete-source freeze now preserves it alongside all earlier Core files.
All 14 declarations pass the fresh axiom audit, using only standard axioms;
there are no placeholders or compiler warnings.

See the [main companion](V1S1OrderedWick.md) for the exact review history,
validation commands, source/manifest hashes and finite/analytic scope boundaries.
The public Wick predicate's equivalence with `Good univ` is proved in the main
module, so this helper introduces no alternative oscillator functional.

[Source](../../../../Bosonize/Core/V1S1PairingCombinatorics.lean).
