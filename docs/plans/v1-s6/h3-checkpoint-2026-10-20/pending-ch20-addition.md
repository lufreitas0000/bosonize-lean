
#### Constructive realization: quantitative physical product residuals (S6)

The finite product comparison retains two geometrically different losses.
For an actual intermediate orthogonal budget projector $P$ and an isometric
embedding $U$ of a selected oscillator or partition carrier whose image lies
inside that budget, insert

$$
I=UU^\dagger+(P-UU^\dagger)+(I-P).
$$

Between the actual field factors this gives the embedded product, the range
inside the budget omitted by the embedding, and the discarded intermediate
budget channel. Endpoint embeddings and their adjoints transport each term
to its stated source and target. Surjectivity of the partition embedding is
not assumed. Replacing the two embedded factors by independently specified
candidates adds the familiar estimate

$$
\|\widehat A\widehat B-V_AV_B\|
\leq\|\widehat A-V_A\|\,\|\widehat B\|
 +\|V_A\|\,\|\widehat B-V_B\|.
$$

The full product bound also retains the norms of both residual terms.

For the Chapter 20 CDW witness, $h=2$ and $L=4$, source and intermediate
budgets are zero, the target budget is one, the twist is periodic and $x=1$.
Choose the target occupation obtained by removing the occupied left mode
$-1$ and creating the right mode $+1$. Equality with this occupation singles
out that contributing pair. The erased intermediate has excitation at least
one and is rejected by budget zero, while the final occupation has charge
$(1,-1)$ and total excitation one and survives the target projection. Its
coefficient is the product of the two field normalizations, the annihilation
character, the conjugated creation character and the two CAR signs. The
characters and signs all have modulus one, and each field normalization is
$1/2$. The coefficient therefore has magnitude exactly $1/4$. The normalized
occupation coordinate inequality proves

$$
\|P_t c_R^\dagger(I-P_m)c_L|\mathrm{sea}\rangle\|\geq\frac14.
$$

This strengthens the earlier nonzero witness quantitatively on the actual
budget subtype. The five comparison obligations remain distinct:
intermediate projection, mode truncation or omitted range, normal ordering
and normalization, state comparison, and dispersion or Hamiltonian
approximation. The one-species Chapter 14 obstruction bounds the complete
candidate error and does not isolate a mode-only cause. No state or dispersion
substitution is made in these fixed-operator comparisons; that absence gives
no later state or spectral approximation. Formal-Weyl equal-point
normalization calculations remain supporting mathematical context unless
separately proved. The finite results establish no physical field equality,
interacting-state equivalence, analytic evaluation or continuum limit.

See the [S6 source](../../Bosonize/Core/V1S6PhysicalFields.lean) and its
[companion](../../docs/companion/Bosonize/Core/V1S6PhysicalFields.md) for the
exact contracts and validation receipts.
