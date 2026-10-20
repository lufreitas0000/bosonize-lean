
#### 14.5 Constructive realization: a quantitative finite field obstruction

The S6 construction uses the same finite occupation Hilbert space and the same
physical normalization. Take one species, half-length $h=3$, circumference
$L=6$, periodic twist and position $x=0$. The source charge and excitation
budget are zero; the lowered target has charge $-1$ and budget two. The source
sea is $\{-2,-1,0\}$, and write $G=\{-2,-1\}$ for the lowered sea.

At oscillator cutoff $M=1$, the source zero-mode phase and Klein-ground phase
are both one. The lowering Taylor factor has cutoff zero and is the identity.
The raising factor is the degree-two Taylor polynomial of the actual
compressed operator $-\rho_1$. The CAR occupation calculation gives

$$
\rho_1|G\rangle=|\{-2,0\}\rangle,\qquad
\rho_1|\{-2,0\}\rangle
 =|\{-1,0\}\rangle+|\{-2,1\}\rangle.
$$

All four displayed configurations lie in the specified target budget. Thus
the candidate's coefficient on $J=\{-2,1\}$ is $1/(2\sqrt6)$. The physical
annihilation field has coefficient zero there: removing one particle from the
source sea cannot produce an occupation containing $+1$, and the target
occupation projection cannot create such a coordinate. Consequently the
physical-minus-candidate error has coefficient $-1/(2\sqrt6)$ on $J$.
Cauchy–Schwarz with the normalized occupation ket gives the verified bound

$$
\|\bigl(A-B\bigr)|\mathrm{sea}\rangle\|
 \geq \frac1{2\sqrt6}.
$$

The budget is a Hilbert subspace with its inherited norm, so this coordinate
estimate applies to the genuinely typed field comparison. The result concerns
the complete physical-to-CH14 candidate error at these parameters. It does not
attribute all discrepancy to omitted modes or alter the conditional field
criterion above. It makes no interacting-state, analytic, continuum or
thermodynamic identification. Exact declarations and review evidence are in
the [S6 companion](../../docs/companion/Bosonize/Core/V1S6PhysicalFields.md).
