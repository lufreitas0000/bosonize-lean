
## Constructive realization in Lean: finite interacting states and moment limits (S5)

The S4 comparison evaluates transformed observables in the free finite sea.
An interacting state requires a separate construction. Fix admissible integer
charges $N_\nu$, a regulator $h>0$, and a total excitation budget $K$.
Let $W_{h,N,K}$ be the actual fixed-charge budget subspace of the finite CAR
Hilbert space, and let $i:W_{h,N,K}\hookrightarrow\mathcal H_h$ be inclusion.
The interacting operator used here is the Chapter 17 bosonized Hamiltonian,
including its full charge zero-mode and chemical-potential terms. Its budget
Hamiltonian is
$$
H_W=i^\dagger H i.
$$
Compression retains the effect of leaving and returning to the budget inside
an ambient product. In general it does not preserve products:
$i^\dagger XYi$ need not equal $(i^\dagger Xi)(i^\dagger Yi)$.

Inclusion is isometric, $i^\dagger i=1_W$, and $ii^\dagger$ is the actual
coordinate projection onto the budget. The ambient Hamiltonian is Hermitian,
so $H_W$ is Hermitian. The admissible finite sea supplies a nonzero vector in
$W_{h,N,K}$. Finite-dimensional spectral theory therefore gives a unit vector
$\psi$ and a real energy $E$ satisfying
$$
H_W\psi=E\psi,\qquad
E\|v\|^2\le\operatorname{Re}\langle v,H_Wv\rangle
\quad(v\in W_{h,N,K}).
$$
This is a minimum on the entire budget. It makes no assertion that $i\psi$
minimizes the uncompressed ambient Hamiltonian. Existence here requires no
small-coupling assumption: every nonzero finite Hermitian problem has a
lowest eigenvalue, although that fact supplies no uniform regulator limit.

The corresponding functional on ambient operators is
$$
\omega_\psi(X)=\langle\psi,i^\dagger Xi\psi\rangle
             =\langle i\psi,Xi\psi\rangle.
$$
It is complex linear, normalized at the identity, and positive because
$\omega_\psi(X^\dagger X)=\|Xi\psi\|^2$. Its definition places compression
only outside the whole ambient observable.

The excitation filtration gives a sharp obstruction to unrestricted moment
matching with the squeezed oscillator functional. For $m>0$, negative current
transfer lowers the total excitation grade by $m$. Consequently
$$
K<qm\quad\Longrightarrow\quad
\rho_\nu(-m)^qv=0\qquad(v\in W_{h,N,K}).
$$
The grade has a nonnegative floor; this argument uses the actual lowering
map, rather than deducing nilpotence from finite dimension. It follows that
$$
\langle v,\rho_\nu(m)^q\rho_\nu(-m)^qv\rangle=0.
$$
The same vanishing is proved separately for products of compressed currents:
lowering stays in the budget, which justifies transporting its powers through
inclusion. The two compression placements are separate results.

Under the fixed raw dictionary $C_{\nu,m}\mapsto\rho_\nu(m)$ and
$A_{\nu,m}\mapsto\rho_\nu(-m)$, the squeezed oscillator value instead is
$$
\omega_P(C_{\nu,m}^qA_{\nu,m}^q)=q!(m s^2)^q.
$$
For nonzero squeeze and $K<qm$, this value is positive. Thus no budget vector
state can match all these raw oscillator moments. This does not contradict
S4's word-dependent, inverse-Bogoliubov comparison in the free sea: it uses a
different state/observable construction and keeps its finite margins explicit.

A complete small model demonstrates the issue already at selected quadratic
moments. Take two species, zero charges, $h=8$, $K=M=2$, and
$(v_F,g_4,g_2,\mu)=(1,32\pi,30\pi,\mu_{\rm canonical})$.
The normalized partition basis is ordered as vacuum, $R1$, $L1$, $R11$,
$L11$, $R1L1$, $R2$, $L2$. Here $R11=C_{R,1}^2Ω/\sqrt2$, $L11=C_{L,1}^2Ω/\sqrt2$,
$R2=C_{R,2}Ω/\sqrt2$, and $L2=C_{L,2}Ω/\sqrt2$.
Its span is the entire budget, of dimension eight.
Writing $\alpha=\pi/8$, the derived matrix has diagonal
$\alpha(0,17,17,34,34,34,34,34)$, with the only off-diagonal entries
$H_{0,5}=H_{5,0}=15\alpha$. Every entry is obtained from the actual currents
and the Chapter 17 operator, including the final projection of channels
outside the budget.

The full spectrum, with multiplicities, is
$$
\alpha(17-\sqrt{514}),\quad
17\alpha\ (2\text{ times}),\quad
34\alpha\ (4\text{ times}),\quad
\alpha(17+\sqrt{514}).
$$
With $\eta=15/(17+\sqrt{514})$, the selected ground vector is
$\psi=(|0\rangle-\eta|R1L1\rangle)/\sqrt{1+\eta^2}$.
Together with this ground vector, the remaining eigenvectors form a complete
orthonormal basis, so the
minimum is verified on all eight dimensions, not only on the coupled block.
For ambient products with final compression, its exact moments are
$$
\omega_\psi(\rho_R(1)\rho_R(-1))
 =\frac{1-17/\sqrt{514}}2,\qquad
\omega_\psi(\rho_R(1)\rho_L(1))
 =-\frac{15}{2\sqrt{514}}.
$$
Both differ from the corresponding oscillator values $9/16$ and $-15/16$ at
$c=5/4,s=3/4$. The concrete example supports the general finite-state
construction and obstruction. It supplies no physical-field equality,
continuum exponent, thermodynamic gap, or analytic limit. Physical-field and
residual norm comparisons remain S6 work.

See the [S5 companion](../../docs/companion/Bosonize/Core/V1S5FiniteInteractingStates.md)
and [finite-state source](../../Bosonize/Core/V1S5FiniteGroundState.lean) for
precise contracts and validation evidence.
