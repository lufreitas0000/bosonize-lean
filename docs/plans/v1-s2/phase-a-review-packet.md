# V1-S2 Phase A specification candidate: charge words and formal vertices

Date: 2026-10-17. Status: **S1 dependency accepted; actual S2 Lean interface independently reviewed PASS and scoped-locked in commit `0610d1495ebc4e95dec323c27faf22966e55e9d2`; Phase B is in progress.** The interface review covered Lean SHA-256 `984132893e986956592cf291bba2ed4ff3ddfc8ba61b748f298814068d046bd7` with packet snapshot `57f336cb6c5ff9dd9656bf7a7e775ea0f63d4b2b7f17044557b6bfe2c31b2fbf` and companion snapshot `6122a5513a52709b246265cd75760cf7197d6233bdd1c5429d9501fa384a1dbb`.

This packet records the independently checkable S2 mathematical interface and
convention derivations. The accepted S1 homogeneous-linear-form, ordered-Wick,
pull-through, and all-orders single-form-moment declarations are imported from
Core. The S2 correlator remains a Phase A contract until its proof is completed.

## Source identity and baseline

Original specification prepared on `main` at HEAD `728987b0e939fd11a0dbfd29a8ecdc6a4368ca17`. Current implementation baseline is `main` at `84d4243df842307050ce03125e14419ed92734fd`, Lean toolchain
`leanprover/lean4:v4.35.0-rc4`. The worktree has pre-existing tracked and
untracked changes; none are modified by this packet. Recompute hashes before
review or implementation.

| Source | SHA-256 |
|---|---|
| `Bosonize/Core/A08OscillatorStates.lean` | `ed3ef9f87c9be26460004fd52efbdd7f0a2490b544c990cc89e6178f0a97ee35` |
| `Bosonize/Core/Ch19Correlations.lean` | `845e95b619fca515b25c2a103071ba1fa0fdfa46ddd12081440ddfbdae902339` |
| `Bosonize/Core/Ch13KleinFactors.lean` | `9a4a7ed40e514a5e57345ad731f23c967b4e725e388d5d9b7b6c2d36a65f5c32` |
| `Bosonize/Core/Ch14Mandelstam.lean` | `0d3feed562023e5d8a20027021014cc56512d636b58848fa7a8122b61cc320fc` |
| `notes/latex/chapters/sections/20.2.tex` | `5186686ca8ce8cddb06d4c81d5dfb89544ea76f11f326dce53cdd6ec3921fbf9` |
| `notes/latex/appendices/app_a08_states_correlations.tex` | `88e10bdda2822f9673cc44e80bc3e278202f70a7cef867a4f4d0d98d2f6ec63a` |
| `docs/plans/ch20-theory/02-formal-vertices.md` | `6bd7271a6cebe94ee6da780d252aa99a54632cec77625507a5d5a1dd5c01fe87` |
| `notes/review/review: Formal CDW-SC vertex correlators.md` | `004747b56b82581e170472a27a80f75fb6b393458331cb2aa6026e3dd66bfd80` |
| `notes/review/review: Formal charge-oscillator vertex correlators.md` | `f7a123ce93ee750207d633c81a47a26d5386a7f3c45838278078224a7dfc13a1` |
| `docs/plans/v1-s1/phase-a-review-packet.md` | `af140bf23f026590114b8b537a0a60c3dfe1bfc996691f18254f4b540ef8bc45` |

The original S1 packet was superseded by the promoted Core module and its companion. The accepted declarations are in `Bosonize/Core/V1S1OrderedWick.lean` (SHA-256 `f26d52cb29008f7d39030157368b7b9131bf14a4db173e97ef404062220852a9`) and helper `Bosonize/Core/V1S1PairingCombinatorics.lean` (SHA-256 `33fefe1fafbdde6c544925a641ac8cdec496ce571f3036558500a53ddb0ddeff`). The reusable interface includes `OscLinearForm`, `linearElement`, `contraction`, `wordElement`, `wordForms`, `orderedPairingSum`, `omegaP_pull_through`, `omegaP_ordered_wick`, `omegaP_odd_word_zero`, `omegaP_single_odd_moment`, and `omegaP_single_even_moment`; `dressedGeneratorForm` and `dressedForm` encode conversion to the forward dressed coordinates. The S1 companion records independent PASS, source hashes, zero-placeholder audits, and Phase C promotion. Recompute all hashes at each S2 gate.
## Reconciled carrier and formal algebra

Fix `h : ℕ` with `0 < h`, `L = 2*h`, finite `M : ℕ` (including `M=0`), and
`hp : Bosonize.Ch18.HyperbolicPair`. Let `c=hp.c`, `s=hp.s`, so
`c²-s²=1`. Positions are elements `x : ZMod L`; phase characters use a
primitive `L`th root `ζ` (the repository's `A01.canonicalRoot L`). An integer
lift of a position is used only inside `ζ^(n*x)`. Independence of the lift is
the root-order identity `ζ^(n*(x+kL))=ζ^(n*x)`. The condition `h>0` makes
`L>0`.

The charge vector space is `ChargeVec := ℂ`-valued finitely supported
functions on `ℤ × ℤ`, with basis `|N_R,N_L⟩`. The oscillator polynomial carrier
is exactly A08's `OscPoly M = MvPolynomial (OscMode M) ℂ`: there are finitely
many modes but no degree cutoff. Use the algebraic tensor product
`ChargeVec ⊗[ℂ] OscPoly M`, with the charge vector functional
`[N]`-coefficient and the existing polynomial functional `omegaP M hp`.
Their tensor product is the joint coefficient functional. It is a vector
functional; no multiplicativity of `omegaP` is inferred.

The oscillator coefficient syntax is the monoid algebra of finite words in
A08's oscillator generators. Its dagger conjugates coefficients, reverses each
word, and swaps creator/annihilator generators. Evaluation sends each word to
A08's `wordElement` in the free algebra and respects multiplication. Operator
equalities needed for commutation are proved after applying A08's polynomial
representation; the syntax algebra is not assigned literal CCR relations, and
no global adjoint is asserted for arbitrary `Module.End`. The charge/oscillator
vector carrier is `ChargeVec ⊗[ℂ] OscPoly M`. Its joint linear functional is
the tensor lift of source-charge coordinate evaluation and polynomial vacuum
coefficient. A syntax coefficient acts through A08's polynomial representation
after inverse Bogoliubov pullback; its vacuum matrix coefficient is exactly
`omegaP M hp`. The coefficient functional on a charge word and oscillator
word is the product of the source charge matrix coefficient and this `omegaP`
value. This is a vector functional; no multiplicativity of `omegaP` is used.

For represented adjoints on the tensor carrier, the Phase A source defines a
product sesquilinear pairing by the tensor-product basis indexed by a charge
and an A08 oscillator monomial. Its diagonal weights are
`oscMonomialNorm`, so on simple tensors it is required to factor as
`chargePairing * oscPairing`. The represented coefficient action must satisfy
the adjoint identity for this pairing, and the joint functional must equal
the matrix coefficient at `|N> ⊗ 1`. This basis-defined pairing supplies the
explicit bridge from coefficient dagger to represented action without a
global star instance on arbitrary endomorphisms. The exact interface passed
independent Phase A review; these laws remain theorem contracts for Phase B
proof.

For formal series, the Lean candidate currently stores each coefficient as a
finite multiset of charge/oscillator monomials. Multiplication is finite
Cauchy convolution with monomial multiplication; adjoint is coefficientwise.
This representation makes adjoint reversal a literal coefficient equality
while retaining finite multiplicities. The central formal variable `t` is
the degree index and is fixed by adjoint. Define `Exp_f(i*t*X)_n =
(i*X)^n/n!`; each coefficient is a finite expression. Prove
`[X_J(x),X_J(y)]=0` in this represented coefficient algebra before using the
formal binomial identity.
Do not posit a global star on arbitrary `Module.End` or identify literal CCR
equalities in A08's free algebra.

The S2 candidate imports `Bosonize.Core.V1S1OrderedWick` and must use its proved general-moment interface. No `sorryAx`, new axiom, or theorem proposition is a substitute. The dependency evaluates every power of a homogeneous oscillator linear form from its ordered self-contraction.

## Canonical CH13 convention and explicit gauge adapter

For two ordered species `R < L`, CH13 defines
`phaseExponent h N ν = Σ_{η<ν}(h+Nη) + (h+Nν-1)` and lowers `Nν` by one.
Thus its abstract basis-shift coefficients are

| shift | CH13 coefficient |
|---|---|
| `R` lowering | `(-1)^(h+N_R-1)` |
| `L` lowering | `(-1)^(2h+N_R+N_L-1) = (-1)^(N_R+N_L-1)` |

The simplified research convention has `F_R|N⟩=|N-e_R⟩` and
`F_L|N⟩=(-1)^N_R|N-e_L⟩`. It is not literally CH13's basis convention.
Define the diagonal unitary gauge

`U|N⟩ = u(N)|N⟩`,
`u(N)=(-1)^(h*N_R + binom(N_R,2) + binom(N_L,2))`,

where integer binomial coefficients use `n*(n-1)/2`, valid for all integer
charges. Then
`U F_R U†|N⟩ = (-1)^(h+N_R-1)|N-e_R⟩` and
`U F_L U†|N⟩ = (-1)^(N_R+N_L-1)|N-e_L⟩`.
This follows by taking the finite difference of the exponent of `u`; the
`2h` term in the second line is even. Hence conjugation by `U` is the explicit
adapter to the canonical CH13 charge shifts. Since `U` is diagonal, it
commutes with every charge phase; diagonal charge expectations are unchanged
by this rephasing. The oscillator tensor factor is untouched.

All products act right to left. Put `P_a(x)|N⟩=ζ^(a(N)x)|N⟩`, with
`a_D(N)=N_L-N_R-1` and `a_S(N)=N_R+N_L`. The scalar is therefore evaluated
on the source before the shift word:

| word | shift action on source `N` | target | Klein sign |
|---|---|---|---|
| `K_D(x)=F_R† F_L P_{a_D}(x)` | `F_L` then `F_R†` | `(N_R+1,N_L-1)` | `(-1)^N_R` |
| `K_S(x)=F_R F_L P_{a_S}(x)` | `F_L` then `F_R` | `(N_R-1,N_L-1)` | `(-1)^N_R` |

The shift inverses are adjoints on the finitely supported charge carrier.
Product reversal gives
`K_D(x)† = P_{-a_D}(x) F_L† F_R` and
`K_S(x)† = P_{-a_S}(x) F_L† F_R†`.
In `K_J(x)† K_J(y)`, the rightmost `K_J(y)` first shifts the source and
`K_J(x)†` restores it. Its adjoint phase is evaluated after the inverse shift,
at the original source `N`; the shift signs multiply to `1`. Thus

`⟨N|K_J(x)†K_J(y)|N⟩ = ζ^(a_J(N)*(y-x))`.

More generally, charge basis evaluation annihilates every shift word whose net
charge displacement is nonzero. Here the two-point word has zero net
displacement, so it survives. This is the charge-selection statement for this
functional; no charge expectation is replaced by a multiplicative rule.

The target labels obey `a_D(N+(1,-1))=a_D(N)-2` and
`a_S(N+(-1,-1))=a_S(N)-2`, but these shifted values are not the phase in the
two-point product. `L=4`, `ζ=i`, `x=0`, `y=1`, `N=(1,0)` is a useful sign
check: the charge factors are `-1` for D and `i` for S. At `N=(0,0)` they are
`-i` and `1`. In particular the current Section 20.2 positive SC exponent is
consistent with the ordered source-phase computation; no appendix sign edit is
proposed.

## Oscillator fields and conditional algebraic derivation

Use A08's actual map `beta = bogoliubovMap hp.c hp.s` for the dressed fields
`C̃=beta(C)`, `Ã=beta(A)`. A08 defines
`omegaP = omega0 ∘ bogoliubovMap(c,-s)`, the inverse pullback. Do not apply
`beta` to the dressed expressions a second time. Its contextual descent and
polynomial representation supply the represented CCR and adjoints. Set
`ε_R=1`, `ε_L=-1`,

`Q_ν(x)=Σ_(m=1..M) (ζ^(-ε_ν*m*x) C̃_(ν,m) + ζ^(ε_ν*m*x) Ã_(ν,m))/m`,
`X_D=(c-s)(Q_R+Q_L)`, `X_S=(c+s)(Q_R-Q_L)`,
`g_D=(c-s)^2`, `g_S=(c+s)^2`.

Each `X_J(x)` is Hermitian in the represented oscillator *-algebra. For one
chirality the represented commutator of the `x` and `y` fields is proportional
to `ζ^(ε*m*(x-y))-ζ^(-ε*m*(x-y))`; the `R` and `L` terms cancel because
`ε_L=-ε_R`. The channel sign in `X_S` squares to one. Therefore
`[X_J(x),X_J(y)]=0` in either same channel. This argument says nothing about a
mixed D/S commutator.

The creator and annihilator parts of `X_D` have represented contraction
`[A_D(x),C_D(y)] = 2g_D Σ_m ζ^(m*(x-y))/m`; for S the same expression has
`g_S`. Adding both orientations gives

`omegaP((X_J(y)-X_J(x))^2)=4*g_J*D1(x,y)`,
`D1(x,y)=Σ_(m=1..M) (1-cos(2πm(x-y)/L))/m`.

The commutator and variance are finite sums on the uncompressed polynomial
carrier and descend to the represented coefficient algebra. For `M=0` both
fields and `D1` vanish. At `x=y` the difference is zero. For `M>0`, the
`m=1` summand makes `D1≥0`; for even `L`, it vanishes exactly when `x=y` in
`ZMod L`.

Assuming an accepted S1 single-form moment theorem, put `Y=X_J(y)-X_J(x)`.
S1 must yield
`omegaP(Y^(2k+1))=0` and
`omegaP(Y^(2k))=(2k)!/(2^k k!)*(4g_J D1)^k`.
Termwise multiplication of formal exponentials is justified in the
represented coefficient algebra by the finite Cauchy product and
`[X_J(x),X_J(y)]=0`; it gives
`Exp_f(-itX_J(x))*Exp_f(itX_J(y))=Exp_f(itY)` coefficientwise. This identity
is not used for noncommuting fields or without the represented commutator
proof. The identity is not asserted in the unreduced free algebra.

## Candidate main theorem, conditional on S1

Define `W_J(t,x)=L^(-1) K_J(x) Exp_f(i*t*X_J(x))`. On the generated
charge/oscillator coefficient *-algebra and its coefficientwise series, the
target is

`ωhat_(P,N)(W_J(t,x)†*W_J(t,y))`
`= L^(-2) ζ^(a_J(N)*(y-x)) Exp_f(-2*g_J*D1(x,y)*t^2)`.

The derivation must be implemented in this order:

1. Adjoint reversal gives `Exp_f(-itX_J(x))*K_J(x)†`; commute only the charge
   and oscillator tensor factors, not arbitrary charge words.
2. Evaluate `K_J(x)†K_J(y)` on the source basis. Its inverse shift restores
   `N` before the adjoint diagonal phase acts, giving the positive exponent
   `a_J(N)(y-x)`.
3. Use the same-channel represented commutator to combine formal exponentials
   into `Exp_f(itY)` by a coefficientwise binomial proof.
4. Apply the accepted S1 moments, including `i^(2k)=(-1)^k` and the factorial
   denominator. The coefficient at degree `2k` is
   `(-2*g_J*D1)^k/k!`; odd coefficients vanish.
5. Include the two vertex normalizations: `L^(-1)*L^(-1)=L^(-2)`.

Checks: at `t^0` the coefficient is `L^(-2)ζ^(aΔx)`; at `t^1` it is zero;
at `t^2` it is `-2L^(-2)ζ^(aΔx)gD1`; at `t^4` it is
`2L^(-2)ζ^(aΔx)g²D1²`. At `x=y` the entire series is the constant `L^(-2)`.
The theorem is a formal coefficient identity; do not substitute `t=1` or claim
analytic convergence.

For a four-site check `L=4`, `M=1`, `x=0`, `y=1`, `D1=1`. At zero squeeze,
`c=±1,s=0` gives `g_D=g_S=1`; at source `N=(0,0)` the two correlators are
respectively `(-i/16) Exp_f(-2t²)` and `(1/16) Exp_f(-2t²)`. For nonzero
squeeze the four sign choices `c=±5/3`, `s=±4/3` all satisfy the hyperbolic
condition; `g_D,g_S` are `(1/9,9)` when `c,s` have equal signs and `(9,1/9)`
when they have opposite signs. These detect orientation, charge, and squeeze-
sign mistakes without asserting a physical finite-CAR identity.

An exact integer parity calculation of the gauge finite differences for
`h=1..4` and both charges in `[-4,4]` passes. Direct `L=4` phase evaluation
gives `N=(0,0) ↦ (-i,1)` and `N=(1,0) ↦ (-1,i)` for `(D,S)` at `y-x=1`.
For `D1=1`, the formal coefficient lists at degrees `0..4` are
`(1,0,-2g,0,2g²)`, including `g=1,1/9,9`. These are finite convention and
coefficient checks only; they do not validate a Lean declaration or replace
the S1 moment proof.

## Normal-ordering audit

The principal convention is Weyl type. Let `H_M=Σ_(m=1..M)1/m`. Split
`X_J=C_J+A_J` into dressed creator/annihilator parts. The represented CCR give
`[A_J,C_J]=2g_J H_M`. Central BCH (proved by finite formal coefficient
expansion in this generated algebra) gives

`Exp_f(itX_J)=Exp_f(itC_J) Exp_f(itA_J) Exp_f(-g_J H_M t²)`.

Thus the dressed-normal vertex
`W_J^d=L^(-1)K_J Exp_f(itC_J)Exp_f(itA_J)` satisfies
`W_J^d=Exp_f(g_J H_M t²) W_J`, and its two-point series is
`L^(-2)ζ^(aΔx) Exp_f(2g_J(H_M-D1)t²)`.

For bare oscillators, substitution of the actual `beta` gives
`Q_R=cQ_R^0+sQ_L^0`, `Q_L=cQ_L^0+sQ_R^0`, hence, using
`(c-s)(c+s)=1`, `X_D=Q_R^0+Q_L^0` and `X_S=Q_R^0-Q_L^0`.
The bare commutator is `[A_J^0,C_J^0]=2H_M`, independent of `g_J`. Therefore
`W_J^b=Exp_f(H_M t²)W_J` and its two-point series is
`L^(-2)ζ^(aΔx) Exp_f(2(H_M-g_J D1)t²)`.
The review's proposed per-vertex multipliers `Exp_f(g_J H_M t²)` (dressed)
and `Exp_f(H_M t²)` (bare) are consistent with these commutators; they are
different conventions and neither multiplier belongs in the principal Weyl
vertex theorem.

## Scope, proof plan, and unresolved gates

No finite CAR field is redefined or identified with `W_J`; CH14's conditional
field criterion remains conditional. No finite interacting ground state,
particle-hole map, analytic limit, continuum result, or S3 duality is included.

S1 is integrated and its general-moment declaration is available. Phase A adds
the minimal charge/vector, position/phase, represented oscillator-field,
coefficientwise series, adjoint, and formal correlator interface. The
independent mathematical/interface review passed for the exact source and
document hashes recorded above; the scoped lock was committed in
`0610d1495ebc4e95dec323c27faf22966e55e9d2`. Phase B's current proof inventory is recorded in
[`phase-b-checkpoint.md`](phase-b-checkpoint.md). The October 17 resumption
completed 18 further contracts, leaving eight unchanged placeholders; 31 S2
theorem declarations are proved in total. The exact partial package at source
SHA-256 `a639ded883ef762f34063a0a1425dc2cbdab4059d7be4026ce4d6e2c83e5dc03` passed
independent review. Fresh strict/Core guards pass; the staging build succeeds
with exactly eight placeholder warnings; the 31 completed theorem closures
use only the three permitted standard axioms. The main correlator, variance,
remaining field identities and normal-ordering theorems are still unproved.
The packet's mathematical interface and earlier Phase A review provenance
are retained; the resumption is not a full Phase B or Phase C verdict.
This packet does not start S3.
