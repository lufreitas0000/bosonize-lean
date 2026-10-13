## Source map

- `docs/webllm/ch15_core_api.md` (exported Core signatures): `A01.integerCharacter`, `A01.complex_character_conj`, `A01.character_sum`, `A01.canonicalRoot`, `A05.Operators`, `A05.rho`, `A05.rho_adjoint`, `A05.rho_cross_commute`, `A05.rho_tensor`, `A05.rho_budget_map`, `A05.jointBudget`, `A05.admissible`, `A05.groundKet`, `A05.ground_mem_budget`, `A05.ground_ne_zero`, `Ch10.rho_signed_ccr` and `Ch10.schwingerCoefficient`. The proposed joint-species CCR is **not** a cited existing Core theorem; it requires transport from the one-species theorem.
- `notes/md/ch15_dual_fields.md`, §§15.1–15.3: separate two orientations and species, the chiral expansion, dual combinations, character-valued commutators, forward difference, and zero-mode obstruction. These are conjectural interfaces until reviewed.
- `notes/appendices/a06_chiral_fields_and_lattice_kernels.md`, sections *Separate species from chirality*, *Exact gradient and zero-mode obstruction*, and *Kernel identities and corner cases*: adopt orientation reversal of the spatial character, not a change to the current commutator; use exact finite sums and additive periodic differences. Exclude its later normal-ordering, Hamiltonian, dispersion, RG, and excited-state proposals (CH16 territory).
- `note/ch14_phase_c_validation_2026-10-13.md`: CH14 Core is reported as verified for a **conditional** cyclic/common-residual comparison, not an unconditional physical fermion/vertex identity. No CH14 identification is imported into CH15's claims.
- `scripts/webllm/verify_phase_a.py`, `lean-toolchain`, `lakefile.toml`: the local runner requires one Lean fence, explicit audited data declarations and exactly one `:= by sorry` per theorem/lemma; Lean version is `v4.35.0-rc4`. This is an uncompiled proposal, not runner output.

## Design and scope

All operators act on the **ambient finite** `A05.FockSpace σ h`; their carrier is `A05.Operators σ h = Module.End ℂ (A05.FockSpace σ h)`. Sites are `ZMod (2*h)`, not integers. An explicit pair of distinct existing species is held in `A06.Branches σ`. Orientation is a separate two-valued type: `right ↦ +1`, `left ↦ -1`. Both species use the **same** `A05.rho` convention. In particular, positive `rho(m)` raises the excitation budget and negative `rho(-m)` lowers it. `Ch10.schwingerCoefficient m n = if m+n=0 then -(m:ℂ) else 0`, so `[rho(-m),rho(m)] v = m • v` for positive `m` on a suitable input.

Take `h>0`, `1≤M` independent of `h`, and `2*M<2*h`. For the two-current action on an actual joint-budget vector `v ∈ A05.jointBudget h Ns K`, require, separately for each used branch `ν`, the **sufficient** margin `2*M + K + |Ns ν| ≤ h` (integers, with the natural quantities cast into `ℤ`). This is stronger than no aliasing; it does not introduce any global CCR or fictitious margin on unused species. The commutator action has source `v` in budget `K`, while its expanded products may traverse budgets as high as `K+2*M` before cancellation. Neither field is claimed to preserve the input budget; consequently, fields remain ambient endomorphisms rather than endomorphisms of `jointBudget`.

For an arbitrary primitive complex `2*h`-th root `ζ`, set `χ_k(x)=ζ^(k*x)` on residues, and define `S_M(x,y)=∑_{m=1}^M (χ_m(x-y)-χ_{-m}(x-y))/m`. With `ϕ_η(x)=i∑_{m=1}^M (χ_{ηm}(x)ρ_{-m,ν(η)}-χ_{-ηm}(x)ρ_{m,ν(η)})/m`, the **candidate, normalization-checked** consequence of the signed Core CCR is

`[ϕ_η(x),ϕ_η(y)]v = η S_M(x,y) • v`; cross-species commutators vanish globally; hence `[φ(x),φ(y)]v=[θ(x),θ(y)]v=0` and `[φ(x),θ(y)]v=2 S_M(x,y) • v` for `φ=ϕ_right+ϕ_left`, `θ=ϕ_right-ϕ_left`. Here multiplication by complex scalars means scalar action on `v`; the commutator is ordered as `AB-BA`. The sign is fixed by the **minus** in `Ch10.schwingerCoefficient`, not by postulating a second CCR with opposite central charge. For the canonical exponential root only, `S_M=2i∑ sin(2πm(x-y)/(2h))/m`; no such sine statement is inferred for arbitrary `ζ`.

`Δf(x)=f(x+1)-f(x)` is defined for additively structured codomains and is periodic by construction. The exact differentiated character factor is `(ζ^(±ηm)-1)/m`, not a mode-independent density multiplier. `δ_M(x,y)=(2h)⁻¹∑_{m=-M}^M χ_m(x-y)` has spatial sum `1` under the stated root/no-alias hypotheses, whereas every periodic forward difference has spatial sum `0`. Accordingly, no nonzero scalar times the **unsubtracted** `δ_M` can equal the commutator with `Δθ` even on a nonzero admissible ground input. No inverse-gradient, continuum, thermodynamic, Hamiltonian, or vertex conclusion is claimed.

## Lean draft

```lean
import Bosonize

namespace Bosonize.A06

open scoped BigOperators

inductive Orientation where
  | right
  | left
  deriving DecidableEq

def orientationSign : Orientation → ℤ
  | .right => 1
  | .left => -1

structure Branches (σ : Type*) where
  rightSpecies : σ
  leftSpecies : σ
  distinct : rightSpecies ≠ leftSpecies

def speciesOf {σ : Type*} (branches : Branches σ) : Orientation → σ
  | .right => branches.rightSpecies
  | .left => branches.leftSpecies

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

def marginAt (h M K : ℕ) (Ns : σ → ℤ) (ν : σ) : Prop :=
  2 * (M : ℤ) + (K : ℤ) + |Ns ν| ≤ (h : ℤ)

def branchMargins (h M K : ℕ) (Ns : σ → ℤ)
    (branches : Branches σ) : Prop :=
  marginAt h M K Ns branches.rightSpecies ∧
    marginAt h M K Ns branches.leftSpecies

noncomputable def latticeCharacter (h : ℕ) (ζ : ℂ) (k : ℤ)
    (x : ZMod (2 * h)) : ℂ :=
  A01.integerCharacter ζ k (x.val : ℤ)

noncomputable def skewKernel (h M : ℕ) (ζ : ℂ)
    (x y : ZMod (2 * h)) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M,
    (latticeCharacter h ζ (m : ℤ) (x - y) -
      latticeCharacter h ζ (-(m : ℤ)) (x - y)) / (m : ℂ)

noncomputable def dirichletKernel (h M : ℕ) (ζ : ℂ)
    (x y : ZMod (2 * h)) : ℂ :=
  ((2 * h : ℕ) : ℂ)⁻¹ *
    ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      latticeCharacter h ζ m (x - y)

def opForwardDiff (h : ℕ) {V : Type*} [AddGroup V]
    (f : ZMod (2 * h) → V) : ZMod (2 * h) → V :=
  fun x => f (x + 1) - f x

def integerLift (h : ℕ) {V : Type*}
    (f : ZMod (2 * h) → V) (x : ℤ) : V :=
  f (x : ZMod (2 * h))

noncomputable def chiralField (h M : ℕ) (ζ : ℂ)
    (branches : Branches σ) (η : Orientation)
    (x : ZMod (2 * h)) : A05.Operators σ h :=
  ∑ m ∈ Finset.Icc 1 M,
    (Complex.I / (m : ℂ)) •
      ((latticeCharacter h ζ (orientationSign η * (m : ℤ)) x •
          A05.rho h (speciesOf branches η) (-(m : ℤ))) -
        (latticeCharacter h ζ (-(orientationSign η * (m : ℤ))) x •
          A05.rho h (speciesOf branches η) (m : ℤ)))

noncomputable def chiralDifferenceExpansion (h M : ℕ) (ζ : ℂ)
    (branches : Branches σ) (η : Orientation)
    (x : ZMod (2 * h)) : A05.Operators σ h :=
  ∑ m ∈ Finset.Icc 1 M,
    (Complex.I / (m : ℂ)) •
      (((A01.integerCharacter ζ (orientationSign η * (m : ℤ)) 1 - 1) *
          latticeCharacter h ζ (orientationSign η * (m : ℤ)) x) •
          A05.rho h (speciesOf branches η) (-(m : ℤ)) -
        ((A01.integerCharacter ζ (-(orientationSign η * (m : ℤ))) 1 - 1) *
          latticeCharacter h ζ (-(orientationSign η * (m : ℤ))) x) •
          A05.rho h (speciesOf branches η) (m : ℤ))

lemma lattice_character_shift (h : ℕ) [NeZero (2 * h)] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 * h)) (k : ℤ) (x : ZMod (2 * h)) :
    latticeCharacter h ζ k (x + 1) =
      A01.integerCharacter ζ k 1 * latticeCharacter h ζ k x := by sorry

lemma lattice_character_conj (h : ℕ) [NeZero (2 * h)] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 * h)) (k : ℤ) (x : ZMod (2 * h)) :
    star (latticeCharacter h ζ k x) = latticeCharacter h ζ (-k) x := by sorry

lemma integer_lift_periodic (h : ℕ) {V : Type*}
    (f : ZMod (2 * h) → V) (x : ℤ) :
    integerLift h f (x + (2 * h : ℕ)) = integerLift h f x := by sorry

lemma forward_diff_add (h : ℕ) {V : Type*} [AddCommGroup V]
    (f g : ZMod (2 * h) → V) (x : ZMod (2 * h)) :
    opForwardDiff h (fun y => f y + g y) x =
      opForwardDiff h f x + opForwardDiff h g x := by sorry

lemma forward_diff_smul (h : ℕ) {V : Type*} [AddCommGroup V]
    [Module ℂ V] (a : ℂ) (f : ZMod (2 * h) → V)
    (x : ZMod (2 * h)) :
    opForwardDiff h (fun y => a • f y) x =
      a • opForwardDiff h f x := by sorry

lemma forward_diff_sum_zero (h : ℕ) [NeZero (2 * h)]
    {V : Type*} [AddCommGroup V] (f : ZMod (2 * h) → V) :
    (∑ x : ZMod (2 * h), opForwardDiff h f x) = 0 := by sorry

lemma chiral_adjoint (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : Branches σ)
    (η : Orientation) (x : ZMod (2 * h)) :
    LinearMap.adjoint (chiralField h M ζ branches η x) =
      chiralField h M ζ branches η x := by sorry

lemma chiral_forward_diff (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : Branches σ)
    (η : Orientation) (x : ZMod (2 * h)) :
    opForwardDiff h (chiralField h M ζ branches η) x =
      chiralDifferenceExpansion h M ζ branches η x := by sorry

lemma joint_signed_current_commutator (h K : ℕ) (hh : 0 < h)
    (Ns : σ → ℤ) (ν : σ) (m n : ℤ)
    (hmargin : |m| + |n| + (K : ℤ) + |Ns ν| ≤ (h : ℤ))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (A05.rho h ν m) (A05.rho h ν n) v =
      Ch10.schwingerCoefficient m n • v := by sorry

lemma chiral_cross_commute (h M : ℕ) (ζ : ℂ)
    (branches : Branches σ) (x y : ZMod (2 * h)) :
    A02.commutator
      (chiralField h M ζ branches .right x)
      (chiralField h M ζ branches .left y) = 0 := by sorry

lemma chiral_same_commutator_on_budget (h M K : ℕ) (hh : 0 < h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : Branches σ) (η : Orientation)
    (Ns : σ → ℤ)
    (hmargin : marginAt h M K Ns (speciesOf branches η))
    (x y : ZMod (2 * h))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator
      (chiralField h M ζ branches η x)
      (chiralField h M ζ branches η y) v =
      ((orientationSign η : ℂ) * skewKernel h M ζ x y) • v := by sorry

lemma dirichlet_diagonal (h M : ℕ) (hh : 0 < h) (ζ : ℂ) :
    dirichletKernel h M ζ (0 : ZMod (2 * h)) 0 =
      ((2 * M + 1 : ℕ) : ℂ) / ((2 * h : ℕ) : ℂ) := by sorry

lemma dirichlet_spatial_sum (h M : ℕ) [NeZero (2 * h)]
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (hNoAlias : 2 * M < 2 * h) (x : ZMod (2 * h)) :
    (∑ y : ZMod (2 * h), dirichletKernel h M ζ x y) = 1 := by sorry

lemma skew_kernel_diff_sum_zero (h M : ℕ) [NeZero (2 * h)]
    (ζ : ℂ) (x : ZMod (2 * h)) :
    (∑ y : ZMod (2 * h),
      opForwardDiff h (skewKernel h M ζ x) y) = 0 := by sorry

lemma admissible_ground_nonzero (h K : ℕ) (hh : 0 < h)
    (Ns : σ → ℤ) (hN : A05.admissible h Ns) :
    ∃ v : A05.FockSpace σ h,
      v ∈ A05.jointBudget h Ns K ∧ v ≠ 0 := by sorry

lemma concrete_two_branch_parameters :
    ∃ (h M K : ℕ) (Ns : Fin 2 → ℤ) (branches : Branches (Fin 2)),
      0 < h ∧ 1 ≤ M ∧ 2 * M < 2 * h ∧
      A05.admissible h Ns ∧ branchMargins h M K Ns branches ∧
      A05.groundKet h Ns ∈ A05.jointBudget h Ns K ∧
      A05.groundKet h Ns ≠ 0 := by sorry

end Bosonize.A06

namespace Bosonize.Ch15

open scoped BigOperators

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

noncomputable def phiField (h M : ℕ) (ζ : ℂ)
    (branches : A06.Branches σ) (x : ZMod (2 * h)) : A05.Operators σ h :=
  A06.chiralField h M ζ branches .right x +
    A06.chiralField h M ζ branches .left x

noncomputable def thetaField (h M : ℕ) (ζ : ℂ)
    (branches : A06.Branches σ) (x : ZMod (2 * h)) : A05.Operators σ h :=
  A06.chiralField h M ζ branches .right x -
    A06.chiralField h M ζ branches .left x

lemma phi_adjoint (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ)
    (x : ZMod (2 * h)) :
    LinearMap.adjoint (phiField h M ζ branches x) =
      phiField h M ζ branches x := by sorry

lemma theta_adjoint (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ)
    (x : ZMod (2 * h)) :
    LinearMap.adjoint (thetaField h M ζ branches x) =
      thetaField h M ζ branches x := by sorry

lemma phi_self_commutator_on_budget (h M K : ℕ) (hh : 0 < h)
    (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : A06.branchMargins h M K Ns branches)
    (x y : ZMod (2 * h))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (phiField h M ζ branches x)
      (phiField h M ζ branches y) v = 0 := by sorry

lemma theta_self_commutator_on_budget (h M K : ℕ) (hh : 0 < h)
    (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : A06.branchMargins h M K Ns branches)
    (x y : ZMod (2 * h))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (thetaField h M ζ branches x)
      (thetaField h M ζ branches y) v = 0 := by sorry

lemma mixed_commutator_on_budget (h M K : ℕ) (hh : 0 < h)
    (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : A06.branchMargins h M K Ns branches)
    (x y : ZMod (2 * h))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (phiField h M ζ branches x)
      (thetaField h M ζ branches y) v =
      (2 * A06.skewKernel h M ζ x y) • v := by sorry

lemma mixed_forward_diff_on_budget (h M K : ℕ) (hh : 0 < h)
    (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : A06.branchMargins h M K Ns branches)
    (x y : ZMod (2 * h))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (phiField h M ζ branches x)
      (A06.opForwardDiff h (thetaField h M ζ branches) y) v =
      (2 * A06.opForwardDiff h (A06.skewKernel h M ζ x) y) • v := by sorry

theorem zero_mode_obstruction_on_ground (h M K : ℕ)
    [NeZero (2 * h)] (hh : 0 < h)
    (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hmargin : A06.branchMargins h M K Ns branches)
    (x : ZMod (2 * h)) (c : ℂ) (hc : c ≠ 0) :
    ¬ (∀ y : ZMod (2 * h),
      A02.commutator (phiField h M ζ branches x)
        (A06.opForwardDiff h (thetaField h M ζ branches) y)
          (A05.groundKet h Ns) =
        (c * A06.dirichletKernel h M ζ x y) • A05.groundKet h Ns) := by sorry

end Bosonize.Ch15
```

## Companion notebook

**Carriers and imports.** `import Bosonize` is the only import. `σ` has precisely the `Fintype` and `LinearOrder` instances required by multispecies A05; no new representation of currents, CAR, charge, or Fock states is postulated. `Branches σ` supplies concrete indices and a proof of inequality. The field and its exact difference expansion are ambient `Module.End ℂ (A05.FockSpace σ h)` values. `LinearMap.adjoint`, rather than an assumed `StarRing` operation on a hypothetical operator algebra, is the actual Core adjoint API. `ζ` is a complex scalar input; results requiring conjugation or Fourier orthogonality assume `IsPrimitiveRoot ζ (2*h)`. The actual phase dictionary is not identified with `Ch14.wPlus/wMinus`, which are compressed, integer-coordinate, species-specific constructions.

**Operator order, budgets and normalizations.** The rightmost current in `ρ_-m`/`ρ_m` expressions acts first. A product of two terms can raise an input from global cutoff `K` to `K+2M`, so the contracted central term uses the sufficient per-species condition `2M+K+|Ns ν|≤h`. In the same-species transport lemma, this is sharpened to `|m|+|n|+K+|Ns ν|≤h`, mirroring `Ch10.rho_signed_ccr`. The Core statement is originally on `Ch07.fixedBudget`, not on joint vectors, hence the joint lemma is a genuinely new obligation: use `A05.rho_tensor`, finite occupation/tensor decomposition and the actual definition of `Ch07.speciesBudget`. `A05.rho_cross_commute` proves the cross terms globally without a margin; `A05.rho_adjoint` and `A01.complex_character_conj` handle Hermiticity globally. No composition is compressed or silently projected onto the input budget.

For positive `m`, the `ρ_-m,ρ_m` term contributes `+m` while `ρ_m,ρ_-m` contributes `-m`. The two minus signs (from the expansion and `i²=-1`) yield exactly `(χ_{ηm}(x-y)-χ_{-ηm}(x-y))/m` for the same branch; there is **no** extra factor of `i`, `2` or `1/(2h)` in `S_M`. Summing the two opposite branches gives `2 S_M` in the mixed commutator, with a **zero** sum in each self-commutator. The `1/(2h)` occurs only in `δ_M`. The source's `2i C(x,y)` is consistent only when `ζ` is the canonical exponential root and `C=∑_{m=1}^M (2/m)sin(2πm(x-y)/(2h))`; it is not an arbitrary-root characterization.

**Periodicity and source/target signatures.** `latticeCharacter` uses residue representatives; root primitivity makes the representative-independent Fourier laws available. `integerLift` requires a proved period-`2h` lemma and is not the definition domain of fields. `opForwardDiff` needs only additive subtraction; its summation theorem additionally needs `[NeZero (2*h)]` for a finite spatial sum. It uses no commutative multiplication on endomorphisms. Its exact field formula multiplies each nonzero retained current by `ζ^(±ηm)-1`; no purported exact proportionality to a uniformly normalized charge density is present. The `dirichletKernel` diagonal is `(2M+1)/(2h)`; its spatial average is `1` when the only retained multiple of `2h` is `0`. The no-alias bound supplies this restriction and separates nonzero positive/negative modes.

**Non-vacuity.** A05 already supplies `ground_mem_budget` and `ground_ne_zero` under admissibility; the proposed `admissible_ground_nonzero` restates the existence in the actual joint carrier. `concrete_two_branch_parameters` asks for a genuine constructive example over the existing `Fin 2` species: candidate parameters are `h=4`, `M=1`, `K=0`, zero charges and the two distinct `Fin 2` indices, with `2≤4`, `2<8`; admissibility and the remaining predicates must be checked in Lean. The obstruction theorem applies to this nonzero ground witness, not merely to a possibly zero budget space. The zero-mode contradiction only rules out nonzero multiples of **unsubtracted** `δ_M`; a zero-average kernel or spectral derivative is not ruled out.

**Adopted/adapted/rejected.** Adopt the A06 orientation reversal, exact finite character sums, separate cutoff, bounded current actions, and exact periodic differences. Adapt the original abstract Hilbert-space and informal `star` proposals to `A05.Operators`, `LinearMap.adjoint`, actual species and `ZMod (2*h)`. Reject identical-chirality cancellation, an opposite-sign CCR for unmodified identical currents, a global scalar current commutator, arbitrary-root sine formulas, commutative `Ch02.forwardDiff` on endomorphisms, and the exact unmodified delta-gradient identity. The cited CH14 Phase C status is restricted to its conditional theorem; CH16 square/Hamiltonian/error statements are excluded entirely.

## Review obligations

1. **Elaboration (not performed here).** Run the packet's `scripts/webllm/verify_phase_a.py` locally on the candidate, under the pinned Lean toolchain; check namespace lookup, complex integer casts, `ZMod` coercions, `LinearMap.adjoint` inferred Hilbert structures, endomorphism scalar multiplication, `Finset.Icc` indexing, finite `ZMod` enumeration and `autoImplicit=false`. Confirm data-axiom audit and the exact one-sorry stub format. No successful build, test or axiom audit is asserted here.
2. **Current transport.** Prove `joint_signed_current_commutator` on all elements of the **actual** `jointBudget`, not just pure product kets; provide the finite spanning/decomposition bridge from the single-species `Ch10.rho_signed_ccr`. Show explicitly that the species and charge preserved by each current match the margin actually stated, and that zero vectors do not hide a failed theorem.
3. **Algebraic audit.** Independently expand both mixed current orderings with `schwingerCoefficient` (coefficient `-m` for `[ρ_m,ρ_-m]`) and verify the `i²` sign, `1/m` weight, opposite spatial orientations, field normalization and the direction `x-y`. Demonstrate the two self-commutators vanish **on the same input** with both branch margins. Give explicit small-sector calculations or an independent algebraic check, not a global CCR assumption.
4. **True adjoints.** Check `A05.rho_adjoint`, `A01.complex_character_conj` and the conjugation of `i/m` in the full ambient endomorphism, including negative orientation. Avoid translating Hilbert adjoints to `star` without an existing compatible instance.
5. **Finite witnesses and bounds.** Prove a concrete `Fin 2` pair, admissibility at `Ns=0`, actual membership/nonzeroness of `A05.groundKet`, and all margins for `h=4,M=1,K=0`; if any candidate fails, replace it with a proved explicit choice rather than retain a vacuous existential. Confirm `2M<2h` as sufficient for Fourier nonaliasing and note that the CCR margins are stronger.
6. **Character and delta sums.** Check representative independence, spatial translation `x+1`, roots of unity for negative integers, diagonal cardinality `2M+1`, finite orthogonality and `∑_y δ_M(x,y)=1` for **arbitrary** primitive `ζ`. The sine formula is a separate possible canonical-root theorem, not part of the present claims.
7. **Zero-mode contradiction.** Establish `∑_y Δθ(y)=0` in the ambient additive operator group; commute the finite sum past the commutator action in the stated order, and use `∑_y δ_M(x,y)=1`, `c≠0` and the proved nonzero ground ket. Explain why the result does not prohibit a zero-mode-subtracted target kernel. Check exact difference multipliers rather than replacing them by derivatives.
8. **Boundary of scope.** Review whether the choice of spatial orientation really represents the desired physics without modifying the already fixed current/sea convention. No unconditional CH14 physical-field/vertex identification, CH16 normal-ordering/Hamiltonian construction, infinite-volume limit, Fourier sawtooth, or RG estimate can follow from these declarations alone. Subsequent independent mathematical review and local Core-compatible elaboration must precede staging and locking.
