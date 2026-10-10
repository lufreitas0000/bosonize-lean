# Ch06Ext Phase B: reviewed length-assumption cleanup proposal

Status: **approved and applied by the user’s instruction to proceed to Phase C**. Approved baseline: `b92dd3b`. All 72 theorem bodies compile without placeholders. Frozen definitions, namespaces, imports and mathematical conclusions are unchanged. The current source retains its approved length assumptions; the compiler reports eight unused-section-variable warnings. Four further unnecessary dependencies become visible when those primitive assumptions are removed.

## Exact requested change

Add `omit [NeZero L] in` before the documented declaration of each of the following 12 lemmas. The resulting declarations retain `(L : ℕ)` and every explicit parameter/hypothesis/conclusion, but have no automatically included `[NeZero L]` argument. Keep every other theorem's positive-length contract.

- `Bosonize.Ch06Ext.twist_step_ne_zero`
- `Bosonize.Ch06Ext.holonomy_norm`
- `Bosonize.Ch06Ext.lift_phase_norm`
- `Bosonize.Ch06Ext.lift_phase_add`
- `Bosonize.Ch06Ext.lift_phase_winding`
- `Bosonize.Ch06Ext.periodic_holonomy`
- `Bosonize.Ch06Ext.angle_root_shift`
- `Bosonize.Ch06Ext.translation_ket`
- `Bosonize.Ch06Ext.translation_zero`
- `Bosonize.Ch06Ext.transport_apply`
- `Bosonize.Ch06Ext.trivialization_ratio_periodic`
- `Bosonize.Ch06Ext.zero_mode_ket`

For example, the elaborated type of `twist_step_ne_zero` changes from

```lean
(L : ℕ) → [NeZero L] → (b : BoundaryTwist L) → b.step ≠ 0
```

to

```lean
(L : ℕ) → (b : BoundaryTwist L) → b.step ≠ 0
```

The Lean source form is:

```lean
omit [NeZero L] in
/-- Existing declaration documentation. -/
lemma twist_step_ne_zero (b : BoundaryTwist L) : b.step ≠ 0 := by
  -- Preserve the completed proof body.
```

These are scalar/basis identities that do not need a nonempty ring. In particular, norm-one step implies nonzero step even at L=0; integer-power algebra is independent of ring length; basis extension and zero-displacement translation remain valid on the empty-mode Fock carrier. The root-shift exponential identity also holds at L=0 under Lean's division convention. Removing these arguments does not assign a physical ring interpretation to L=0. Angular holonomy/coverage, winding decomposition, actual spatial fields and the remaining transport contracts retain their required positive-length assumptions.

Only the Ch06Ext v2 entry would be refreshed after approval, including its scoped-command context hashes. Preserve all other entries and the unrelated working-tree manifest additions. No frozen Core source is changed.

## Verification before approval

A full temporary copy with exactly these 12 omissions and the completed 72 proofs compiled with `lake env lean -DwarningAsError=true /tmp/ch06ext-cleanup-proposal.lean`, exit 0. The final tested copy emits no diagnostics. The original locked source and proof bodies remain reviewable in Ch06Ext. The original strict working-tree guard and eight Core hashes pass; the committed baseline has only Ch06Ext newly locked, while A03/CH07 lock additions remain separate local work.

The repository [formalizer skill](../.agents/skills/formalizer/SKILL.md) requires: “New top-level declarations/files or changes to a frozen interface require explicit review and baseline approval.” That requirement applies to removing the implicit length hypothesis, even though the compiler confirms it is unnecessary. Approval authorizes these 12 omissions and only the affected Ch06Ext lock entry, followed by repeated validation.

## Approved cleanup checkpoint

Applied exactly the twelve scoped omissions above, preserving every proof body and explicit theorem header. Fresh warning-as-error compilation emitted no diagnostics. The working-tree strict interface guard verified 457 statements/342 commands; all eight existing Core hashes passed. Only the Ch06Ext manifest entry is committed here; local A03/CH07 additions remain preserved separately.
