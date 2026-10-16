import BosonizeStubs.Ch20CDW

namespace Bosonize.Ch20
open scoped BigOperators Classical

-- Reduction step for the concrete zero-target-cutoff residual witness.
example :
    Ch14.projectedMap 2 witnessZero (cdwTarget Ch16.standardBranches witnessZero)
        0 0 (cdwResidualOp 2 (fun _ => Ch06Ext.periodicTwist 4)
          Ch16.standardBranches 1 witnessZero 0)
        (Ch14.groundVector 2 (by decide) witnessZero witnessZero_admissible 0) = 0 := by
  apply Subtype.ext
  rw [Ch14.projected_map_apply]
  -- Remaining goal is the occupation-coordinate projection of the residual.
  sorry

end Bosonize.Ch20
