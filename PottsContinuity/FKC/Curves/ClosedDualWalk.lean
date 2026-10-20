-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/ClosedDualWalk.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.PrimalDualSegments
public import PottsContinuity.FKC.Medial.WholePlaneClusterContainment

@[expose] public section

namespace PottsContinuity.FKC.Medial

noncomputable section

/-- Interpolate each actual closed-dual edge by its straight embedded face-center
segment, retaining walk order and repeated visits. -/
def closedDualWalkPath (δ : PositiveMesh) (ω : LatticeConfiguration) :
    {u v : LatticeVertex} → (wholePlaneClosedDualGraph ω).Walk u v →
      Path (dualFaceCenter δ u) (dualFaceCenter δ v)
  | _, _, .nil => Path.refl _
  | u, _, .cons (v := v) _h p =>
      (Path.segment (dualFaceCenter δ u)
        (dualFaceCenter δ v)).trans (closedDualWalkPath δ ω p)

end
end PottsContinuity.FKC.Medial
