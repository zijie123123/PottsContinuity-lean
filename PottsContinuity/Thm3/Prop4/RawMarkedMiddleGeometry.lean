module

public import PottsContinuity.Thm3.Prop4.RawMarkedTraceAccess
public import PottsContinuity.Thm3.Prop4.RawComponentBoundaryPartition
public import PottsContinuity.PlanarMixed.CrosscutOpenWalks

/-! # Actual raw trace attachments to the access-defined middle -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite Push Exploration
noncomputable section
local instance rawMarkedMiddleGeometryEdgeEq (n : ℕ) :
    DecidableEq (finiteLatticeGraph (box n)).edgeSet := Classical.decEq _

/-- The access-defined middle is used only as a retained vertex carrier. -/
def rawMarkedMiddleVertices (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A : Configuration (finiteLatticeGraph (box n))) : Set (box n : Set LatticeVertex) :=
  sourceMiddleDomain n ((markedLowerBoxTrace n u v A).image Subtype.val)
    ((markedUpperBoxTrace n u v A).image Subtype.val)

end
end PottsContinuity.Thm3.Prop4
