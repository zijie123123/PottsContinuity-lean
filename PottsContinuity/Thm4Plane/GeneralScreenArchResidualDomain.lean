module

public import PottsContinuity.Thm4Plane.ScreenArchPath
public import PottsContinuity.PlanarTopology.SlitArchSampledGeometry
public import PottsContinuity.PlanarTopology.BottomArchSeparation
public import PottsContinuity.PlanarTopology.RectangleDualGraphBridge
public import PottsContinuity.FKC.FiniteFK.RectangleConnectivity
public import PottsContinuity.FKC.FiniteFK.EdgeRestriction

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity.FKC.FiniteFK
open PottsContinuity.FKC.Medial

noncomputable section

local instance generalScreenArchResidualDomainEdgeFintype (n : ℕ) :
    Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _

local instance generalScreenArchResidualDomainEdgeDecidableEq (n : ℕ) :
    DecidableEq (slitBoxGraph n).edgeSet := Classical.decEq _

/-- The induced domain left after deleting bonds crossed by an arch. -/
def generalScreenArchCapDomainGraph (n : ℕ)
    (R : Configuration (slitBoxGraph n))
    (D : Set (SlitBoxVertex n)) : SimpleGraph {v : SlitBoxVertex n // v ∈ D} :=
  (edgeRestriction (slitBoxGraph n) R).induce D

end
end PottsContinuity.Thm4Plane
