module

public import PottsContinuity.Thm3.Prop4.RawMarkedMiddleGeometry
public import PottsContinuity.Thm3.Prop4.ComponentPocketMarginal

/-! # Exact wired middle marginal under the actual raw induced law -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite Push Exploration PlanarMixed.Square
noncomputable section
local instance rawMarkedMiddleLawEdgeEq (n : ℕ) :
    DecidableEq (finiteLatticeGraph (box n)).edgeSet := Classical.decEq _

/-- Delete only the actual raw joint queries from the original box graph. -/
def rawMarkedRemainingGraph (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A : Configuration (finiteLatticeGraph (box n))) : SimpleGraph (box n : Set LatticeVertex) :=
  edgeRestriction (finiteLatticeGraph (box n)) (markedJointBoxRawReveal n u v A)

/-- Retain only the fresh middle edges; all other fresh edges are integrated,
without changing the original raw record or queried states. -/
def rawMarkedMiddleGraph (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A : Configuration (finiteLatticeGraph (box n))) : SimpleGraph (rawMarkedMiddleVertices n u v A) :=
  (rawMarkedRemainingGraph n u v A).induce (rawMarkedMiddleVertices n u v A)

end
end PottsContinuity.Thm3.Prop4
