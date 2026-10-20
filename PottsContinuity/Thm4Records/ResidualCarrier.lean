module

public import PottsContinuity.Thm4Records.ExteriorFreeze
public import PottsContinuity.PD.FK.EdgeRestriction

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Exploration Push RSW Thm4Plane
noncomputable section
local instance residualSourceEdgeEq (m : ℕ) :
    DecidableEq (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet := Classical.decEq _
local instance residualDualEdgeEq (m : ℕ) :
    DecidableEq (SlitRStarGraph m).edgeSet := Classical.decEq _
local instance residualDualEdgeFintype (m : ℕ) :
    Fintype (SlitRStarGraph m).edgeSet := Fintype.ofFinite _

/-- R* bonds whose crossed source bonds have already been queried. -/
def recordedDualEdges (m : ℕ) (hm : 1 ≤ m)
    (R : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    Configuration (SlitRStarGraph m) :=
  Finset.univ.filter fun e => (slitRStarEdgeBridge m hm e).primalEdge ∈ R

@[simp] theorem mem_recordedDualEdges (m : ℕ) (hm : 1 ≤ m)
    (R : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (e : (SlitRStarGraph m).edgeSet) :
    e ∈ recordedDualEdges m hm R ↔ (slitRStarEdgeBridge m hm e).primalEdge ∈ R := by
  simp [recordedDualEdges]

end
end PottsContinuity.Thm4Records
