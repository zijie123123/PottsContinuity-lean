module

public import PottsContinuity.Thm4Records.OuterClusterReveals
public import PottsContinuity.Thm4Plane.ScreenActiveConnectorDualConfig

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Exploration Push RSW Thm4Plane
noncomputable section
local instance exteriorSourceEdgeEq (m : ℕ) :
    DecidableEq (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet := Classical.decEq _

/-- Original primal bonds crossed by the dual bonds of R*. -/
def rStarSourceEdges (m : ℕ) (hm : 1 ≤ m) :
    Configuration (FKC.FiniteFK.slitBoxGraph (16*m)) := by
  classical
  exact Finset.univ.image (fun e => (slitRStarEdgeBridge m hm e).primalEdge)

/-- Every source bond outside R* is frozen before the residual law is taken. -/
def exteriorRevealEdges (m : ℕ) (hm : 1 ≤ m) :
    Configuration (FKC.FiniteFK.slitBoxGraph (16*m)) := by
  classical
  exact Finset.univ \ rStarSourceEdges m hm

/-- Concrete common reveal, including the fixed exterior of R*. -/
def connectorReveal (m : ℕ) (hm : 1 ≤ m) :
    RevealMap (G := FKC.FiniteFK.slitBoxGraph (16*m)) :=
  jointReveal (connectorClusterReveal m) (fun _ => exteriorRevealEdges m hm)

theorem connectorReveal_stable (m : ℕ) (hm : 1 ≤ m) :
    ∀ A B, B ∩ connectorReveal m hm A = A ∩ connectorReveal m hm A →
      connectorReveal m hm B = connectorReveal m hm A :=
  jointReveal_stable (connectorClusterReveal m) (fun _ => exteriorRevealEdges m hm)
    (connectorClusterReveal_stable m) (by intro A B _; rfl)

theorem screenEvent_readFrom_connectorReveal (m : ℕ) (hm : 1 ≤ m) :
    ReadFromReveal (connectorReveal m hm) (slitScreenEvent m) :=
  readFromReveal_joint_left _ _ (connectorClusterReveal_stable m)
    (by intro A B _; rfl) _ (screenEvent_readFrom_connectorClusterReveal m)

/-- No original source bond outside R* remains random on the record. -/
theorem remaining_edge_mem_rStarSourceEdges (m : ℕ) (hm : 1 ≤ m)
    (A : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (e : (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet)
    (he : e ∉ connectorReveal m hm A) : e ∈ rStarSourceEdges m hm := by
  classical
  by_contra h
  apply he
  apply Finset.mem_union_right
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,h⟩

end
end PottsContinuity.Thm4Records
