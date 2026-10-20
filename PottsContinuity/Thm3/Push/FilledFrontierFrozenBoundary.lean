module

public import PottsContinuity.Thm3.Push.FilledFrontierSideConnection
public import PottsContinuity.Thm3.Push.FilledFrontierDMP
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance frontierBoundaryEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Physical wired sides together with all vertices incident to the actual
filled frontier. The bottom interior is not added to this wired class. -/
def filledFrontierWiredVertices (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) : Set (RectangleVertex a w h) :=
  {v | v.val.1=a.1 ∨ v.val.1=a.1+(w : ℤ) ∨
    ∃ f ∈ rectangleFilledTopFrontier a w h A, v ∈ f.val}

/-- Every vertex of the proposed lower-domain wiring connects to an original
physical wired side using actual frontier bonds. -/
theorem filledFrontierWiredVertices_connects_to_side (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h))
    (hA : A ∈ rectangleHorizontalCrossingEvent a w h)
    (v : RectangleVertex a w h) (hv : v ∈ filledFrontierWiredVertices a w h A) :
    ∃ t : RectangleVertex a w h, (t.val.1=a.1 ∨ t.val.1=a.1+(w : ℤ)) ∧
      ActualConnected (rectangleGraph a w h) (rectangleFilledTopFrontier a w h A) v t := by
  rcases hv with hv | hv | ⟨f,hf,hvf⟩
  · exact ⟨v,Or.inl hv,SimpleGraph.Reachable.rfl⟩
  · exact ⟨v,Or.inr hv,SimpleGraph.Reachable.rfl⟩
  · exact filled_frontier_bond_vertex_connects_to_side a w h A hA f hf v hvf

end
end PottsContinuity.Push
