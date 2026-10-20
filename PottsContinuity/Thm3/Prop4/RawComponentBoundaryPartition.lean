module

public import PottsContinuity.Thm3.Prop4.RawRemainingBoundaryWiring
public import PottsContinuity.Thm3.Prop4.ComponentPocketMarginal

/-! # The exact wired partition on each raw remaining component -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial Push
noncomputable section

/-- Actual endpoints of queried source bonds, on the original rectangle carrier. -/
def sourceMarkedRawBoundaryVertices (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h)) : Set (RectangleVertex a w h) :=
  {x | ∃ e ∈ sourceMarkedRawReveal a w h u v A, x ∈ e.val}

/-- The literal induced partition of the free source law after the raw record. -/
def sourceMarkedRawBoundary (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h)) :
    BoundaryCondition (RectangleVertex a w h) :=
  frozenBoundary (BoundaryCondition.free ∅)
    (Exploration.revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A).val

/-- Every nontrivial induced boundary join uses queried original-edge endpoints. -/
theorem sourceMarkedRawBoundary_rel_support (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h))
    (x y : RectangleVertex a w h)
    (hxy : (sourceMarkedRawBoundary a w h u v A).partition.r x y) :
    x = y ∨ x ∈ sourceMarkedRawBoundaryVertices a w h u v A ∧
      y ∈ sourceMarkedRawBoundaryVertices a w h u v A := by
  let B := Exploration.revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A
  let W := sourceMarkedRawBoundaryVertices a w h u v A
  have hsupport := componentSetoid_le_wired_union_of_edge_endpoints (BoundaryCondition.free ∅) W B.val
    (fun e he z hz => ⟨e,B.property he,hz⟩)
  have hwire := (BoundaryCondition.wired_rel _ x y).mp (hsupport hxy)
  rcases hwire with heq | ⟨hx,hy⟩
  · exact Or.inl heq
  · right
    change x ∈ (∅ : Set (RectangleVertex a w h)) ∪ W at hx
    change y ∈ (∅ : Set (RectangleVertex a w h)) ∪ W at hy
    exact ⟨by simpa only [Set.empty_union] using hx,by simpa only [Set.empty_union] using hy⟩

/-- A nonempty remaining path supplies a genuine fresh bond incident to its start. -/
theorem sourceMarkedRaw_active_of_remaining_reachable_ne (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h))
    (x y : RectangleVertex a w h) (hne : x ≠ y)
    (hconn : (sourceMarkedRawDomain a w h u v A).Reachable x y) :
    ∃ e : (rectangleGraph a w h).edgeSet, e ∉ sourceMarkedRawReveal a w h u v A ∧ x ∈ e.val := by
  obtain ⟨p⟩ := hconn
  cases p with
  | nil => exact (hne rfl).elim
  | @cons x z y hxz p =>
    change (edgeRestriction (rectangleGraph a w h) (sourceMarkedRawReveal a w h u v A)).Adj x z at hxz
    obtain ⟨hG,hnot⟩ := SimpleGraph.deleteEdges_adj.mp hxz
    let e : (rectangleGraph a w h).edgeSet := ⟨s(x,z),(rectangleGraph a w h).mem_edgeSet.mpr hG⟩
    refine ⟨e,?_,Sym2.mem_iff.mpr (Or.inl rfl)⟩
    intro he
    exact hnot ⟨e,he,rfl⟩

end
end PottsContinuity.Thm3.Prop4
