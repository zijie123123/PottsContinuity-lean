module

public import PottsContinuity.PlanarTopology.RectangleSampledClosedDual
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial

/-- Genuine boundary-arc labels belong to the expanded finite face carrier. -/
theorem rectangle_dual_arc_mem_expanded (a : LatticeVertex) (w h : ℕ)
    (u v s : LatticeVertex)
    (hs : s ∈ rectangleLowerDualArc a w h u v ∨ s ∈ rectangleUpperDualArc a w h u v) :
    s ∈ rectangleDualExpanded a w h := by
  rw [rectangleDualExpanded,mem_latticeRectangle]
  rcases hs with hs | hs
  · rcases hs with hs | hs | hs <;> omega
  · rcases hs with hs | hs | hs <;> omega

/-- Boundary-arc separation on the ORIGINAL face labels of the sampled
rectangle. Unlike a full-plane extension, this graph adds no unsampled edges. -/
theorem rectangle_sampled_dual_screen_excludes_primal (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (u v : RectangleVertex a w h)
    (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (s t : LatticeVertex)
    (hs : s ∈ rectangleLowerDualArc a w h u.val v.val)
    (ht : t ∈ rectangleUpperDualArc a w h u.val v.val)
    (q : (rectangleSampledClosedDualGraph a w h A).Walk s t) :
    ¬ ActualConnected (rectangleGraph a w h) A u v := by
  have hs' := rectangle_dual_arc_mem_expanded a w h u.val v.val s (Or.inl hs)
  have ht' := rectangle_dual_arc_mem_expanded a w h u.val v.val t (Or.inr ht)
  obtain ⟨q'⟩ := rectangleSampledClosedDualGraph_walk_finite a w h A q hs' ht'
  exact rectangle_boundary_arc_dual_excludes_primal a w h A u v hu hv
    ⟨s,hs'⟩ ⟨t,ht'⟩ hs ht q'

/-- Two actual sampled dual arms and an actual sampled dual connector
separate the original primal endpoints in their SAME modified configuration. -/
theorem rectangle_disconnected_of_sampled_dual_arms_and_connector
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    (u v : RectangleVertex a w h) (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (s f g t : LatticeVertex)
    (hs : s ∈ rectangleLowerDualArc a w h u.val v.val)
    (ht : t ∈ rectangleUpperDualArc a w h u.val v.val)
    (minus : (rectangleSampledClosedDualGraph a w h A).Walk s f)
    (center : (rectangleSampledClosedDualGraph a w h A).Walk f g)
    (plus : (rectangleSampledClosedDualGraph a w h A).Walk g t) :
    ¬ ActualConnected (rectangleGraph a w h) A u v :=
  rectangle_sampled_dual_screen_excludes_primal a w h A u v hu hv s t hs ht
    (minus.append (center.append plus))

end PottsContinuity.PlanarTopology
