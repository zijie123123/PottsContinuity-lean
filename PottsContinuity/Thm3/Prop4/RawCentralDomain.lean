module

public import PottsContinuity.Thm3.Prop4.RawPhysicalBoundary

/-! # The marked recorded class and all its remaining edge components -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK Push
noncomputable section

/-- The union of actual remaining edge components touching the recorded
class of the first mark. No extra bond is queried in this construction. -/
def sourceMarkedRawCentralVertices (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h)) :
    Set (RectangleVertex a w h) :=
  {x | ∃ y, (sourceMarkedRawDomain a w h u v A).Reachable x y ∧
    (sourceMarkedRawBoundary a w h u v A).partition.r y u}

/-- The first mark belongs to the retained union. -/
theorem sourceMarkedRawCentralVertices_mark (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h)) :
    u ∈ sourceMarkedRawCentralVertices a w h u v A :=
  ⟨u,SimpleGraph.Reachable.refl _,(sourceMarkedRawBoundary a w h u v A).partition.refl _⟩

/-- The retained marked union is closed under every remaining original edge. -/
theorem sourceMarkedRawCentralVertices_edge_closed (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h))
    (x : RectangleVertex a w h) (hx : x ∈ sourceMarkedRawCentralVertices a w h u v A)
    (y : RectangleVertex a w h) (hxy : (sourceMarkedRawDomain a w h u v A).Adj x y) :
    y ∈ sourceMarkedRawCentralVertices a w h u v A := by
  obtain ⟨z,hxz,hzu⟩ := hx
  exact ⟨z,hxy.symm.reachable.trans hxz,hzu⟩

/-- Every queried-adjacent vertex in the retained union is in the SAME
actual recorded class as the original mark. -/
theorem sourceMarkedRawCentralVertices_boundary_class (a : LatticeVertex) (w h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) (u v : RectangleVertex a w h)
    (hu : u.val.1 = a.1) (A : Configuration (rectangleGraph a w h))
    (x : RectangleVertex a w h) (hx : x ∈ sourceMarkedRawCentralVertices a w h u v A)
    (hxB : x ∈ sourceMarkedRawBoundaryVertices a w h u v A) :
    (sourceMarkedRawBoundary a w h u v A).partition.r x u := by
  obtain ⟨y,hxy,hyu⟩ := hx
  have huB := sourceMarkedRawBoundaryVertices_of_rectangle_side a w h hw hh u v u A (Or.inl hu)
  have hyB : y ∈ sourceMarkedRawBoundaryVertices a w h u v A := by
    rcases sourceMarkedRawBoundary_rel_support a w h u v A y u hyu with h | h
    · exact h ▸ huB
    · exact h.1
  by_cases hne : x = y
  · exact hne ▸ hyu
  · have hxActive := sourceMarkedRaw_active_of_remaining_reachable_ne a w h u v A x y hne hxy
    have hyActive := sourceMarkedRaw_active_of_remaining_reachable_ne a w h u v A y x (Ne.symm hne) hxy.symm
    exact (sourceMarkedRawBoundary a w h u v A).partition.trans
      (sourceMarkedRaw_remaining_component_boundary_wired a w h hw hh u v A (BoundaryCondition.free ∅)
        x y hxy hxActive hyActive hxB hyB) hyu

/-- No actual induced raw boundary identification leaves the retained marked
union. Other components can therefore be integrated without merging it. -/
theorem sourceMarkedRawCentralVertices_boundary_closed (a : LatticeVertex) (w h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) (u v : RectangleVertex a w h)
    (hu : u.val.1 = a.1) (A : Configuration (rectangleGraph a w h))
    (x : RectangleVertex a w h) (hx : x ∈ sourceMarkedRawCentralVertices a w h u v A)
    (y : RectangleVertex a w h) (hxy : (sourceMarkedRawBoundary a w h u v A).partition.r x y) :
    y ∈ sourceMarkedRawCentralVertices a w h u v A := by
  rcases sourceMarkedRawBoundary_rel_support a w h u v A x y hxy with heq | ⟨hxB,hyB⟩
  · exact heq ▸ hx
  · have hxu := sourceMarkedRawCentralVertices_boundary_class a w h hw hh u v hu A x hx hxB
    exact ⟨y,SimpleGraph.Reachable.refl _,
      (sourceMarkedRawBoundary a w h u v A).partition.trans
        ((sourceMarkedRawBoundary a w h u v A).partition.symm hxy) hxu⟩

/-- The actual induced raw partition on the whole marked retained union is
wired exactly on queried-adjacent vertices and free on all other vertices. -/
theorem sourceMarkedRawCentralVertices_partition_eq_wired
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (u v : RectangleVertex a w h) (hu : u.val.1 = a.1)
    (A : Configuration (rectangleGraph a w h)) :
    (isolatedExtensionPullbackBoundary (pocketInclusion (sourceMarkedRawCentralVertices a w h u v A))
      (sourceMarkedRawBoundary a w h u v A)).partition =
    (BoundaryCondition.wired {x : sourceMarkedRawCentralVertices a w h u v A |
      x.val ∈ sourceMarkedRawBoundaryVertices a w h u v A}).partition := by
  apply Setoid.ext
  intro x y
  change (sourceMarkedRawBoundary a w h u v A).partition.r x.val y.val ↔ _
  constructor
  · intro hxy
    apply (BoundaryCondition.wired_rel _ _ _).mpr
    rcases sourceMarkedRawBoundary_rel_support a w h u v A x.val y.val hxy with heq | h
    · exact Or.inl (Subtype.ext heq)
    · exact Or.inr h
  · intro hxy
    rcases (BoundaryCondition.wired_rel _ _ _).mp hxy with heq | ⟨hx,hy⟩
    · exact heq ▸ (sourceMarkedRawBoundary a w h u v A).partition.refl x.val
    · exact (sourceMarkedRawBoundary a w h u v A).partition.trans
        (sourceMarkedRawCentralVertices_boundary_class a w h hw hh u v hu A x.val x.property hx)
        ((sourceMarkedRawBoundary a w h u v A).partition.symm
          (sourceMarkedRawCentralVertices_boundary_class a w h hw hh u v hu A y.val y.property hy))

end
end PottsContinuity.Thm3.Prop4
