module

public import PottsContinuity.Thm3.Prop4.MarkedCellOutsidePorts
public import PottsContinuity.Thm3.Prop4.TwoExteriorPortsParity
public import PottsContinuity.Thm3.Prop4.MarkedFaceFrontierBridge
public import PottsContinuity.Thm3.Prop4.MarkedLowerCellLabels

/-! # Actual marked frontier connectivity from literal complementary arc labels -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- Every face region containing the lower exterior arc and excluding the
upper exterior arc has an actual original-bond frontier joining the marks. -/
theorem rawFaceRegionFrontier_connects_of_marked_arc_labels
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (u v : RectangleVertex a w h) (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (P : LatticeVertex → Prop)
    (hlower : ∀ f ∈ PlanarTopology.rectangleLowerDualArc a w h u.val v.val, P f)
    (hupper : ∀ f ∈ PlanarTopology.rectangleUpperDualArc a w h u.val v.val, ¬P f) :
    ActualConnected (rectangleGraph a w h) (rawFaceRegionFrontier a w h P) u v := by
  classical
  let S := markedLowerFaceCells a w h P
  obtain ⟨hl,hr,hb,ht⟩ := markedLowerFaceCells_side_labels_of_arc_labels a w h hw hh u v hu hv P hlower hupper
  have hne : u ≠ v := by
    intro heq
    have hx := congrArg (fun z : RectangleVertex a w h => z.val.1) heq
    omega
  have hconn : ((latticeCellBoundaryGraph S).induce (PD.FK.latticeRectangle a w h : Set LatticeVertex)).Reachable u v := by
    apply reachable_induce_of_even_degrees_and_two_exterior_ports
      (latticeCellBoundaryGraph S) (PD.FK.latticeRectangle a w h : Set LatticeVertex) u v hne
      (a.1-1,u.val.2) (a.1+(w : ℤ)+1,v.val.2)
    · change (a.1-1,u.val.2) ∉ PD.FK.latticeRectangle a w h
      rw [PD.FK.mem_latticeRectangle]
      omega
    · change (a.1+(w : ℤ)+1,v.val.2) ∉ PD.FK.latticeRectangle a w h
      rw [PD.FK.mem_latticeRectangle]
      omega
    · exact latticeCellBoundaryGraph_even_degree S
    · intro z t
      exact cellBoundary_outside_neighbor_iff_of_marked_side_labels a w h S u v z hu hv hl hr hb ht t
  let f : (latticeCellBoundaryGraph S).induce (PD.FK.latticeRectangle a w h : Set LatticeVertex) →g
      openGraph (rectangleGraph a w h) (rawFaceRegionFrontier a w h P) := {
    toFun := id
    map_rel' := fun {x y} hxy => (rawFaceRegionFrontier_adj_iff_marked_cell_boundary a w h P x y).mp hxy }
  exact hconn.map f

/-- The actual lower raw explored frontier joins the source side marks on
every genuine original marked connection. No planar alternative is assumed. -/
theorem sampledLowerRawFrontier_connects_of_marked_connection
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (u v : RectangleVertex a w h) (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (A : Configuration (rectangleGraph a w h)) (hA : ActualConnected (rectangleGraph a w h) A u v) :
    ActualConnected (rectangleGraph a w h)
      (rawFaceRegionFrontier a w h (sampledDualSeedRegion a w h A
        (PlanarTopology.rectangleLowerDualArc a w h u.val v.val))) u v := by
  obtain ⟨hl,hu'⟩ := sampledLowerRegion_exterior_labels a w h u v hu hv A hA
  exact rawFaceRegionFrontier_connects_of_marked_arc_labels a w h hw hh u v hu hv _ hl hu'

/-- The existing exact marked lower frontier now has its unconditional
source connection theorem. The previous sampled-alternative input is gone. -/
theorem markedLowerFrontier_connects_of_marked_connection
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (u v : RectangleVertex a w h) (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (A : Configuration (rectangleGraph a w h)) (hA : ActualConnected (rectangleGraph a w h) A u v) :
    ActualConnected (rectangleGraph a w h) (markedLowerFrontier a w h u v A) u v := by
  rw [markedLowerFrontier_eq_source_raw_frontier]
  exact sampledLowerRawFrontier_connects_of_marked_connection a w h hw hh u v hu hv A hA

end
end PottsContinuity.Thm3.Prop4
