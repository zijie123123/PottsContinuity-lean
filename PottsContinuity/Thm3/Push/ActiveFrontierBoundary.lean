module

public import PottsContinuity.Thm3.Push.ActiveFrontierCarrier
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- An active vertex off the wired frontier cannot lie on the original top
row. This uses the actual filled top-port labels and the four incident faces. -/
theorem active_filledFrontier_not_top (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h))
    (hA : A ∈ rectangleHorizontalCrossingEvent a w h)
    (x : unexaminedVertices (rectangleGraph a w h) (rectangleFilledTopReveal a w h A))
    (hx : x.val ∉ filledFrontierWiredVertices a w h A) :
    x.val.val.2 ≠ a.2+(h : ℤ) := by
  classical
  intro htop
  have hl : x.val.val.1 ≠ a.1 := fun he => hx (Or.inl he)
  have hr : x.val.val.1 ≠ a.1+(w : ℤ) := fun he => hx (Or.inr (Or.inl he))
  have hprops := (mem_latticeRectangle a x.val.val w h).mp x.val.property
  have hleft : a.1 < x.val.val.1 := by omega
  have hright : x.val.val.1 < a.1+(w : ℤ) := by omega
  have hno : ∀ t, ¬ (latticeCellBoundaryGraph (rectangleFilledFaceCells a w h A)).Adj
      x.val.val t := by
    intro t hcell
    have ht := filledCell_neighbor_mem_rectangle_off_sides a w h A hA x.val hleft hright t hcell
    let y : RectangleVertex a w h := ⟨t,ht⟩
    have hadj := (filledTopFrontier_adj_iff_cellBoundary a w h A x.val y).mp hcell
    let f : (rectangleGraph a w h).edgeSet :=
      ⟨s(x.val,y),(rectangleGraph a w h).mem_edgeSet.mpr (openGraph_le _ _ hadj)⟩
    have hf : f ∈ rectangleFilledTopFrontier a w h A :=
      (coe_mem_openEdges_iff _ _ f).mp ((openGraph_adj _ _ x.val y).mp hadj)
    exact hx (Or.inr (Or.inr ⟨f,hf,(Sym2.mem_iff').mpr (Or.inl rfl)⟩))
  obtain ⟨g,hg,hxg⟩ := x.property
  have hbg : x.val.val ∈ (rectanglePrimalEdgeBond a w h g).toSym2 := by
    erw [rectanglePrimalEdgeBond_toSym2_public]
    exact Sym2.mem_map.mpr ⟨x.val,hxg,rfl⟩
  have hfalse : (rectanglePrimalEdgeBond a w h g).faceBase false ∉
      rectangleFilledFaceCells a w h A := by
    intro hm
    exact hg ((mem_filledTopReveal_iff_cellFaces a w h A g).mpr (Or.inl hm))
  have htrue : x.val.val ∈ rectangleFilledFaceCells a w h A := by
    have hm := rectangleFilledFaceCells_top a w h A x.val.val.1 hleft.le hright
    simpa only [← htop] using hm
  exact hfalse ((cellBoundary_no_adj_incident_face_label _ _ hno _ hbg false).mpr htrue)

/-- The reference rectangle's entire top/side boundary is avoided away from
the proved frontier wiring. Together with neighbor closure this discharges
the geometric hypotheses of the closed-interior FK comparison. -/
theorem active_filledFrontier_boundary_avoid (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h))
    (hA : A ∈ rectangleHorizontalCrossingEvent a w h)
    {x : unexaminedVertices (rectangleGraph a w h) (rectangleFilledTopReveal a w h A)}
    (hx : x.val ∉ filledFrontierWiredVertices a w h A) :
    x.val ∉ (BoundaryCondition.wired {v : RectangleVertex a w h |
      v.val.1=a.1 ∨ v.val.1=a.1+(w : ℤ) ∨ v.val.2=a.2+(h : ℤ)}).boundary := by
  rintro (hl | hr | ht)
  · exact hx (Or.inl hl)
  · exact hx (Or.inr (Or.inl hr))
  · exact active_filledFrontier_not_top a w h A hA x hx ht

end
end PottsContinuity.Push
