module

public import PottsContinuity.Thm3.Push.CrossingRestriction
public import PottsContinuity.Thm3.Push.RectangleHeightCarrier

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.RCInfinite
noncomputable section

/-- The frozen Boolean restriction and the literal PD original-bond
restriction give exactly the same finite configuration. -/
theorem rectangle_bool_configuration_restriction (a : LatticeVertex) (w h : ℕ)
    (V : Finset LatticeVertex) (hV : PD.FK.latticeRectangle a w h ⊆ V)
    (A : Configuration (finiteLatticeGraph V)) :
    boolConfigurationEquiv (rectangleGraph a w h)
      (Foundations.rectangleRestriction a w h V hV ((boolConfigurationEquiv (finiteLatticeGraph V)).symm A)) =
    embeddedConfigurationRestriction _ _ (finiteLatticeVertexEmbedding hV) (finiteLatticeGraph_map_le hV) A := by
  classical
  ext e
  rw [mem_boolConfigurationEquiv]
  erw [mem_embeddedConfigurationRestriction]
  let eV := (PD.FK.squareLattice.induceHomOfLE
    (show (PD.FK.latticeRectangle a w h : Set LatticeVertex) ⊆ (V : Set LatticeVertex)
      from fun x hx => hV hx)).mapEdgeSet e
  change ((boolConfigurationEquiv (finiteLatticeGraph V)).symm A) eV=true ↔ _
  have hm : ((boolConfigurationEquiv (finiteLatticeGraph V)).symm A) eV=true ↔ eV ∈ A := by
    simpa only [Equiv.apply_symm_apply] using
      (mem_boolConfigurationEquiv (finiteLatticeGraph V)
        ((boolConfigurationEquiv (finiteLatticeGraph V)).symm A) eV).symm
  have he : eV = embeddedEdgeEmbedding _ _ (finiteLatticeVertexEmbedding hV)
      (finiteLatticeGraph_map_le hV) e := by
    apply Subtype.ext
    rfl
  exact hm.trans (by rw [he])

/-- The frozen actual horizontal crossing event on a canonical reference
rectangle is exactly the PD shorter-target restriction event. -/
theorem canonical_rectangle_finiteBoolEvent (a : LatticeVertex) (w h n : ℕ) (hn : n ≤ h) :
    RSW.finiteBoolEvent (PD.FK.latticeRectangle a w h)
      (PottsContinuity.horizontalCrossing (PD.FK.latticeRectangle a w h)
        a.1 (a.1+(w : ℤ)) a.2 (a.2+(n : ℤ))) =
    DualityExt.rectangleInnerHorizontalCrossingEvent (rectangle_height_subset a w n h hn) := by
  ext A
  have he := Foundations.horizontalCrossing_iff_PD_rectangleHorizontalCrossingEvent_of_restriction
    a w n (PD.FK.latticeRectangle a w h) (rectangle_height_subset a w n h hn)
    ((boolConfigurationEquiv (rectangleGraph a w h)).symm A)
  erw [rectangle_bool_configuration_restriction] at he
  exact he

/-- Exact probability bridge for the canonical top/side-wired reference
rectangle. This identifies the actual Boolean event `PottsContinuity.horizontalCrossing`,
not merely a crossing of the boundary partition. -/
theorem canonical_rectangle_crossing_probability (a : LatticeVertex) (w h n : ℕ) (hn : n ≤ h)
    (θ : Parameters) :
    RSW.finiteBoundaryEventProbability (PD.FK.latticeRectangle a w h) θ
      (BoundaryCondition.wired {v | v.val.1=a.1 ∨ v.val.1=a.1+(w : ℤ) ∨ v.val.2=a.2+(h : ℤ)})
      (PottsContinuity.horizontalCrossing (PD.FK.latticeRectangle a w h)
        a.1 (a.1+(w : ℤ)) a.2 (a.2+(n : ℤ))) =
    (measure (rectangleGraph a w h) θ
      (BoundaryCondition.wired {v : RectangleVertex a w h |
        v.val.1=a.1 ∨ v.val.1=a.1+(w : ℤ) ∨ v.val.2=a.2+(h : ℤ)})
      (DualityExt.rectangleInnerHorizontalCrossingEvent (rectangle_height_subset a w n h hn))).toReal := by
  unfold RSW.finiteBoundaryEventProbability
  rw [canonical_rectangle_finiteBoolEvent a w h n hn]
  rfl

end
end PottsContinuity.Push
