module

public import PottsContinuity.Thm3.Push.FiniteRectangleEventBridge
public import PottsContinuity.Thm3.Push.RectangleBandSideErasure

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PD.Duality BD12
noncomputable section

/-- The full horizontal rectangle event uses exactly the two coordinate sides. -/
theorem rectangleHorizontalCrossingEvent_eq_arcs (a : LatticeVertex) (w b : ℕ) :
    rectangleHorizontalCrossingEvent a w b =
      arcsConnectionEvent (rectangleGraph a w b)
        {u | u.val.1=a.1} {v | v.val.1=a.1+(w:ℤ)} := by
  ext C
  constructor
  · rintro ⟨u,v,hu,hv,hp⟩
    exact ⟨u,(Finset.mem_filter.mp hu).2,v,(Finset.mem_filter.mp hv).2,hp⟩
  · rintro ⟨u,hu,v,hv,hp⟩
    exact ⟨u,v,Finset.mem_filter.mpr ⟨u.property,hu⟩,
      Finset.mem_filter.mpr ⟨v.property,hv⟩,hp⟩

/-- The band event is the same literal shorter-target rectangle event. -/
theorem rectangleBandConnectionEvent_eq_inner (a : LatticeVertex) (w b h : ℕ)
    (hbh : b ≤ h) :
    rectangleBandConnectionEvent a w b h hbh =
      DualityExt.rectangleInnerHorizontalCrossingEvent (rectangle_height_subset a w b h hbh) := by
  rw [DualityExt.rectangleInnerHorizontalCrossingEvent, rectangleHorizontalCrossingEvent_eq_arcs]
  rfl

/-- Exact frozen-to-PD probability bridge for actual sampled band crossings. -/
theorem rectangleBand_crossing_probability (a : LatticeVertex) (w h b : ℕ)
    (hbh : b ≤ h) (θ : Parameters) :
    RSW.finiteBoundaryEventProbability (PD.FK.latticeRectangle a w h) θ
      (BoundaryCondition.wired {v | v.val.1=a.1 ∨ v.val.1=a.1+(w:ℤ) ∨ v.val.2=a.2+(h:ℤ)})
      (PottsContinuity.horizontalCrossing (PD.FK.latticeRectangle a w h)
        a.1 (a.1+(w:ℤ)) a.2 (a.2+(b:ℤ))) =
    (measure (rectangleGraph a w h) θ
      (BoundaryCondition.wired {v : RectangleVertex a w h |
        v.val.1=a.1 ∨ v.val.1=a.1+(w:ℤ) ∨ v.val.2=a.2+(h:ℤ)})
      (rectangleBandConnectionEvent a w b h hbh)).toReal := by
  rw [rectangleBandConnectionEvent_eq_inner]
  exact canonical_rectangle_crossing_probability a w h b hbh θ

end
end PottsContinuity.Push
