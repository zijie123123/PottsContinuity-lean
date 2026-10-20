module

public import PottsContinuity.Thm3.Push.FiniteRectangleEventBridge
public import PottsContinuity.Thm3.Push.RectangleBandSideErasure

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality PD.RCInfinite DualityExt
noncomputable section

/-- The sampled bottom-band connection event is exactly the original Boolean
horizontal crossing in the containing rectangle. -/
theorem rectangleBandConnectionEvent_eq_finiteBoolEvent
    (a : LatticeVertex) (w b h : ℕ) (hbh : b ≤ h) :
    Push.rectangleBandConnectionEvent a w b h hbh =
      finiteBoolEvent (PD.FK.latticeRectangle a w h)
        (horizontalCrossing (PD.FK.latticeRectangle a w h)
          a.1 (a.1+(w:ℤ)) a.2 (a.2+(b:ℤ))) := by
  rw [Push.canonical_rectangle_finiteBoolEvent a w h b hbh]
  ext C
  have hc : rectangleConfigurationRestriction (Push.rectangle_height_subset a w b h hbh) C =
      embeddedConfigurationRestriction (rectangleGraph a w b) (rectangleGraph a w h)
        (Push.rectangleBandEmbedding a w b h hbh)
        (Push.rectangleBandEmbedding_map_le a w b h hbh) C := rfl
  change (_ ∈ BD12.arcsConnectionEvent _ _ _) ↔
    (_ ∈ rectangleHorizontalCrossingEvent a w b)
  rw [hc]
  simp only [BD12.arcsConnectionEvent, rectangleHorizontalCrossingEvent,
    Set.mem_ofPred_eq,rectangleLeftSide,rectangleRightSide,Finset.mem_filter]
  constructor
  · rintro ⟨u,hu,v,hv,hp⟩
    exact ⟨u,v,⟨u.property,hu⟩,⟨v.property,hv⟩,hp⟩
  · rintro ⟨u,v,hu,hv,hp⟩
    exact ⟨u,hu.2,v,hv.2,hp⟩

end
end PottsContinuity.RSW
