module

public import PottsContinuity.Thm3.Push.FiniteContainedRectangleEvent

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.RCInfinite
noncomputable section

/-- An arbitrary contained target rectangle may be read through an
intermediate reference rectangle without altering any actual sampled bond
or the frozen Boolean crossing event in the outer finite volume. -/
theorem intermediate_rectangle_event_eq_finiteBoolEvent
    {a b : LatticeVertex} {w n W H : ℕ}
    (hrect : PD.FK.latticeRectangle a w n ⊆ PD.FK.latticeRectangle b W H)
    (V : Finset LatticeVertex) (hV : PD.FK.latticeRectangle b W H ⊆ V) :
    {A | DualityExt.rectangleConfigurationRestriction hrect
      (embeddedConfigurationRestriction _ _ (finiteLatticeVertexEmbedding hV)
        (finiteLatticeGraph_map_le hV) A) ∈ rectangleHorizontalCrossingEvent a w n} =
    RSW.finiteBoolEvent V (PottsContinuity.horizontalCrossing V
      a.1 (a.1+(w : ℤ)) a.2 (a.2+(n : ℤ))) := by
  let hsmall : PD.FK.latticeRectangle a w n ⊆ V := hrect.trans hV
  rw [finiteBoolEvent_contained_rectangle a w n V hsmall]
  ext A
  have he := embeddedConfigurationRestriction_comp (rectangleGraph a w n) (rectangleGraph b W H)
    (finiteLatticeGraph V) (DualityExt.rectangleVertexEmbedding hrect) (finiteLatticeVertexEmbedding hV)
    (DualityExt.rectangleGraph_map_rectangleVertexEmbedding hrect) (finiteLatticeGraph_map_le hV) A
  exact Iff.of_eq (congrArg (fun C => C ∈ rectangleHorizontalCrossingEvent a w n) he.symm)

end
end PottsContinuity.Push
