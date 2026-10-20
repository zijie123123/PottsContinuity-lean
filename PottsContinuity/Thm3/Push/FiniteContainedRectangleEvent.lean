module

public import PottsContinuity.Thm3.Push.FiniteRectangleEventBridge
public import PottsContinuity.Thm3.Push.EmbeddedRestrictionStates

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.RCInfinite
noncomputable section

/-- Frozen Boolean crossings in any finite containing volume are exactly
actual PD crossings read on the SAME original target bonds. -/
theorem finiteBoolEvent_contained_rectangle (a : LatticeVertex) (w n : ℕ)
    (V : Finset LatticeVertex) (hV : PD.FK.latticeRectangle a w n ⊆ V) :
    RSW.finiteBoolEvent V (PottsContinuity.horizontalCrossing V
      a.1 (a.1+(w : ℤ)) a.2 (a.2+(n : ℤ))) =
    {A | embeddedConfigurationRestriction _ _ (finiteLatticeVertexEmbedding hV)
      (finiteLatticeGraph_map_le hV) A ∈ rectangleHorizontalCrossingEvent a w n} := by
  ext A
  have he := Foundations.horizontalCrossing_iff_PD_rectangleHorizontalCrossingEvent_of_restriction
    a w n V hV ((boolConfigurationEquiv (finiteLatticeGraph V)).symm A)
  erw [rectangle_bool_configuration_restriction] at he
  exact he

/-- Passing through an intermediate reference rectangle does not alter the
actual shorter crossing event in the outer finite volume. -/
theorem nested_rectangle_event_eq_finiteBoolEvent (a : LatticeVertex) (w h n : ℕ)
    (hn : n ≤ h) (V : Finset LatticeVertex) (hV : PD.FK.latticeRectangle a w h ⊆ V) :
    {A | DualityExt.rectangleConfigurationRestriction (rectangle_height_subset a w n h hn)
      (embeddedConfigurationRestriction _ _ (finiteLatticeVertexEmbedding hV)
        (finiteLatticeGraph_map_le hV) A) ∈ rectangleHorizontalCrossingEvent a w n} =
    RSW.finiteBoolEvent V (PottsContinuity.horizontalCrossing V
      a.1 (a.1+(w : ℤ)) a.2 (a.2+(n : ℤ))) := by
  let hsmall : PD.FK.latticeRectangle a w n ⊆ V :=
    (rectangle_height_subset a w n h hn).trans hV
  rw [finiteBoolEvent_contained_rectangle a w n V hsmall]
  ext A
  have he := embeddedConfigurationRestriction_comp (rectangleGraph a w n) (rectangleGraph a w h)
    (finiteLatticeGraph V) (DualityExt.rectangleVertexEmbedding (rectangle_height_subset a w n h hn))
    (finiteLatticeVertexEmbedding hV)
    (DualityExt.rectangleGraph_map_rectangleVertexEmbedding (rectangle_height_subset a w n h hn))
    (finiteLatticeGraph_map_le hV) A
  exact Iff.of_eq (congrArg (fun C => C ∈ rectangleHorizontalCrossingEvent a w n) he.symm)

end
end PottsContinuity.Push
