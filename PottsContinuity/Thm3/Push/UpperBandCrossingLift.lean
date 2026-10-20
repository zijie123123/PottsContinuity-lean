module

public import PottsContinuity.Thm3.Push.UpperBandCarrier
public import PottsContinuity.Thm3.Push.EmbeddedFrontierWiring
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- An actual upper-band crossing is an actual crossing of the reference
rectangle on its original bonds. No virtual boundary edges enter the lift. -/
theorem upper_band_crossing_implies_reference_crossing (a : LatticeVertex)
    (w H t : ℕ) (ht : t ≤ H) (A : Configuration (rectangleGraph a w H))
    (hband : DualityExt.rectangleConfigurationRestriction (rectangle_upper_band_subset a w H t ht) A ∈
      rectangleHorizontalCrossingEvent (a.1,a.2+(t : ℤ)) w (H-t)) :
    A ∈ rectangleHorizontalCrossingEvent a w H := by
  let hrect := rectangle_upper_band_subset a w H t ht
  let f := DualityExt.rectangleVertexEmbedding hrect
  let hGH := DualityExt.rectangleGraph_map_rectangleVertexEmbedding hrect
  obtain ⟨u,v,hu,hv,hconn⟩ := hband
  have hu' : (f u).val ∈ rectangleLeftSide a w H := by
    change (f u).val ∈ (PD.FK.latticeRectangle a w H).filter (fun z => z.1=a.1)
    exact Finset.mem_filter.mpr ⟨(f u).property,(Finset.mem_filter.mp hu).2⟩
  have hv' : (f v).val ∈ rectangleRightSide a w H := by
    change (f v).val ∈ (PD.FK.latticeRectangle a w H).filter (fun z => z.1=a.1+(w : ℤ))
    exact Finset.mem_filter.mpr ⟨(f v).property,(Finset.mem_filter.mp hv).2⟩
  exact ⟨f u,f v,hu',hv',actualConnected_mono
    (embeddedConfigurationEmbedding_restriction_subset _ _ f hGH A)
    (actualConnected_embeddedConfiguration _ _ f hGH _ hconn)⟩

end
end PottsContinuity.Push
