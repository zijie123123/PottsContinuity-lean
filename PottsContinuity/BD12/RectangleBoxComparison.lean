module

public import PottsContinuity.BD12.InfiniteRectangleEvents
public import PottsContinuity.Infinite.LocalComparisons
public import PottsContinuity.Infinite.Bridge
public import PottsContinuity.PD.RCInfinite.SubgraphComparison

/-! Literal rectangle observables and finite wired-box comparison. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory PD.FK PD.RCInfinite
noncomputable section

/-- A rectangle contained in a box reads only sampled bonds of that box. -/
theorem horizontalRectangle_dependsOn_box (a : LatticeVertex) (w h N : ℕ)
    (hbox : PD.FK.latticeRectangle a w h ⊆ latticeBox (0,0) N) :
    DependsOn (boxEdges (0,0) N) (horizontalRectangle a w h) := by
  intro ω η hagree
  have hrestrict : embeddedRestriction (rectangleGraph a w h)
      (frozenEdgeEmbedding (PD.FK.latticeRectangle a w h)) ω =
      embeddedRestriction (rectangleGraph a w h)
        (frozenEdgeEmbedding (PD.FK.latticeRectangle a w h)) η := by
    apply Finset.ext
    intro e
    have he : frozenEdgeEmbedding (PD.FK.latticeRectangle a w h) e ∈ boxEdges (0,0) N := by
      change frozenEdgeEmbedding (PD.FK.latticeRectangle a w h) e ∈
        Set.range (frozenEdgeEmbedding (latticeBox (0,0) N))
      exact frozenEdgeEmbedding_range_mono hbox ⟨e,rfl⟩
    have hv : ω (frozenEdgeEmbedding (PD.FK.latticeRectangle a w h) e) =
        η (frozenEdgeEmbedding (PD.FK.latticeRectangle a w h) e) := hagree _ he
    have hviff : ω (frozenEdgeEmbedding (PD.FK.latticeRectangle a w h) e) = true ↔
        η (frozenEdgeEmbedding (PD.FK.latticeRectangle a w h) e) = true := by rw [hv]
    exact (mem_embeddedRestriction _ _ ω e).trans
      (hviff.trans (mem_embeddedRestriction _ _ η e).symm)
  change embeddedRestriction _ _ ω ∈ rectangleHorizontalCrossingEvent a w h ↔
    embeddedRestriction _ _ η ∈ rectangleHorizontalCrossingEvent a w h
  rw [hrestrict]

/-- The frozen wired infinite rectangle probability is at most the sampled
wired-box rectangle probability whenever the entire rectangle is contained. -/
theorem wired_rectangle_probability_le_wired_box (θ : Parameters)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (a : LatticeVertex) (w h N : ℕ)
    (hbox : PD.FK.latticeRectangle a w h ⊆ latticeBox (0,0) N) :
    μ.real (horizontalRectangle a w h) ≤
      (wiredBoxProbabilityMeasure θ (0,0) N : Measure LatticeConfiguration).real
        (horizontalRectangle a w h) := by
  have hbound := Infinite.limit_le_wired_box_local θ μ
    (Infinite.isRCInfiniteVolumeLimit_to_PD_box _ _ _ _ hμ) N
    (horizontalRectangle_isCylinder a w h) (horizontalRectangle_dependsOn_box a w h N hbox)
    (horizontalRectangle_isUpperSet a w h)
  simpa only [boxMeasure_wired] using hbound

end
end PottsContinuity.BD12
