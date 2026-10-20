module

public import PottsContinuity.Thm3.Push.OuterFrontierComparison
public import PottsContinuity.Thm3.Push.UpwardEmbeddedEvent
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance outerWitnessEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Quantitative reference-witness bound in the ACTUAL outer remaining law.
All active-carrier geometry and induced frozen wiring are discharged; only
the genuine original physical-side wiring is specified. -/
theorem reference_event_le_outer_frozen_active_witness {V : Type*} [Finite V]
    (a : LatticeVertex) (w h : ℕ) (G : SimpleGraph V)
    (f : RectangleVertex a w h ↪ V) (hRG : (rectangleGraph a w h).map f ≤ G)
    (A : Configuration G)
    (hA : embeddedConfigurationRestriction _ _ f hRG A ∈ rectangleHorizontalCrossingEvent a w h)
    (θ : Parameters) (ξ : BoundaryCondition V)
    (hsides : ∀ u v : RectangleVertex a w h,
      (u.val.1=a.1 ∨ u.val.1=a.1+(w : ℤ)) →
      (v.val.1=a.1 ∨ v.val.1=a.1+(w : ℤ)) → ξ.partition.r (f u) (f v))
    (E : Set (Configuration (rectangleGraph a w h))) :
    let D := embeddedConfigurationRestriction _ _ f hRG A
    let R := rectangleFilledTopReveal a w h D
    let Rout := embeddedFilledTopReveal a w h G f hRG A
    (measure (rectangleGraph a w h) θ
      (BoundaryCondition.wired {v : RectangleVertex a w h |
        v.val.1=a.1 ∨ v.val.1=a.1+(w : ℤ) ∨ v.val.2=a.2+(h : ℤ)}) E).toReal ≤
    (measure (edgeRestriction G Rout) θ (frozenBoundary ξ (A ∩ Rout))
      {C | embeddedConfigurationRestriction _ _ ((Function.Embedding.subtype _).trans f)
        (activeUnexaminedGraph_map_le_outer_remaining (rectangleGraph a w h) G f hRG R) C ∈
        upwardEmbeddedEvent _ _ (Function.Embedding.subtype _)
          (activeUnexaminedGraph_map_le _ _) E}).toReal := by
  let D := embeddedConfigurationRestriction _ _ f hRG A
  let R := rectangleFilledTopReveal a w h D
  let J := activeUnexaminedGraph (rectangleGraph a w h) R
  let P := upwardEmbeddedEvent J (rectangleGraph a w h) (Function.Embedding.subtype _)
    (activeUnexaminedGraph_map_le _ _) E
  have hP : IsUpperSet P := upwardEmbeddedEvent_isUpperSet _ _ _ _ E
  have hbase := reference_active_restriction_le_frontier_wired a w h D hA θ P hP
  have houter := frontier_wired_le_outer_frozen_restriction a w h G f hRG A hA θ ξ hsides P hP
  exact (measure_le_preimage_upwardEmbeddedEvent _ _ _ _ θ _ E).trans (hbase.trans houter)

end
end PottsContinuity.Push
