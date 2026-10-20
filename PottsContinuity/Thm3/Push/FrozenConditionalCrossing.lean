module

public import PottsContinuity.Thm3.Push.RestoredConditionalLaw
public import PottsContinuity.Thm3.Push.OuterRestoredCrossingBound
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance frozenCrossingEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace
local instance frozenCrossingDiscrete {V : Type*} (G : SimpleGraph V) :
    DiscreteMeasurableSpace (Configuration G) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Exact event form of the full frozen conditional law, on the original
configuration space and its full power-set sigma field. -/
theorem frozen_filter_event_eq_deleted_restore_preimage {V : Type*} [Finite V]
    (G : SimpleGraph V) (θ : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) (F : RemovedConfiguration G R) (E : Set (Configuration G)) :
    (((law G θ ξ).filter (frozenStateEvent R F)
      (frozenStateEvent_support θ ξ R F)).toMeasure E) =
    measure (edgeRestriction G R) θ (frozenBoundary ξ F.val)
      {C | restoreRemainingConfiguration G R F C ∈ E} := by
  rw [← edgeRestrictionLaw_map_restore_eq_filter G θ ξ R F]
  exact PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete (MeasurableSet.of_discrete)

/-- The genuine full OUTER law, conditioned on the actual filled record's
observed bond states, has at least the reference probability of an actual
shorter-target crossing. This discharges the conditional crossing estimate
needed on each good upper-band record, for arbitrary interior FK parameters. -/
theorem reference_crossing_le_outer_frozen_conditional_crossing {V : Type*} [Finite V]
    (a : LatticeVertex) (w h n : ℕ) (hn : n ≤ h) (G : SimpleGraph V)
    (f : RectangleVertex a w h ↪ V) (hRG : (rectangleGraph a w h).map f ≤ G)
    (A : Configuration G)
    (hA : embeddedConfigurationRestriction _ _ f hRG A ∈ rectangleHorizontalCrossingEvent a w h)
    (θ : Parameters) (ξ : BoundaryCondition V)
    (hsides : ∀ u v : RectangleVertex a w h,
      (u.val.1=a.1 ∨ u.val.1=a.1+(w : ℤ)) →
      (v.val.1=a.1 ∨ v.val.1=a.1+(w : ℤ)) → ξ.partition.r (f u) (f v)) :
    let Rout := embeddedFilledTopReveal a w h G f hRG A
    let F : RemovedConfiguration G Rout := ⟨A ∩ Rout,Finset.inter_subset_right⟩
    (measure (rectangleGraph a w h) θ
      (BoundaryCondition.wired {v : RectangleVertex a w h |
        v.val.1=a.1 ∨ v.val.1=a.1+(w : ℤ) ∨ v.val.2=a.2+(h : ℤ)})
      (DualityExt.rectangleInnerHorizontalCrossingEvent (rectangle_height_subset a w n h hn))).toReal ≤
    (((law G θ ξ).filter (frozenStateEvent Rout F)
      (frozenStateEvent_support θ ξ Rout F)).toMeasure
      {B | DualityExt.rectangleConfigurationRestriction (rectangle_height_subset a w n h hn)
        (embeddedConfigurationRestriction _ _ f hRG B) ∈ rectangleHorizontalCrossingEvent a w n}).toReal := by
  dsimp only
  rw [frozen_filter_event_eq_deleted_restore_preimage]
  exact reference_crossing_le_outer_frozen_restored_crossing a w h n hn G f hRG A hA θ ξ hsides

end
end PottsContinuity.Push
