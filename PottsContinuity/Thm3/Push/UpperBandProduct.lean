module

public import PottsContinuity.Thm3.Push.EmbeddedUpperBandRecord
public import PottsContinuity.Thm3.Push.UpperBandCrossingLift
public import PottsContinuity.Thm3.Push.FrozenConditionalCrossing
public import PottsContinuity.FKC.FiniteFK.FiniteConditionalGoodFiberBound
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance upperProductEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace
local instance upperProductDiscrete {V : Type*} (G : SimpleGraph V) :
    DiscreteMeasurableSpace (Configuration G) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The genuine highest-frontier product for an integer upper band and a
shorter crossing target. It is proved by the actual canonical exploration,
its recorded-state conditional law and finite fiber averaging. No product,
selector, locality, path-replacement or conditional-probability hypothesis
is left among the inputs. This is the geometric product before substituting
n=3*s and the exact real-aspect rectangle carriers. -/
theorem upper_band_crossing_reference_product {V : Type*} [Finite V]
    (a : LatticeVertex) (w h n t : ℕ) (hn : n ≤ h) (ht : t ≤ h) (G : SimpleGraph V)
    (f : RectangleVertex a w h ↪ V) (hRG : (rectangleGraph a w h).map f ≤ G)
    (θ : Parameters) (ξ : BoundaryCondition V)
    (hsides : ∀ u v : RectangleVertex a w h,
      (u.val.1=a.1 ∨ u.val.1=a.1+(w : ℤ)) →
      (v.val.1=a.1 ∨ v.val.1=a.1+(w : ℤ)) → ξ.partition.r (f u) (f v)) :
    let Q := DualityExt.rectangleInnerHorizontalCrossingEvent (rectangle_height_subset a w n h hn)
    let S : Set (Configuration G) := {A |
      DualityExt.rectangleConfigurationRestriction (rectangle_upper_band_subset a w h t ht)
        (embeddedConfigurationRestriction _ _ f hRG A) ∈
          rectangleHorizontalCrossingEvent (a.1,a.2+(t : ℤ)) w (h-t)}
    let E : Set (Configuration G) := {A |
      DualityExt.rectangleConfigurationRestriction (rectangle_height_subset a w n h hn)
        (embeddedConfigurationRestriction _ _ f hRG A) ∈ rectangleHorizontalCrossingEvent a w n}
    (measure (rectangleGraph a w h) θ
      (BoundaryCondition.wired {v : RectangleVertex a w h |
        v.val.1=a.1 ∨ v.val.1=a.1+(w : ℤ) ∨ v.val.2=a.2+(h : ℤ)}) Q).toReal *
      (measure G θ ξ S).toReal ≤ (measure G θ ξ E).toReal := by
  let : Fintype (Configuration G) := Fintype.ofFinite _
  let Q := DualityExt.rectangleInnerHorizontalCrossingEvent (rectangle_height_subset a w n h hn)
  let S : Set (Configuration G) := {A |
    DualityExt.rectangleConfigurationRestriction (rectangle_upper_band_subset a w h t ht)
      (embeddedConfigurationRestriction _ _ f hRG A) ∈
        rectangleHorizontalCrossingEvent (a.1,a.2+(t : ℤ)) w (h-t)}
  let E : Set (Configuration G) := {A |
    DualityExt.rectangleConfigurationRestriction (rectangle_height_subset a w n h hn)
      (embeddedConfigurationRestriction _ _ f hRG A) ∈ rectangleHorizontalCrossingEvent a w n}
  let p := law G θ ξ
  let reveal := embeddedFilledTopReveal a w h G f hRG
  let record := FKC.FiniteFK.revealRecordStatistic reveal
  let c := (measure (rectangleGraph a w h) θ
    (BoundaryCondition.wired {v : RectangleVertex a w h |
      v.val.1=a.1 ∨ v.val.1=a.1+(w : ℤ) ∨ v.val.2=a.2+(h : ℤ)}) Q).toReal
  have hp : ∀ A, p A ≠ 0 := fun A => (law_pos G θ ξ A).ne'
  have hstable : ∀ A B, record A=record B → (A ∈ S ↔ B ∈ S) := by
    intro A B hAB
    exact embedded_upper_band_crossing_record_invariant a w h t ht G f hRG A B hAB
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hc1 : c ≤ 1 := MeasureTheory.measureReal_le_one
  have hcond : ∀ y : Set.range record,
      (∃ A, record A=y.val ∧ A ∈ S) →
        c ≤ ((FKC.FiniteFK.finiteStatisticConditionalPMF p hp record y).toMeasure E).toReal := by
    intro y hy
    obtain ⟨A,hAy,hAS⟩ := hy
    have hA : embeddedConfigurationRestriction _ _ f hRG A ∈ rectangleHorizontalCrossingEvent a w h :=
      upper_band_crossing_implies_reference_crossing a w h t ht _ hAS
    let Rout := reveal A
    let F : RemovedConfiguration G Rout := ⟨A ∩ Rout,Finset.inter_subset_right⟩
    have hfiber : {B | record B=y.val}=frozenStateEvent Rout F := by
      calc
        {B | record B=y.val} = {B | record B=record A} := by rw [hAy]
        _ = Exploration.revealRecordEvent reveal A :=
          FKC.FiniteFK.revealRecordStatistic_fiber_eq reveal A
        _ = frozenStateEvent Rout F :=
          Exploration.revealRecordEvent_eq_frozenStateEvent reveal
            (embeddedFilledTopReveal_stable a w h G f hRG) A
    change c ≤ ((p.filter {B | record B=y.val} _).toMeasure E).toReal
    simpa only [hfiber] using
      (reference_crossing_le_outer_frozen_conditional_crossing a w h n hn G f hRG A hA θ ξ hsides)
  have hjoint := FKC.FiniteFK.finiteConditional_event_lower_bound_on_good_fibers
    p hp record S E c hstable hc0 hc1 hcond
  apply hjoint.trans
  apply ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
  exact MeasureTheory.measure_mono Set.inter_subset_right

end
end PottsContinuity.Push
