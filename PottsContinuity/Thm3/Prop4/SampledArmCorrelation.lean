module

public import PottsContinuity.Thm3.Prop4.SampledRectangleDualArms
public import PottsContinuity.Thm3.Prop4.FrozenLowerCorrelation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Individual dual arms on the actual sampled rectangle carrier

Both arms use the same original sample. Every step crosses a closed sampled
bond, and their joint event is their literal intersection.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

local instance sampledArmCorrelationEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- A single actual sampled dual arm with prescribed endpoints and support. -/
def sampledRectangleDualArmEvent (a : LatticeVertex) (w h : ℕ)
    (F L : Set LatticeVertex) (P : LatticeVertex → Prop) :
    Set (Configuration (rectangleGraph a w h)) :=
  {A | ∃ f ∈ F, ∃ s ∈ L,
    ∃ p : (PlanarTopology.rectangleSampledClosedDualGraph a w h A).Walk s f,
      ∀ z ∈ p.support, P z}

/-- Closing original sampled bonds preserves each sampled dual arm. -/
theorem isLowerSet_sampledRectangleDualArmEvent (a : LatticeVertex) (w h : ℕ)
    (F L : Set LatticeVertex) (P : LatticeVertex → Prop) :
    IsLowerSet (sampledRectangleDualArmEvent a w h F L P) := by
  rintro A C hCA ⟨f,hf,s,hs,p,hp⟩
  refine ⟨f,hf,s,hs,p.mapLe (sampled_rectangle_closed_dual_antitone a w h hCA),?_⟩
  simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hp

/-- The two sampled arms are witnessed in the same literal original sample. -/
theorem sampledRectangleDualArmsEvent_eq_inter (a : LatticeVertex) (w h : ℕ)
    (F G L U : Set LatticeVertex) (P Q : LatticeVertex → Prop) :
    sampledRectangleDualArmsEvent a w h F G L U P Q =
      sampledRectangleDualArmEvent a w h F L P ∩ sampledRectangleDualArmEvent a w h U G Q := by
  ext A
  constructor
  · rintro ⟨f,hf,g,hg,s,hs,t,ht,minus,plus,hm,hp⟩
    exact ⟨⟨f,hf,s,hs,minus,hm⟩,⟨t,ht,g,hg,plus,hp⟩⟩
  · rintro ⟨⟨f,hf,s,hs,minus,hm⟩,⟨t,ht,g,hg,plus,hp⟩⟩
    exact ⟨f,hf,g,hg,s,hs,t,ht,minus,plus,hm,hp⟩

/-- The genuine normalized frozen fiber correlates the two actual sampled
arms, retaining a closed original sampled bond at every step. -/
theorem frozen_fiber_sampled_dual_arms_probability_ge_product (θ : Parameters)
    (a : LatticeVertex) (w h : ℕ) (ξ : BoundaryCondition (RectangleVertex a w h))
    (R : Configuration (rectangleGraph a w h)) (B : RemovedConfiguration (rectangleGraph a w h) R)
    (F G L U : Set LatticeVertex) (P Q : LatticeVertex → Prop) :
    ((frozenFiberLaw θ ξ R B).toMeasure
      {A | A.val ∪ B.val ∈ sampledRectangleDualArmEvent a w h F L P}).toReal *
    ((frozenFiberLaw θ ξ R B).toMeasure
      {A | A.val ∪ B.val ∈ sampledRectangleDualArmEvent a w h U G Q}).toReal ≤
    ((frozenFiberLaw θ ξ R B).toMeasure
      {A | A.val ∪ B.val ∈ sampledRectangleDualArmsEvent a w h F G L U P Q}).toReal := by
  rw [sampledRectangleDualArmsEvent_eq_inter]
  exact frozen_fiber_lower_events_correlation (PD.FK.latticeRectangle a w h) θ ξ R B _ _
    (isLowerSet_sampledRectangleDualArmEvent a w h F L P)
    (isLowerSet_sampledRectangleDualArmEvent a w h U G Q)

end
end PottsContinuity.Thm3.Prop4
