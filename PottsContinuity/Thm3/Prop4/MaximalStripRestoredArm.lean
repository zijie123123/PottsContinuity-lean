module

public import PottsContinuity.Thm3.Prop4.MaximalStripReferenceExit
public import PottsContinuity.Thm3.Prop4.FiniteDualSampledWalkMap
public import PottsContinuity.Thm3.Prop4.SampledArmCorrelation
public import PottsContinuity.Thm3.Prop4.FrozenLowerMonotonicity

/-!
# The maximal-root arm in every original conditional sample

Exact dual transport gives the arm in the all-open reference fiber. Lower
event monotonicity then gives the same bound for every prescribed revealed
state. All steps remain actual sampled closed-original bonds.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance maximalStripRestoredEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- The true dual exit maps to a sampled arm of the same restored original
state, with its entire support above the actual supporting line. -/
theorem maximal_reference_exit_gives_restored_arm (a : LatticeVertex) (w h : ℕ)
    (R : Configuration (rectangleGraph a w h)) (A : RemainingConfiguration (rectangleGraph a w h) R)
    (t : ℝ) (z : RectangleDualVertex a w h)
    (hA : frozenReferenceDualSample a w h R A ∈ pathConfinedTargetEvent _
      {y | tiltedHeight t z.val ≤ tiltedHeight t y.val}
      {y | y.val ∈ rectangleDualBoundary a w h} z) :
    A.val ∪ R ∈ sampledRectangleDualArmEvent a w h {z.val}
      (rectangleDualBoundary a w h : Set LatticeVertex)
      (fun y => tiltedHeight t z.val ≤ tiltedHeight t y) := by
  obtain ⟨y,hy,p,hp⟩ := hA
  obtain ⟨q,hq⟩ := frozenReferenceDualSample_walk_sampled a w h R A p
  refine ⟨z.val,rfl,y.val,hy,q.reverse,?_⟩
  intro v hv
  have hvq : v ∈ q.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hv
  rw [hq] at hvq
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hvq
  exact hp b hb

/-- The maximal-root exit lower bound holds in every actual original fiber;
no correlation with the source record or independence assumption is used. -/
theorem maximal_restored_arm_lower_of_touch (q : Set.Ici (1 : ℝ))
    (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) (z : LatticeVertex)
    (hz : z ∈ rectangleDualExpanded (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (R : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)))
    (B : RemovedConfiguration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) R)
    (hR : ∀ e ∈ R,
      tiltedHeight t (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).source ≤ tiltedHeight t z ∧
      tiltedHeight t (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).target ≤ tiltedHeight t z)
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    ((frozenFiberLaw (RSW.selfDualParameters q) (BoundaryCondition.free ∅) R B).toMeasure
      {A | A.val ∪ B.val ∈ sampledRectangleDualArmEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) {z}
        (rectangleDualBoundary (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) : Set LatticeVertex)
        (fun y => tiltedHeight t z ≤ tiltedHeight t y)}).toReal ≥
      1/(20*((4*n+4 : ℕ) : ℝ)^2*((4*n+4 : ℕ) : ℝ)^2) := by
  let a : LatticeVertex := (-(n : ℤ),-(n : ℤ))
  let E := sampledRectangleDualArmEvent a (2*n) (2*n) {z}
    (rectangleDualBoundary a (2*n) (2*n) : Set LatticeVertex)
    (fun y => tiltedHeight t z ≤ tiltedHeight t y)
  let F := pathConfinedTargetEvent
    (edgeRestriction (rectangleDualGraph a (2*n) (2*n)) (rectangleCrossedEdges a (2*n) (2*n) R))
    {y | tiltedHeight t z ≤ tiltedHeight t y.val}
    {y | y.val ∈ rectangleDualBoundary a (2*n) (2*n)} ⟨z,hz⟩
  have hLower := maximal_strip_reference_exit_lower_of_touch q n t ht z hz R hR hTouch
  rw [← selfDual_frozenReferenceDualSample_probability q a (2*n) (2*n) R F] at hLower
  have hRef : 1/(20*((4*n+4 : ℕ) : ℝ)^2*((4*n+4 : ℕ) : ℝ)^2) ≤
      ((frozenFiberLaw (RSW.selfDualParameters q) (BoundaryCondition.free ∅) R
        ⟨R,Finset.Subset.refl R⟩).toMeasure {A | A.val ∪ R ∈ E}).toReal :=
    hLower.trans (measureReal_mono (fun A hA =>
      maximal_reference_exit_gives_restored_arm a (2*n) (2*n) R A t ⟨z,hz⟩ hA) (measure_ne_top _ _))
  exact hRef.trans (frozen_fiber_lower_event_ge_all_open (PD.FK.latticeRectangle a (2*n) (2*n))
    (RSW.selfDualParameters q) (BoundaryCondition.free ∅) R B E
    (isLowerSet_sampledRectangleDualArmEvent a (2*n) (2*n) _ _ _))

end
end PottsContinuity.Thm3.Prop4
