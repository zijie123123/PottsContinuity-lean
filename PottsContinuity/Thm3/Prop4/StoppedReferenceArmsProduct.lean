module

public import PottsContinuity.Thm3.Prop4.StoppedReferenceArmProbability

/-!
# The two actual stopped reference arms occur in the same restored sample

The exact normalized frozen fiber has proved positive correlation for lower
events. Reverse the upper arm's orientation and apply that correlation to
obtain the squared touch lower bound, without any independence premise.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance stoppedArmsProductPrimalEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Reversing an actual sampled dual arm exchanges its two endpoint sets
and retains every vertex constraint on its original support. -/
theorem sampledRectangleDualArmEvent_symm (a : LatticeVertex) (w h : ℕ)
    (F L : Set LatticeVertex) (P : LatticeVertex → Prop) :
    sampledRectangleDualArmEvent a w h F L P = sampledRectangleDualArmEvent a w h L F P := by
  ext A
  constructor <;> rintro ⟨f,hf,s,hs,p,hp⟩ <;> refine ⟨s,hs,f,hf,p.reverse,?_⟩
  all_goals
    intro z hz
    rw [SimpleGraph.Walk.support_reverse,List.mem_reverse] at hz
    exact hp z hz

/-- Both complementary-arc arms at the actual stopped roots have the squared
explicit lower bound under one literal all-open primal reference fiber. -/
theorem stopped_reference_arms_product_lower_of_touch (q : Set.Ici (1 : ℝ))
    {n : ℕ} (hn : 1 ≤ n) (r : ℝ) (hr : 2 ≤ r) (u v : LatticeVertex)
    (huBox : u ∈ box n) (hvBox : v ∈ box n) (huX : u.1 = -(n : ℤ)) (hvX : v.1 = n)
    (t b : ℝ) (ht : |t| ≤ 1) (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    ∃ lo hi : ℤ, lo ≤ hi ∧ radiusTubeCutRows n r u v 0 = Finset.Icc lo hi ∧
      (1/(20*((4*n+2 : ℕ) : ℝ)^2*((4*n+2 : ℕ) : ℝ)^2))^2 ≤
        ((frozenFiberLaw (RSW.selfDualParameters q) (BoundaryCondition.free ∅)
          (rectangleTubeRevealedEdges n r u v) ⟨rectangleTubeRevealedEdges n r u v,Finset.Subset.refl _⟩).toMeasure
          {A | A.val ∪ rectangleTubeRevealedEdges n r u v ∈
            sampledRectangleDualArmsEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
              {(0,max (-(n : ℤ)-1) ⌊b-2*r⌋)} {(0,min (n : ℤ) ⌈b+2*r⌉)}
              (PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v)
              (PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v)
              (fun _ => True) (fun _ => True)}).toReal := by
  obtain ⟨lo,hi,hlohi,hrows,hL,hU⟩ := stopped_reference_arm_probabilities_lower_of_touch q hn r hr
    u v huBox hvBox huX hvX t b ht hu hv hTouch
  refine ⟨lo,hi,hlohi,hrows,?_⟩
  have hcorr := frozen_fiber_sampled_dual_arms_probability_ge_product (RSW.selfDualParameters q)
    (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (BoundaryCondition.free ∅)
    (rectangleTubeRevealedEdges n r u v) ⟨rectangleTubeRevealedEdges n r u v,Finset.Subset.refl _⟩
    {(0,max (-(n : ℤ)-1) ⌊b-2*r⌋)} {(0,min (n : ℤ) ⌈b+2*r⌉)}
    (PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v)
    (PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v)
    (fun _ => True) (fun _ => True)
  rw [sampledRectangleDualArmEvent_symm _ _ _
    (PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v)
    {(0,min (n : ℤ) ⌈b+2*r⌉)} (fun _ => True)] at hcorr
  rw [pow_two]
  exact (mul_le_mul hL hU (by positivity) ENNReal.toReal_nonneg).trans hcorr

end
end PottsContinuity.Thm3.Prop4
