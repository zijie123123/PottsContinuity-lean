module

public import PottsContinuity.Thm3.Prop4.StoppedReferenceArmsProduct
public import PottsContinuity.Thm3.Prop4.TubeConnectorArmProbability

/-!
# Actual complementary-arc reference arms at the original cut roots

The stopped touch arms and the retained connector energy are combined in
one normalized restored fiber. Only the corrected touch theorem is an input.
-/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance cutTouchOriginalEq (n : ℕ) :
    DecidableEq (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet := Classical.decEq _

/-- Both source cut-root arms have the explicit squared touch lower bound
with the additional proved retained-connector exponential cost. -/
theorem cut_reference_arms_lower_of_touch (q : Set.Ici (1 : ℝ))
    {n : ℕ} (hn : 1 ≤ n) (r : ℝ) (hr : 2 ≤ r) (u v : LatticeVertex)
    (huBox : u ∈ box n) (hvBox : v ∈ box n) (huX : u.1 = -(n : ℤ)) (hvX : v.1 = n)
    (t b : ℝ) (ht : |t| ≤ 1) (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    ∃ lo hi : ℤ, lo ≤ hi ∧ radiusTubeCutRows n r u v 0 = Finset.Icc lo hi ∧
      Real.exp (-tubeClosingCoefficient (RSW.selfDualParameters q)*r) *
      (1/(20*((4*n+2 : ℕ) : ℝ)^2*((4*n+2 : ℕ) : ℝ)^2))^2 ≤
        ((frozenFiberLaw (RSW.selfDualParameters q) (BoundaryCondition.free ∅)
          (rectangleTubeRevealedEdges n r u v) ⟨rectangleTubeRevealedEdges n r u v,Finset.Subset.refl _⟩).toMeasure
          {A | A.val ∪ rectangleTubeRevealedEdges n r u v ∈
            sampledRectangleDualArmsEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
              {(0,lo-1)} {(0,hi)}
              (PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v)
              (PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v)
              (fun _ => True) (fun _ => True)}).toReal := by
  obtain ⟨lo,hi,hlohi,hrows,hstop⟩ := stopped_reference_arms_product_lower_of_touch q hn r hr
    u v huBox hvBox huX hvX t b ht hu hv hTouch
  refine ⟨lo,hi,hlohi,hrows,?_⟩
  have hmove := tube_reference_cut_arms_ge_stopped (RSW.selfDualParameters q) hn r
    (by linarith only [hr]) u v t b ht hu hv lo hi hlohi hrows
    (PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v)
    (PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v)
  exact (mul_le_mul_of_nonneg_left hstop (Real.exp_pos _).le).trans hmove

end
end PottsContinuity.Thm3.Prop4
