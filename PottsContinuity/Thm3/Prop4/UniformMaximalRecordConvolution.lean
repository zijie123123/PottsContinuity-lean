module

public import PottsContinuity.Thm3.Prop4.MaximalConvolutionCost

/-!
# One uniform coefficient for all maximal source-record events

The same coefficient works for every scale, cutoff, endpoints and supplied
source record. All model probability, star surgery and convolution-shift
steps are discharged; the source selector geometry remains explicit.
-/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance uniformMaximalRecordEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- The equation-(29)/(30) source estimate has a common positive coefficient,
conditional only on touch and the exact deterministic marked-path record data. -/
theorem uniform_maximal_record_convolution_bound_of_touch_and_geometry
    (q : Set.Ici (1 : ℝ))
    (μ : Measure (PottsContinuity.squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 0 μ)
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (hn : 1 ≤ n) (ε : ℝ) (u v z : LatticeVertex)
    (huB : u ∈ box n) (hvB : v ∈ box n) (hzB : z ∈ box n)
    (huX : u.1 = -(n : ℤ)) (hvX : v.1 = n)
    (trace : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) → Finset LatticeVertex)
    (reveal : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) →
      Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)))
    (hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (T : Set (RSW.StoppingObservationRange reveal))
    (htrace : ∀ C₀, RSW.stoppingObservationMap reveal C₀ ∈ T → ∀ w ∈ trace C₀, w ∈ box n)
    (huT : ∀ C₀, RSW.stoppingObservationMap reveal C₀ ∈ T → u ∈ trace C₀)
    (hvT : ∀ C₀, RSW.stoppingObservationMap reveal C₀ ∈ T → v ∈ trace C₀)
    (hmax : ∀ C₀, RSW.stoppingObservationMap reveal C₀ ∈ T →
      C₀ ∈ maximalTubeExcursionEvent n ε u v trace z)
    (hR : ∀ C₀, RSW.stoppingObservationMap reveal C₀ ∈ T → ∀ e ∈ reveal C₀,
      (∃ w ∈ trace C₀,
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).source.1 = w.1 ∧
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).source.2 ≤ w.2) ∧
      (∃ w ∈ trace C₀,
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).target.1 = w.1 ∧
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).target.2 ≤ w.2))

    (r : ℝ) (hr : 1 ≤ r) (hrn : 2*⌈r⌉₊ ≤ 2*n-2)
    (hfar : 4*r ≤ tubeDistance u v z)

    (hgeometry : ∀ A, RSW.stoppingObservationMap reveal A ∈ T →
      ActualConnected _ A
        ⟨u,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact huB⟩
        ⟨z,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact hzB⟩ ∧
      ActualConnected _ A
        ⟨v,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact hvB⟩
        ⟨z,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact hzB⟩ ∧
      A ∈ sampledRectangleDualArmEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        (sampledStarFacePorts (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
          ⟨z,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact hzB⟩)
        (PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v)
        (fun _ => True)),
      (measure _ (RSW.selfDualParameters q) (BoundaryCondition.free ∅)
        ((RSW.stoppingObservationMap reveal) ⁻¹' T)).toReal ≤
        C*(n : ℝ)^4*splitArmSum (RSW.oneArmProbability μ) r (2*n) := by
  obtain ⟨C,hC,hcost⟩ := exists_maximal_split_coefficient (RSW.selfDualParameters q) μ hμ
  refine ⟨C,hC,?_⟩
  intro n hn ε u v z huB hvB hzB huX hvX trace reveal hstable T htrace huT hvT hmax hR r hr hrn hfar hgeometry
  apply hcost n hn r
  exact maximal_record_split_arm_bound_of_touch_and_geometry q hn ε u v z huB hvB hzB huX hvX
    trace reveal hstable T htrace huT hvT hmax hR hTouch r hr hrn hfar μ hμ hgeometry

end
end PottsContinuity.Thm3.Prop4
