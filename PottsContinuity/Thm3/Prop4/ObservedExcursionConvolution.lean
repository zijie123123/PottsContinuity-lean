module

public import PottsContinuity.Thm3.Prop4.ObservedMaximalExcursion
public import PottsContinuity.Thm3.Prop4.UniformExcursionConvolution

/-!
# The actual trace excursion bound without a record-cover input

The complete observation determines the trace. Its maximal-event images give
exact selected records and automatically cover the actual excursion event.
-/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance observedExcursionEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Touch and actual observed-trace geometry imply the full excursion
convolution. No selected-record family or event-cover assumption is needed. -/
theorem uniform_excursion_convolution_bound_of_touch_and_observed_trace
    (q : Set.Ici (1 : ℝ)) (μ : Measure (PottsContinuity.squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 0 μ)
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (hn : 1 ≤ n) (ε r : ℝ), 1 ≤ r →
    2*⌈r⌉₊ ≤ 2*n-2 → 4*r ≤ (n : ℝ)^ε →
    ∀ (u v : LatticeVertex) (huB : u ∈ box n) (hvB : v ∈ box n),
    u.1 = -(n : ℤ) → v.1 = n →
    ∀ (trace : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) → Finset LatticeVertex)
    (reveal : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) →
      Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)))
    (hstable : ∀ A B, B ∩ reveal A = A ∩ reveal A → reveal B = reveal A)
    (hobserved : ∀ A B, RSW.stoppingObservationMap reveal A = RSW.stoppingObservationMap reveal B →
      trace A = trace B),
    (∀ z ∈ inductionTubeAbove n ε u v, ∀ A, A ∈ maximalTubeExcursionEvent n ε u v trace z →
      ∀ w ∈ trace A, w ∈ box n) →
    (∀ z ∈ inductionTubeAbove n ε u v, ∀ A, A ∈ maximalTubeExcursionEvent n ε u v trace z → u ∈ trace A) →
    (∀ z ∈ inductionTubeAbove n ε u v, ∀ A, A ∈ maximalTubeExcursionEvent n ε u v trace z → v ∈ trace A) →
    (∀ z ∈ inductionTubeAbove n ε u v, ∀ A, A ∈ maximalTubeExcursionEvent n ε u v trace z → ∀ e ∈ reveal A,
      (∃ w ∈ trace A,
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).source.1 = w.1 ∧
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).source.2 ≤ w.2) ∧
      (∃ w ∈ trace A,
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).target.1 = w.1 ∧
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).target.2 ≤ w.2)) →
    (∀ z (hz : z ∈ inductionTubeAbove n ε u v), ∀ A, A ∈ maximalTubeExcursionEvent n ε u v trace z →
      ActualConnected _ A
        ⟨u,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact huB⟩
        ⟨z,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact (Finset.mem_filter.mp hz).1⟩ ∧
      ActualConnected _ A
        ⟨v,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact hvB⟩
        ⟨z,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact (Finset.mem_filter.mp hz).1⟩ ∧
      A ∈ sampledRectangleDualArmEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        (sampledStarFacePorts (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
          ⟨z,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact (Finset.mem_filter.mp hz).1⟩)
        (PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v)
        (fun _ => True)) →
      (measure _ (RSW.selfDualParameters q) (BoundaryCondition.free ∅)
        (tubeExcursionEvent n ε u v trace)).toReal ≤
        C*(n : ℝ)^6*splitArmSum (RSW.oneArmProbability μ) r (2*n) := by
  obtain ⟨C,hC,hbound⟩ := uniform_excursion_convolution_bound_of_touch_and_geometry q μ hμ hTouch
  refine ⟨C,hC,?_⟩
  intro n hn ε r hr hrn hscale u v huB hvB huX hvX trace reveal hstable hobserved
    htrace huT hvT hR hgeometry
  let T := maximalExcursionObservations n ε u v trace reveal
  have hmem (z : LatticeVertex) (A : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))) :
      RSW.stoppingObservationMap reveal A ∈ T z ↔ A ∈ maximalTubeExcursionEvent n ε u v trace z :=
    mem_maximalExcursionObservations_iff n ε u v z trace reveal hobserved A
  apply hbound hn ε r hr hrn hscale u v huB hvB huX hvX trace reveal hstable T
  · intro z hz A hA
    exact htrace z hz A ((hmem z A).mp hA)
  · intro z hz A hA
    exact huT z hz A ((hmem z A).mp hA)
  · intro z hz A hA
    exact hvT z hz A ((hmem z A).mp hA)
  · intro z hz A hA
    exact (hmem z A).mp hA
  · intro z hz A hA
    exact hR z hz A ((hmem z A).mp hA)
  · intro z hz A hA
    exact hgeometry z hz A ((hmem z A).mp hA)
  · exact (tubeExcursion_eq_union_observed_maximal n ε u v trace reveal hobserved).subset

end
end PottsContinuity.Thm3.Prop4
