module

public import PottsContinuity.Thm3.Prop4.RecordedExcursionConvolution

/-!
# Primitive recorded-walk data for the excursion branch

This predicate lists only the source reveal, its observed trace, and actual
recorded primal and sampled-dual walks. It contains no probability inequality.
-/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance excursionWitnessEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Literal source-record data sufficient for the excursion branch, for every
actual sample on its carrier. No extremal-path selector is constructed here. -/
def HasRecordedExcursionWitnesses (n : ℕ) (ε : ℝ) (u v : LatticeVertex)
    (huB : u ∈ box n) (hvB : v ∈ box n)
    (trace : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) → Finset LatticeVertex) : Prop :=
  ∃ reveal : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) →
      Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)),
    (∀ A B, B ∩ reveal A = A ∩ reveal A → reveal B = reveal A) ∧
    (∀ A B, RSW.stoppingObservationMap reveal A = RSW.stoppingObservationMap reveal B →
      trace A = trace B) ∧
    (∀ A, A ∈ tubeExcursionEvent n ε u v trace →
      ∃ p : (openGraph _ (Exploration.revealRecordConfiguration reveal A).val).Walk
        ⟨u,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact huB⟩
        ⟨v,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact hvB⟩,
        trace A = (p.support.map Subtype.val).toFinset) ∧
    (∀ z ∈ inductionTubeAbove n ε u v, ∀ A, A ∈ maximalTubeExcursionEvent n ε u v trace z → ∀ e ∈ reveal A,
      (∃ w ∈ trace A,
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).source.1 = w.1 ∧
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).source.2 ≤ w.2) ∧
      (∃ w ∈ trace A,
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).target.1 = w.1 ∧
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).target.2 ≤ w.2)) ∧
    (∀ z (hz : z ∈ inductionTubeAbove n ε u v), ∀ A,
      A ∈ maximalTubeExcursionEvent n ε u v trace z →
      ∃ f ∈ sampledStarFacePorts (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
          ⟨z,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact (Finset.mem_filter.mp hz).1⟩,
      ∃ s ∈ PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v,
      Nonempty ((recordedSampledClosedDualGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        (reveal A) (Exploration.revealRecordConfiguration reveal A).val).Walk s f))

/-- Uniform convolution estimate from the primitive recorded source data. -/
theorem excursion_convolution_of_touch_and_source_witnesses
    (q : Set.Ici (1 : ℝ)) (μ : Measure (PottsContinuity.squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 0 μ)
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (_hn : 1 ≤ n) (ε r : ℝ), 1 ≤ r →
    2*⌈r⌉₊ ≤ 2*n-2 → 4*r ≤ (n : ℝ)^ε →
    ∀ (u v : LatticeVertex) (huB : u ∈ box n) (hvB : v ∈ box n),
    u.1 = -(n : ℤ) → v.1 = n →
    ∀ (trace : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) → Finset LatticeVertex),
    HasRecordedExcursionWitnesses n ε u v huB hvB trace →
      (measure _ (RSW.selfDualParameters q) (BoundaryCondition.free ∅)
        (tubeExcursionEvent n ε u v trace)).toReal ≤
        C*(n : ℝ)^6*splitArmSum (RSW.oneArmProbability μ) r (2*n) := by
  obtain ⟨C,hC,hbound⟩ := uniform_excursion_convolution_bound_of_touch_and_recorded_witnesses q μ hμ hTouch
  refine ⟨C,hC,?_⟩
  intro n hn ε r hr hrn hscale u v huB hvB huX hvX trace hwitness
  obtain ⟨reveal,hstable,hobserved,hpath,hR,hdual⟩ := hwitness
  exact hbound hn ε r hr hrn hscale u v huB hvB huX hvX trace reveal hstable hobserved hpath hR hdual

end
end PottsContinuity.Thm3.Prop4
