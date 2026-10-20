module

public import PottsContinuity.Thm3.Prop4.ObservedExcursionConvolution
public import PottsContinuity.Thm3.Prop4.RecordedSampledDualGraph
public import PottsContinuity.Thm3.Prop4.RecordedWalkConnections

/-!
# The actual excursion bound from recorded primal and dual walks

The trace is the full support of an actual recorded open path. The lower arm
uses only sampled original bonds fixed closed by that same observation.
-/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance recordedExcursionEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Recorded open path support and recorded closed-dual witnesses supply
both primal arms, the lower sampled arm, and all trace endpoint/box properties. -/
theorem uniform_excursion_convolution_bound_of_touch_and_recorded_witnesses
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
    (∀ A, A ∈ tubeExcursionEvent n ε u v trace →
      ∃ p : (openGraph _ (Exploration.revealRecordConfiguration reveal A).val).Walk
        ⟨u,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact huB⟩
        ⟨v,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact hvB⟩,
        trace A = (p.support.map Subtype.val).toFinset) →
    (∀ z ∈ inductionTubeAbove n ε u v, ∀ A, A ∈ maximalTubeExcursionEvent n ε u v trace z → ∀ e ∈ reveal A,
      (∃ w ∈ trace A,
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).source.1 = w.1 ∧
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).source.2 ≤ w.2) ∧
      (∃ w ∈ trace A,
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).target.1 = w.1 ∧
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).target.2 ≤ w.2)) →
    (∀ z (hz : z ∈ inductionTubeAbove n ε u v), ∀ A,
      A ∈ maximalTubeExcursionEvent n ε u v trace z →
      ∃ f ∈ sampledStarFacePorts (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
          ⟨z,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact (Finset.mem_filter.mp hz).1⟩,
      ∃ s ∈ PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v,
      Nonempty ((recordedSampledClosedDualGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        (reveal A) (Exploration.revealRecordConfiguration reveal A).val).Walk s f)) →
      (measure _ (RSW.selfDualParameters q) (BoundaryCondition.free ∅)
        (tubeExcursionEvent n ε u v trace)).toReal ≤
        C*(n : ℝ)^6*splitArmSum (RSW.oneArmProbability μ) r (2*n) := by
  classical
  obtain ⟨C,hC,hbound⟩ := uniform_excursion_convolution_bound_of_touch_and_observed_trace q μ hμ hTouch
  refine ⟨C,hC,?_⟩
  intro n hn ε r hr hrn hscale u v huB hvB huX hvX trace reveal hstable hobserved
    hpaths hR hdual
  have hex (A) (z) (hz : A ∈ maximalTubeExcursionEvent n ε u v trace z) :
      A ∈ tubeExcursionEvent n ε u v trace := ⟨z,hz.1,hz.2.1⟩
  apply hbound hn ε r hr hrn hscale u v huB hvB huX hvX trace reveal hstable hobserved
  · intro z hz A hA w hw
    obtain ⟨p,hp⟩ := hpaths A (hex A z hA)
    rw [hp,List.mem_toFinset,List.mem_map] at hw
    obtain ⟨x,hx,rfl⟩ := hw
    have hxB := x.property
    simpa only [PlanarTopology.latticeRectangle_neg_eq_box,PD.box,box] using hxB
  · intro z hz A hA
    obtain ⟨p,hp⟩ := hpaths A (hex A z hA)
    rw [hp,List.mem_toFinset,List.mem_map]
    exact ⟨_,p.start_mem_support,rfl⟩
  · intro z hz A hA
    obtain ⟨p,hp⟩ := hpaths A (hex A z hA)
    rw [hp,List.mem_toFinset,List.mem_map]
    exact ⟨_,p.end_mem_support,rfl⟩
  · exact hR
  · intro z hz A hA
    obtain ⟨p,hp⟩ := hpaths A (hex A z hA)
    have hztrace := hA.2.1
    rw [hp,List.mem_toFinset,List.mem_map] at hztrace
    obtain ⟨x,hx,hxz⟩ := hztrace
    have hconn := actual_connections_of_recorded_walk _ (reveal A)
      (Exploration.revealRecordConfiguration reveal A).val A rfl p hx
    have hxz' : x = ⟨z,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact (Finset.mem_filter.mp hz).1⟩ :=
      Subtype.ext hxz
    rw [hxz'] at hconn
    refine ⟨hconn.1,hconn.2,?_⟩
    obtain ⟨f,hf,s,hs,⟨d⟩⟩ := hdual z hz A hA
    exact sampled_dual_arm_of_recorded_walk (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
      (reveal A) (Exploration.revealRecordConfiguration reveal A).val A (by ext e; simp [Exploration.revealRecordConfiguration])
      _ _ (fun _ => True) hf hs d (fun _ _ => trivial)

end
end PottsContinuity.Thm3.Prop4
