module

public import PottsContinuity.Thm3.Prop4.MaximalRecordUpperArmBound
public import PottsContinuity.Thm3.Prop4.RectangleComplementaryStarConvolution

/-!
# The maximal source-record split-arm estimate

The upper-arm probability, sampled complementary star screen, surgery and
free-cluster convolution are proved. The remaining selector data describe
actual retained primal connections and a lower complementary sampled arm.
-/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance maximalRecordSplitEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- The source-record mass has the exact split convolution once its actual
lowest-path record and deterministic lower sampled-arm geometry are supplied. -/
theorem maximal_record_split_arm_bound_of_touch_and_geometry
    (q : Set.Ici (1 : ℝ)) {n : ℕ} (hn : 1 ≤ n) (ε : ℝ) (u v z : LatticeVertex)
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
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s)
    (r : ℝ) (hr : 1 ≤ r) (hrn : 2*⌈r⌉₊ ≤ 2*n-2)
    (hfar : 4*r ≤ tubeDistance u v z)
    (μ : Measure (PottsContinuity.squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 0 μ)
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
        (fun _ => True)) :
    (1-edgeParameter (RSW.selfDualParameters q))^4 *
      (1/(20*((4*n+4 : ℕ) : ℝ)^2*((4*n+4 : ℕ) : ℝ)^2)) *
      (measure _ (RSW.selfDualParameters q) (BoundaryCondition.free ∅)
        ((RSW.stoppingObservationMap reveal) ⁻¹' T)).toReal ≤
      splitArmSum (RSW.oneArmProbability μ) r (2*n-2) := by
  let zb : (box n : Set LatticeVertex) := ⟨z,hzB⟩
  let ur := boxTubeRectangleIso n ⟨u,huB⟩
  let vr := boxTubeRectangleIso n ⟨v,hvB⟩
  let zr := boxTubeRectangleIso n zb
  let E := sampledRectangleDualArmEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
    (sampledStarFacePorts (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) zr)
    (PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v) (fun _ => True)
  let S := (RSW.stoppingObservationMap reveal) ⁻¹' T
  have hBound := maximal_record_upper_arm_joint_lower_of_touch_and_column_reveal q hn ε u v z
    huB hvB hzB huX hvX trace reveal hstable T htrace huT hvT hmax hR hTouch
  have hSplit : (1-edgeParameter (RSW.selfDualParameters q))^4 *
      (measure _ (RSW.selfDualParameters q) (BoundaryCondition.free ∅) (E ∩ S)).toReal ≤
      splitArmSum (RSW.oneArmProbability μ) r (2*n-2) := by
    apply rectangle_split_probability_le_arm_sum_of_sampled_complementary_arms
      (RSW.selfDualParameters q) μ hμ n r hn hr hrn ⟨u,huB⟩ ⟨v,hvB⟩ zb huX hvX hfar (E ∩ S)
    intro A hA
    obtain ⟨huz,hvz,f,hf,s,hs,minus,_⟩ := hgeometry A hA.2
    obtain ⟨g,hg,t,ht,plus,_⟩ := hA.1
    exact ⟨huz,hvz,f,hf,g,hg,s,hs,t,ht,minus,plus.reverse,fun _ _ => True.intro,fun _ _ => True.intro⟩
  have hc : 0 ≤ (1-edgeParameter (RSW.selfDualParameters q))^4 :=
    pow_nonneg (one_sub_edgeParameter_pos _).le _
  calc
    _ = (1-edgeParameter (RSW.selfDualParameters q))^4 *
        ((1/(20*((4*n+4 : ℕ) : ℝ)^2*((4*n+4 : ℕ) : ℝ)^2)) *
          (measure _ (RSW.selfDualParameters q) (BoundaryCondition.free ∅) S).toReal) := by ring
    _ ≤ (1-edgeParameter (RSW.selfDualParameters q))^4 *
        (measure _ (RSW.selfDualParameters q) (BoundaryCondition.free ∅) (E ∩ S)).toReal :=
      mul_le_mul_of_nonneg_left hBound hc
    _ ≤ _ := hSplit

end
end PottsContinuity.Thm3.Prop4
