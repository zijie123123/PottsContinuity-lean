module

public import PottsContinuity.Thm3.Prop4.SafeReferenceArmProbability
public import PottsContinuity.Thm3.Prop4.TubeConnectorHeights

/-!
# Both actual stopped reference roots have complementary-arc arms

A root already on its correct physical arc has a length-zero sampled arm.
Every other stopped root is at a safe affine height and uses the proved
cropped touch comparison. Both cases use the same restored primal fiber.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance stoppedArmProbabilityPrimalEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Actual sampled complementary-arc arm probability under the normalized
all-open tube reference fiber, for every radius, mark pair and central root. -/
def tubeReferenceArmProbability (θ : Parameters) (n : ℕ) (r : ℝ) (u v : LatticeVertex)
    (c : ℤ) (reflected : Bool) : ℝ :=
  ((frozenFiberLaw θ (BoundaryCondition.free ∅) (rectangleTubeRevealedEdges n r u v)
    ⟨rectangleTubeRevealedEdges n r u v,Finset.Subset.refl _⟩).toMeasure
      {A | A.val ∪ rectangleTubeRevealedEdges n r u v ∈
        sampledRectangleDualArmEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) {(0,c)}
          (if reflected then PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v else
            PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v) (fun _ => True)}).toReal

/-- A root already on its prescribed arc has its actual length-zero arm
under every original reference sample, so the reference probability is one. -/
theorem tubeReferenceArmProbability_eq_one_of_root_mem_arc (θ : Parameters) (n : ℕ) (r : ℝ)
    (u v : LatticeVertex) (c : ℤ) (reflected : Bool)
    (hroot : (0,c) ∈ if reflected then
      PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v else
      PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v) :
    tubeReferenceArmProbability θ n r u v c reflected = 1 := by
  unfold tubeReferenceArmProbability
  have hE : {A : RemainingConfiguration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
      (rectangleTubeRevealedEdges n r u v) |
      A.val ∪ rectangleTubeRevealedEdges n r u v ∈ sampledRectangleDualArmEvent
        (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) {(0,c)}
        (if reflected then PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v else
          PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v) (fun _ => True)} = Set.univ := by
    ext A
    constructor
    · exact fun _ => Set.mem_univ _
    · intro _
      exact ⟨(0,c),rfl,(0,c),hroot,.nil,fun _ _ => True.intro⟩
  rw [hE]
  simp

/-- Either a correct boundary root or a safe affine root has the same
explicit lower bound, with only Lemma 6 (the full touch bound) as a hypothesis. -/
theorem reference_arm_probability_lower_of_touch_and_safe_or_arc (q : Set.Ici (1 : ℝ))
    {n : ℕ} (hn : 1 ≤ n) (r : ℝ) (hr : 1 ≤ r) (u v : LatticeVertex)
    (huBox : u ∈ box n) (hvBox : v ∈ box n) (huX : u.1 = -(n : ℤ)) (hvX : v.1 = n)
    (t b : ℝ) (ht : |t| ≤ 1) (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (c : ℤ) (hcPhys : -(n : ℤ)-1 ≤ c ∧ c ≤ n) (reflected : Bool)
    (hroot : ((0,c) ∈ if reflected then
      PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v else
      PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v) ∨
      (if reflected then (c : ℝ) ≤ b-2*r else b+2*r ≤ (c : ℝ)))
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    1/(20*((4*n+2 : ℕ) : ℝ)^2*((4*n+2 : ℕ) : ℝ)^2) ≤
      tubeReferenceArmProbability (RSW.selfDualParameters q) n r u v c reflected := by
  rcases hroot with hroot | hsafe
  · rw [tubeReferenceArmProbability_eq_one_of_root_mem_arc _ _ _ _ _ _ _ hroot]
    have hM : (1 : ℝ) ≤ ((4*n+2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 4*n+2 by omega)
    have hM2 : (1 : ℝ) ≤ ((4*n+2 : ℕ) : ℝ)^2 := one_le_pow₀ hM
    have hden : (1 : ℝ) ≤ 20*((4*n+2 : ℕ) : ℝ)^2*((4*n+2 : ℕ) : ℝ)^2 := by
      calc
        (1 : ℝ) ≤ 20 := by norm_num
        _ ≤ 20*((4*n+2 : ℕ) : ℝ)^2 := le_mul_of_one_le_right (by norm_num) hM2
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hM2
    exact (div_le_one (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hden)).mpr hden
  · exact safe_reference_sampled_arm_probability_lower_of_touch q hn r hr u v huBox hvBox huX hvX
      t b ht hu hv c hcPhys reflected hsafe hTouch

/-- The two actual stopped roots of the literal nonempty central cut each
have the polynomial reference arm bound, including every boundary-stop case. -/
theorem stopped_reference_arm_probabilities_lower_of_touch (q : Set.Ici (1 : ℝ))
    {n : ℕ} (hn : 1 ≤ n) (r : ℝ) (hr : 2 ≤ r) (u v : LatticeVertex)
    (huBox : u ∈ box n) (hvBox : v ∈ box n) (huX : u.1 = -(n : ℤ)) (hvX : v.1 = n)
    (t b : ℝ) (ht : |t| ≤ 1) (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    ∃ lo hi : ℤ, lo ≤ hi ∧ radiusTubeCutRows n r u v 0 = Finset.Icc lo hi ∧
      (1/(20*((4*n+2 : ℕ) : ℝ)^2*((4*n+2 : ℕ) : ℝ)^2) ≤
        tubeReferenceArmProbability (RSW.selfDualParameters q) n r u v
          (max (-(n : ℤ)-1) ⌊b-2*r⌋) true) ∧
      (1/(20*((4*n+2 : ℕ) : ℝ)^2*((4*n+2 : ℕ) : ℝ)^2) ≤
        tubeReferenceArmProbability (RSW.selfDualParameters q) n r u v
          (min (n : ℤ) ⌈b+2*r⌉) false) := by
  obtain ⟨lo,hi,hlohi,hrows,_⟩ := rectangle_central_tube_cut_rows hn r hr u v huBox hvBox huX hvX
  have hL := central_cut_lower_connector_stopped hn r u v t b ht hu hv lo hi hlohi hrows
  have hU := central_cut_upper_connector_stopped hn r u v t b ht hu hv lo hi hlohi hrows
  have hbox (y : ℤ) (hy : y ∈ Finset.Icc lo hi) : -(n : ℤ) ≤ y ∧ y ≤ n := by
    have hm : y ∈ radiusTubeCutRows n r u v 0 := by rwa [hrows]
    exact Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
  have hloBox := hbox lo (Finset.mem_Icc.mpr ⟨le_rfl,hlohi⟩)
  have hhiBox := hbox hi (Finset.mem_Icc.mpr ⟨hlohi,le_rfl⟩)
  refine ⟨lo,hi,hlohi,hrows,?_,?_⟩
  · exact reference_arm_probability_lower_of_touch_and_safe_or_arc q hn r (by linarith only [hr])
      u v huBox hvBox huX hvX t b ht hu hv _ (by omega) true hL.2.2.2 hTouch
  · exact reference_arm_probability_lower_of_touch_and_safe_or_arc q hn r (by linarith only [hr])
      u v huBox hvBox huX hvX t b ht hu hv _ (by omega) false hU.2.2.2 hTouch

end
end PottsContinuity.Thm3.Prop4
