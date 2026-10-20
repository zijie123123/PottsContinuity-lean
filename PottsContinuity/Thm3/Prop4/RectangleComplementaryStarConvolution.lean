module

public import PottsContinuity.Thm3.Prop4.BoxComplementaryStarArms
public import PottsContinuity.Thm3.RSW.FiniteIso

/-!
# The sampled complementary-star convolution in the literal rectangle law

The free law is transported by the coordinate identity. Both endpoint
connections and all dual arms remain in the same original finite sample.
-/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance rectangleStarConvolutionSourceEq (n : ℕ) :
    DecidableEq (squareLattice.induce (box n : Set LatticeVertex)).edgeSet := Classical.decEq _
local instance rectangleStarConvolutionTargetEq (n : ℕ) :
    DecidableEq (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet := Classical.decEq _

/-- The actual sampled complementary arms give the source convolution under
the exact free rectangle law; no conditional product premise is required. -/
theorem rectangle_split_probability_le_arm_sum_of_sampled_complementary_arms (θ : Parameters)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (n : ℕ) (r : ℝ) (hn : 1 ≤ n) (hr : 1 ≤ r) (hrn : 2*⌈r⌉₊ ≤ 2*n-2)
    (a b z : (box n : Set LatticeVertex)) (ha : a.val.1 = -(n : ℤ)) (hb : b.val.1 = n)
    (hfar : 4*r ≤ tubeDistance a.val b.val z.val)
    (B : Set (Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))))
    (hB : ∀ A ∈ B,
      ActualConnected _ A (boxTubeRectangleIso n a) (boxTubeRectangleIso n z) ∧
      ActualConnected _ A (boxTubeRectangleIso n b) (boxTubeRectangleIso n z) ∧
      A ∈ sampledRectangleDualArmsEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        (sampledStarFacePorts (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (boxTubeRectangleIso n z))
        (sampledStarFacePorts (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (boxTubeRectangleIso n z))
        (PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) a.val b.val)
        (PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) a.val b.val)
        (fun _ => True) (fun _ => True)) :
    (1-edgeParameter θ)^4 * (measure _ θ (BoundaryCondition.free ∅) B).toReal ≤
      splitArmSum (RSW.oneArmProbability μ) r (2*n-2) := by
  rw [RSW.free_probability_iso θ (boxTubeRectangleIso n)]
  apply split_probability_le_arm_sum_of_sampled_complementary_arms θ μ hμ n r hn hr hrn
    a b z ha hb hfar {A | configurationIso (boxTubeRectangleIso n) A ∈ B}
  intro A hA
  obtain ⟨huz,hvz,harms⟩ := hB _ hA
  exact ⟨harms,(actualConnected_configurationIso (boxTubeRectangleIso n) A a z).mp huz,
    (actualConnected_configurationIso (boxTubeRectangleIso n) A b z).mp hvz⟩

end
end PottsContinuity.Thm3.Prop4
