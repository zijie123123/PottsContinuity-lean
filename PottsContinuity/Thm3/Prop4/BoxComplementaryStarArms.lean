module

public import PottsContinuity.Thm3.Prop4.StarIsoTransport
public import PottsContinuity.Thm3.Prop4.BoxRectangleTubeTransport
public import PottsContinuity.Thm3.Prop4.SampledStarPorts
public import PottsContinuity.Thm3.Prop4.SplitScreenBound

/-!
# The actual complementary star screen on the original source box

All dual steps are genuine sampled closed-original bonds. The coordinate
isomorphism retains the source sample and the full original incident star.
The split convolution therefore uses the actual complementary boundary arcs.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance boxComplementarySourceEdgeEq (n : ℕ) :
    DecidableEq (squareLattice.induce (box n : Set LatticeVertex)).edgeSet := Classical.decEq _
local instance boxComplementaryTargetEdgeEq (n : ℕ) :
    DecidableEq (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet := Classical.decEq _

/-- Two actual sampled complementary-arc arms landing on genuine star ports,
read on the unchanged original box configuration. -/
def boxSampledComplementaryStarArmsEvent (n : ℕ) (a b z : (box n : Set LatticeVertex)) :
    Set (Configuration (squareLattice.induce (box n : Set LatticeVertex))) :=
  configurationIso (boxTubeRectangleIso n) ⁻¹'
    sampledRectangleDualArmsEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
      (sampledStarFacePorts (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (boxTubeRectangleIso n z))
      (sampledStarFacePorts (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (boxTubeRectangleIso n z))
      (PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) a.val b.val)
      (PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) a.val b.val)
      (fun _ => True) (fun _ => True)

/-- Closing sampled original bonds preserves the exact complementary screen. -/
theorem isLowerSet_boxSampledComplementaryStarArmsEvent (n : ℕ)
    (a b z : (box n : Set LatticeVertex)) :
    IsLowerSet (boxSampledComplementaryStarArmsEvent n a b z) := by
  intro A C hCA hA
  exact isLowerSet_sampledRectangleDualArmsEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
    (sampledStarFacePorts (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (boxTubeRectangleIso n z))
    (sampledStarFacePorts (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (boxTubeRectangleIso n z))
    (PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) a.val b.val)
    (PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) a.val b.val)
    (fun _ => True) (fun _ => True)
    (configurationIso_monotone (boxTubeRectangleIso n) hCA) hA

/-- The genuine sampled complementary screen separates the original box marks
when their actual incident star is closed, also on every boundary corner. -/
theorem box_sampled_complementary_star_arms_disconnect {n : ℕ} (hn : 1 ≤ n)
    (a b z : (box n : Set LatticeVertex)) (ha : a.val.1 = -(n : ℤ)) (hb : b.val.1 = n)
    (C : Configuration (squareLattice.induce (box n : Set LatticeVertex)))
    (hC : C ∈ boxSampledComplementaryStarArmsEvent n a b z)
    (hclosed : Disjoint C (vertexStarEdges (squareLattice.induce (box n : Set LatticeVertex)) z)) :
    ¬ ActualConnected _ C a b := by
  have hb' : (boxTubeRectangleIso n b).val.1 = -(n : ℤ)+(2*n : ℕ) := by
    change b.val.1 = -(n : ℤ)+(2*n : ℕ)
    push_cast
    omega
  have hd := sampled_star_closing_dual_arms_disconnect (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
    (by omega) (by omega) (configurationIso (boxTubeRectangleIso n) C)
    (boxTubeRectangleIso n a) (boxTubeRectangleIso n b) ha hb' (boxTubeRectangleIso n z)
    (fun _ => True) (fun _ => True) hC
  intro hconn
  apply hd
  rw [← configurationIso_close_star,actualConnected_configurationIso]
  simpa only [Finset.sdiff_eq_self_of_disjoint hclosed] using hconn

/-- The exact equation-(29) convolution from actual complementary sampled
arms and the two retained primal connections, with planar geometry discharged. -/
theorem split_probability_le_arm_sum_of_sampled_complementary_arms (θ : Parameters)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (n : ℕ) (r : ℝ) (hn : 1 ≤ n) (hr : 1 ≤ r) (hrn : 2*⌈r⌉₊ ≤ 2*n-2)
    (a b z : (box n : Set LatticeVertex)) (ha : a.val.1 = -(n : ℤ)) (hb : b.val.1 = n)
    (hfar : 4*r ≤ tubeDistance a.val b.val z.val)
    (B : Set (Configuration (squareLattice.induce (box n : Set LatticeVertex))))
    (hB : ∀ A ∈ B, A ∈ boxSampledComplementaryStarArmsEvent n a b z ∧
      ActualConnected _ A a z ∧ ActualConnected _ A b z) :
    (1-edgeParameter θ)^4 * (measure _ θ (BoundaryCondition.free ∅) B).toReal ≤
      splitArmSum (RSW.oneArmProbability μ) r (2*n-2) := by
  exact split_probability_le_arm_sum_of_separatingScreen θ μ hμ n r hn hr hrn
    a b z ha hb hfar B (boxSampledComplementaryStarArmsEvent n a b z)
    (isLowerSet_boxSampledComplementaryStarArmsEvent n a b z) hB
    (fun C hC hc => box_sampled_complementary_star_arms_disconnect hn a b z ha hb C hC hc)

end
end PottsContinuity.Thm3.Prop4
