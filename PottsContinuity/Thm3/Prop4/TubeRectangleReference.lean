module

public import PottsContinuity.Thm3.Prop4.RectangleTubeCutRows
public import PottsContinuity.Thm3.Prop4.SampledCutInfiniteProduct
public import PottsContinuity.Thm3.RSW.FiniteIso

/-!
# The literal tube reference estimate at the source radii

The fixed reveal and cut are coordinate images of the original box objects.
The source event consists of original open tube-confined walks. The two
infinite arms have radii n and n-1, with the proved exponential closing cost.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

local instance tubeRectangleReferenceSourceEq (n : ℕ) :
    DecidableEq (squareLattice.induce (box n : Set LatticeVertex)).edgeSet := Classical.decEq _
local instance tubeRectangleReferenceTargetEq (n : ℕ) :
    DecidableEq (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet := Classical.decEq _

/-- The whole original tube reveal on the coordinate-identical rectangle. -/
def rectangleTubeRevealedEdges (n : ℕ) (r : ℝ) (u v : LatticeVertex) :
    Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) :=
  configurationIso (boxTubeRectangleIso n) (radiusTubeRevealedEdges n r u v)

/-- The original tube surgery cut on the coordinate-identical rectangle. -/
def rectangleTubeCutEdges (n : ℕ) (r : ℝ) (u v : LatticeVertex) (k : ℤ) :
    Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) :=
  configurationIso (boxTubeRectangleIso n) (radiusTubeCutEdges n r u v k)

/-- The actual reference-arm probability times the literal source tube
connection and exponential closing cost is bounded by the n,n-1 arm product. -/
theorem tube_reference_probability_le_infinite_arm_product (θ : Parameters)
    {n : ℕ} (hn : 1 ≤ n) (r : ℝ) (hr : 2 ≤ r)
    (a b : (box n : Set LatticeVertex))
    (ha : a.val.1 = -(n : ℤ)) (hb : b.val.1 = n) (P Q : LatticeVertex → Prop)
    (μ : Measure (PottsContinuity.squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) :
    ∃ lo hi : ℤ, lo ≤ hi ∧ radiusTubeCutRows n r a.val b.val 0 = Finset.Icc lo hi ∧
      Real.exp (-tubeClosingCoefficient θ*r) *
        ((frozenFiberLaw θ (BoundaryCondition.free ∅) (rectangleTubeRevealedEdges n r a.val b.val)
          ⟨rectangleTubeRevealedEdges n r a.val b.val,Finset.Subset.refl _⟩).toMeasure
          {A | A.val ∪ rectangleTubeRevealedEdges n r a.val b.val ∈
            sampledRectangleDualArmsEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
              {(0,lo-1)} {(0,hi)}
              (PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) a.val b.val)
              (PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) a.val b.val) P Q}).toReal *
        (measure (squareLattice.induce (box n : Set LatticeVertex)) θ (BoundaryCondition.free ∅)
          {A | ∃ p : (openGraph _ A).Walk a b,
            ∀ z ∈ p.support, z.val ∈ radiusTube n r a.val b.val}).toReal ≤
        RSW.oneArmProbability μ n * RSW.oneArmProbability μ (n-1) := by
  obtain ⟨lo,hi,hlohi,hrows,hsampled⟩ := rectangle_central_tube_cut_rows hn r hr a.val b.val
    a.property b.property ha hb
  refine ⟨lo,hi,hlohi,hrows,?_⟩
  have hv : (boxTubeRectangleIso n b).val.1 = -(n : ℤ)+(2*n : ℕ) := by
    change b.val.1 = -(n : ℤ)+(2*n : ℕ)
    push_cast
    omega
  have huCut : (boxTubeRectangleIso n a).val.1 ≤ 0 := by change a.val.1 ≤ 0; omega
  have hvCut : (0 : ℤ) < (boxTubeRectangleIso n b).val.1 := by change 0 < b.val.1; omega
  have huRad : (n : ℤ) ≤ |0-(boxTubeRectangleIso n a).val.1| := by
    change (n : ℤ) ≤ |0-a.val.1|
    rw [ha]
    simp
  have hvRad : ((n-1 : ℕ) : ℤ) ≤ |0+1-(boxTubeRectangleIso n b).val.1| := by
    change ((n-1 : ℕ) : ℤ) ≤ |0+1-b.val.1|
    rw [hb]
    simp only [zero_add,abs_eq_max_neg]
    omega
  have hbase := sampled_cut_reference_probability_le_infinite_product θ
    (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (boxTubeRectangleIso n a) (boxTubeRectangleIso n b)
    ha hv 0 lo hi hlohi huCut hvCut (rectangleTubeCutEdges n r a.val b.val 0)
    (rectangleTubeRevealedEdges n r a.val b.val)
    (rectangle_tube_cut_column n r a.val b.val 0) hsampled P Q n (n-1) huRad hvRad μ hμ
  have haTube : a.val ∈ radiusTube n r a.val b.val := by
    apply (mem_radiusTube n r a.val b.val a.val).mpr
    refine ⟨a.property,?_⟩
    change Metric.infDist _ (segment ℝ _ _) < r
    rw [Metric.infDist_zero_of_mem (left_mem_segment ℝ _ _)]
    linarith only [hr]
  have hsource :
      (measure _ θ (BoundaryCondition.free ∅)
        {C | ActualConnected _ (C ∩ rectangleTubeRevealedEdges n r a.val b.val)
          (boxTubeRectangleIso n a) (boxTubeRectangleIso n b)}).toReal =
      (measure (squareLattice.induce (box n : Set LatticeVertex)) θ (BoundaryCondition.free ∅)
        {A | ∃ p : (openGraph _ A).Walk a b,
          ∀ z ∈ p.support, z.val ∈ radiusTube n r a.val b.val}).toReal := by
    rw [RSW.free_probability_iso θ (boxTubeRectangleIso n)]
    apply congrArg (fun E => (measure (squareLattice.induce (box n : Set LatticeVertex))
      θ (BoundaryCondition.free ∅) E).toReal)
    ext A
    exact box_rectangle_tube_connection_iff_walk n r a.val b.val A a b haTube
  rw [hsource] at hbase
  have hcost : Real.exp (-tubeClosingCoefficient θ*r) ≤
      (1-edgeParameter θ)^(rectangleTubeCutEdges n r a.val b.val 0).card := by
    unfold rectangleTubeCutEdges
    rw [card_configurationIso]
    exact radiusTube_closing_cost_lower θ hn r (by linarith only [hr])
      a.val b.val a.property b.property ha hb 0
  apply le_trans _ hbase
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcost ENNReal.toReal_nonneg) ENNReal.toReal_nonneg

end
end PottsContinuity.Thm3.Prop4
