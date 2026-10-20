module

public import PottsContinuity.Thm3.Prop4.SampledCutReferenceProduct
public import PottsContinuity.Thm3.Prop4.FiniteDistantTarget

/-!
# The central cut reference estimate in frozen infinite-volume form

The two entire column target events are compared to their requested radii.
The all-open reference arm probability remains an actual model quantity.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

local instance sampledInfiniteEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Exact reference-factor surgery bound with both frozen infinite one-arm
probabilities and no planar or finite-volume comparison premise. -/
theorem sampled_cut_reference_probability_le_infinite_product (θ : Parameters)
    (a : LatticeVertex) (w h : ℕ) (u v : RectangleVertex a w h)
    (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (k lo hi : ℤ) (hlohi : lo ≤ hi) (huCut : u.val.1 ≤ k) (hvCut : k < v.val.1)
    (K R : Configuration (rectangleGraph a w h))
    (hcolumn : ∀ e ∈ K, ∃ y : ℤ, Sym2.map Subtype.val e.val = s((k,y),(k+1,y)))
    (hrows : ∀ y ∈ Finset.Icc lo hi, ∃ c : RectanglePrimalBond a w h,
      c.val = ⟨(k,y),.horizontal⟩ ∧ rectanglePrimalBondToEdge a w h c ∈ K)
    (P Q : LatticeVertex → Prop) (r s : ℕ)
    (hr : (r : ℤ) ≤ |k-u.val.1|) (hs : (s : ℤ) ≤ |k+1-v.val.1|)
    (μ : Measure (PottsContinuity.squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) :
    (1-edgeParameter θ)^K.card *
      ((frozenFiberLaw θ (BoundaryCondition.free ∅) R ⟨R,Finset.Subset.refl R⟩).toMeasure
        {A | A.val ∪ R ∈ sampledRectangleDualArmsEvent a w h {(k,lo-1)} {(k,hi)}
          (PlanarTopology.rectangleLowerDualArc a w h u.val v.val)
          (PlanarTopology.rectangleUpperDualArc a w h u.val v.val) P Q}).toReal *
      (measure (rectangleGraph a w h) θ (BoundaryCondition.free ∅)
        {A | ActualConnected (rectangleGraph a w h) (A ∩ R) u v}).toReal ≤
      RSW.oneArmProbability μ r * RSW.oneArmProbability μ s := by
  apply (sampled_cut_reference_probability_le_free_product θ a w h u v hu hv
    k lo hi hlohi huCut hvCut K R hcolumn hrows P Q).trans
  exact mul_le_mul
    (rectangle_free_column_target_le_infinite_arm θ a w h u k r hr μ hμ)
    (rectangle_free_column_target_le_infinite_arm θ a w h v (k+1) s hs μ hμ)
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg

end
end PottsContinuity.Thm3.Prop4
