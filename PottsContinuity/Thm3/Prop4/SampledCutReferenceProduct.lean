module

public import PottsContinuity.Thm3.Prop4.FrozenSourceLowerBound
public import PottsContinuity.Thm3.Prop4.SampledCutClosingProduct

/-!
# The sampled cut product with one all-open reference state

The source connection uses only a prescribed set of revealed edges. Averaging
its exact frozen states gives the reference dual-arm factor before surgery.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

local instance sampledReferenceEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- The genuine all-open-reference arm probability times the source connection
and closing cost is bounded by the two free adjacent-column arm probabilities. -/
theorem sampled_cut_reference_probability_le_free_product (θ : Parameters)
    (a : LatticeVertex) (w h : ℕ) (u v : RectangleVertex a w h)
    (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (k lo hi : ℤ) (hlohi : lo ≤ hi) (huCut : u.val.1 ≤ k) (hvCut : k < v.val.1)
    (K R : Configuration (rectangleGraph a w h))
    (hcolumn : ∀ e ∈ K, ∃ y : ℤ, Sym2.map Subtype.val e.val = s((k,y),(k+1,y)))
    (hrows : ∀ y ∈ Finset.Icc lo hi, ∃ c : RectanglePrimalBond a w h,
      c.val = ⟨(k,y),.horizontal⟩ ∧ rectanglePrimalBondToEdge a w h c ∈ K)
    (P Q : LatticeVertex → Prop) :
    (1-edgeParameter θ)^K.card *
      ((frozenFiberLaw θ (BoundaryCondition.free ∅) R ⟨R,Finset.Subset.refl R⟩).toMeasure
        {A | A.val ∪ R ∈ sampledRectangleDualArmsEvent a w h {(k,lo-1)} {(k,hi)}
          (PlanarTopology.rectangleLowerDualArc a w h u.val v.val)
          (PlanarTopology.rectangleUpperDualArc a w h u.val v.val) P Q}).toReal *
      (measure (rectangleGraph a w h) θ (BoundaryCondition.free ∅)
        {A | ActualConnected (rectangleGraph a w h) (A ∩ R) u v}).toReal ≤
    (measure (rectangleGraph a w h) θ (BoundaryCondition.free ∅)
      (targetConnectionEvent u {z | z.val.1 = k})).toReal *
    (measure (rectangleGraph a w h) θ (BoundaryCondition.free ∅)
      (targetConnectionEvent v {z | z.val.1 = k+1})).toReal := by
  let G := rectangleGraph a w h
  let ξ : BoundaryCondition (RectangleVertex a w h) := BoundaryCondition.free ∅
  let E := sampledRectangleDualArmsEvent a w h {(k,lo-1)} {(k,hi)}
    (PlanarTopology.rectangleLowerDualArc a w h u.val v.val)
    (PlanarTopology.rectangleUpperDualArc a w h u.val v.val) P Q
  let S : Set (RemovedConfiguration G R) := {H | ActualConnected G H.val u v}
  have hlower := finite_FK_lower_event_joint_ge_all_open (PD.FK.latticeRectangle a w h)
    θ ξ R S E (isLowerSet_sampledRectangleDualArmsEvent a w h _ _ _ _ P Q)
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hlower
  rw [ENNReal.toReal_mul] at hreal
  change ((frozenFiberLaw θ ξ R ⟨R,Finset.Subset.refl R⟩).toMeasure
      {A | A.val ∪ R ∈ E}).toReal *
    (measure G θ ξ {A | ActualConnected G (A ∩ R) u v}).toReal ≤
    (measure G θ ξ ({A | ActualConnected G (A ∩ R) u v} ∩ E)).toReal at hreal
  have hclosing := sampled_cut_closing_probability_le_free_product θ a w h u v hu hv
    k lo hi hlohi huCut hvCut K hcolumn hrows P Q
    ({A | ActualConnected G (A ∩ R) u v} ∩ E) (by
      intro A hA
      exact ⟨hA.2,actualConnected_mono Finset.inter_subset_left hA.1⟩)
  have hcost : 0 ≤ (1-edgeParameter θ)^K.card :=
    pow_nonneg (sub_nonneg.mpr (edgeParameter_lt_one θ).le) _
  apply le_trans _ hclosing
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hreal hcost

end
end PottsContinuity.Thm3.Prop4
