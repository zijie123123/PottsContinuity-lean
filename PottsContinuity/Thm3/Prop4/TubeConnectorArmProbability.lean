module

public import PottsContinuity.Thm3.Prop4.ClosedConnectorArmSplice
public import PottsContinuity.Thm3.Prop4.ClosedConnectorEnergy
public import PottsContinuity.Thm3.Prop4.TubeConnectorCost
public import PottsContinuity.Thm3.Prop4.FrozenFiberDualArms

/-!
# Paying the retained connector cost in the exact reference fiber

The closed-edge event and both stopped arms occur in one remaining-graph
sample. Their pointwise splice gives the original cut-root arms.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance connectorProbabilityOriginalEq (n : ℕ) :
    DecidableEq (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet := Classical.decEq _

/-- The exact all-open tube fiber loses only the proved exponential connector
cost when the stopped sampled arms are moved to the original cut roots. -/
theorem tube_reference_cut_arms_ge_stopped (θ : Parameters) {n : ℕ} (hn : 1 ≤ n)
    (r : ℝ) (hr : 1 ≤ r) (u v : LatticeVertex) (t b : ℝ) (ht : |t| ≤ 1)
    (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (lo hi : ℤ) (hlohi : lo ≤ hi)
    (hrows : radiusTubeCutRows n r u v 0 = Finset.Icc lo hi)
    (lower upper : Set LatticeVertex) :
    let R := rectangleTubeRevealedEdges n r u v;
    let ν := (frozenFiberLaw θ (BoundaryCondition.free ∅) R ⟨R,Finset.Subset.refl _⟩).toMeasure;
    Real.exp (-tubeClosingCoefficient θ*r) *
      (ν {A | A.val ∪ R ∈ sampledRectangleDualArmsEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        {(0,max (-(n : ℤ)-1) ⌊b-2*r⌋)} {(0,min (n : ℤ) ⌈b+2*r⌉)}
        lower upper (fun _ => True) (fun _ => True)}).toReal ≤
      (ν {A | A.val ∪ R ∈ sampledRectangleDualArmsEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        {(0,lo-1)} {(0,hi)} lower upper (fun _ => True) (fun _ => True)}).toReal := by
  dsimp only
  have heq (E : Set (Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)))) :=
    frozen_fiber_event_probability_eq_deleted
      (PD.FK.latticeRectangle (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) θ (BoundaryCondition.free ∅)
      (rectangleTubeRevealedEdges n r u v)
      ⟨rectangleTubeRevealedEdges n r u v,Finset.Subset.refl _⟩ E
  erw [heq,heq]
  let L := max (-(n : ℤ)-1) ⌊b-2*r⌋
  let U := min (n : ℤ) ⌈b+2*r⌉
  let R := rectangleTubeRevealedEdges n r u v
  let restore := fun C : Configuration (tubePrimalRemainingGraph n r u v) =>
    (edgeRestrictionConfigurationEquiv _ R C).val ∪ R
  let E := restore ⁻¹' sampledRectangleDualArmsEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
    {(0,L)} {(0,U)} lower upper (fun _ => True) (fun _ => True)
  let F := tubeRemainingCentralRows n r u v (L+1) (lo-1) ∪
    tubeRemainingCentralRows n r u v (hi+1) U
  let ξ := frozenBoundary (BoundaryCondition.free ∅) R
  have hE : IsLowerSet E := by
    intro A C hCA hA
    apply isLowerSet_sampledRectangleDualArmsEvent _ _ _ _ _ _ _ _ _ _ hA
    apply Finset.union_subset_union_left
    rw [edgeRestrictionConfigurationEquiv_val,edgeRestrictionConfigurationEquiv_val]
    exact Finset.map_subset_map.mpr hCA
  have henergy := finite_closed_edges_and_lower (tubePrimalRemainingGraph n r u v) θ ξ F E hE
  have hcost := tube_connector_closing_cost_lower θ hn r hr u v t b ht hu hv lo hi hlohi hrows
  have hL := central_cut_lower_connector_stopped hn r u v t b ht hu hv lo hi hlohi hrows
  have hU := central_cut_upper_connector_stopped hn r u v t b ht hu hv lo hi hlohi hrows
  have hsub : {C | Disjoint C F} ∩ E ⊆ restore ⁻¹'
      sampledRectangleDualArmsEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        {(0,lo-1)} {(0,hi)} lower upper (fun _ => True) (fun _ => True) := by
    intro C hC
    exact closed_connectors_splice_sampled_arms hn r u v lo hi L U hlohi hrows
      ⟨hL.1,hL.2.1⟩ ⟨hU.1,hU.2.1⟩ C hC.1 lower upper hC.2
  exact (mul_le_mul_of_nonneg_right hcost ENNReal.toReal_nonneg).trans
    (henergy.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)))

end
end PottsContinuity.Thm3.Prop4
