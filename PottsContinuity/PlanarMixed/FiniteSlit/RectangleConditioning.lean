module

public import PottsContinuity.PlanarMixed.FiniteSlit.BoundaryPartition
public import PottsContinuity.PlanarMixed.ComplementaryConditioning

/-! Exact finite slit conditioning in the surrounding free rectangle.
Auxiliary alpha/beta bonds are OPEN and all deleted slit bonds are CLOSED;
rectangular duality transports every one of those fixed states. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.Duality BD12 DualityExt
noncomputable section
local instance finiteSlitRectangleConditioningEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- The active source graph lies in the original balanced rectangle. -/
theorem activeGraph_le_rectangle (M : ℕ) (x y : ℤ) :
    activeGraph M x y ≤ rectangleGraph (x-(M : ℤ),0) (2*M-1) M :=
  (edgeRestriction_le (graph M x y) (internalEdges M x y)).trans (graph_le_rectangle M x y)

/-- Every auxiliary arc bond is outside the active sampled source carrier. -/
theorem rectangleArcBonds_subset_removed (M : ℕ) (x y : ℤ) :
    rectangleArcBonds M x y ⊆ subgraphRemovedEdges (activeGraph M x y)
      (rectangleGraph (x-(M : ℤ),0) (2*M-1) M) := by
  rintro ⟨e,he⟩ hR
  induction e using Sym2.inductionOn with
  | _ u v =>
    rw [mem_subgraphRemovedEdges]
    intro ha
    obtain ⟨hg,hn⟩ := (edgeRestriction_adj_exists_not_mem _ _ _ _).mp
      ((activeGraph M x y).mem_edgeSet.mp ha)
    apply hn
    rw [internalEdges,Finset.mem_union,mem_internalBonds_pair _ _ u v hg,
      mem_internalBonds_pair _ _ u v hg]
    have hr := (rectangleGraph (x-(M : ℤ),0) (2*M-1) M).mem_edgeSet.mp he
    rw [rectangleArcBonds,Finset.mem_union,mem_internalBonds_pair _ _ u v hr,
      mem_internalBonds_pair _ _ u v hr] at hR
    exact hR

/-- OPEN precisely the two arc states; every other removed host bond is CLOSED. -/
def exteriorState (M : ℕ) (x y : ℤ) :
    RemovedConfiguration (rectangleGraph (x-(M : ℤ),0) (2*M-1) M)
      (subgraphRemovedEdges (activeGraph M x y)
        (rectangleGraph (x-(M : ℤ),0) (2*M-1) M)) :=
  ⟨rectangleArcBonds M x y,rectangleArcBonds_subset_removed M x y⟩

def hostRestriction (M : ℕ) (x y : ℤ) :=
  subgraphConfigurationRestriction (activeGraph_le_rectangle M x y)

/-- The conditioned free rectangle restricts to the exact separate-alpha-beta
active source FK law, for every interior FK parameter. -/
theorem active_law_of_conditioned_free_rectangle (θ : Parameters)
    (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    ((law (rectangleGraph (x-(M : ℤ),0) (2*M-1) M) θ (BoundaryCondition.free ∅)).filter
      (frozenStateEvent _ (exteriorState M x y))
      (frozenStateEvent_support θ (BoundaryCondition.free ∅) _ (exteriorState M x y))).map
      (hostRestriction M x y) = law (activeGraph M x y) θ (boundary M x y hM hy hyM) := by
  let H := rectangleGraph (x-(M : ℤ),0) (2*M-1) M
  let G := activeGraph M x y
  let R := subgraphRemovedEdges G H
  let K := exteriorState M x y
  let E := subgraphRemainingConfigurationEquiv (activeGraph_le_rectangle M x y)
  have hpart : (frozenBoundary (BoundaryCondition.free ∅) K.val).partition =
      (boundary M x y hM hy hyM).partition := rectangleArcBonds_frozen_partition M x y hM hy hyM
  have hremaining : remainingLaw H θ (frozenBoundary (BoundaryCondition.free ∅) K.val) R =
      remainingLaw H θ (boundary M x y hM hy hyM) R := by
    rw [← law_edgeRestriction_map,← law_edgeRestriction_map,
      law_eq_of_boundary_partition_eq θ _ _ hpart]
  have h := law_filter_frozen_map_remaining θ (BoundaryCondition.free ∅) R K
  rw [hremaining,← law_subgraphRemaining_map
    (activeGraph_le_rectangle M x y) θ (boundary M x y hM hy hyM)] at h
  have hm := congrArg (fun p => p.map E.symm) h
  rw [PMF.map_comp,PMF.map_comp] at hm
  have hE : E.symm ∘ E = id := funext E.symm_apply_apply
  rw [hE,PMF.map_id] at hm
  have hrestrict : E.symm ∘ (fun C => (configurationSplitEquiv H R C).1) =
      hostRestriction M x y := by
    funext C
    exact subgraphRemainingConfigurationEquiv_symm_split _ C
  rw [hrestrict] at hm
  exact hm

/-- Exact removed dual carrier, including the duals of deleted slit bonds. -/
def dualRemovedEdges (M : ℕ) (x y : ℤ) :
    Configuration (rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M) :=
  rectangleSubgraphRemovedDualEdges (activeGraph_le_rectangle M x y)

/-- Complementary exterior state: auxiliary arc duals CLOSED, slit duals OPEN. -/
def dualExteriorState (M : ℕ) (x y : ℤ) :
    RemovedConfiguration (rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M)
      (dualRemovedEdges M x y) :=
  ⟨positiveRectangleDualConfigurationEquiv (x-(M : ℤ),0) (2*M-1) M
      (exteriorState M x y).val ∩ dualRemovedEdges M x y,Finset.inter_subset_right⟩

/-- Exact finite rectangle duality after fixing all exterior source states.
The induced dual partition is not silently replaced by a boundary label. -/
theorem conditioned_rectangle_duality (θ : Parameters) (M : ℕ) (x y : ℤ) :
    ((law (rectangleGraph (x-(M : ℤ),0) (2*M-1) M) θ (BoundaryCondition.free ∅)).filter
      (frozenStateEvent _ (exteriorState M x y))
      (frozenStateEvent_support θ (BoundaryCondition.free ∅) _ (exteriorState M x y))).map
      (positiveRectangleDualConfigurationEquiv (x-(M : ℤ),0) (2*M-1) M) =
    (law (rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M) (dualParameters θ)
      (rectangleDualBoundaryCondition (x-(M : ℤ),0) (2*M-1) M)).filter
      (frozenStateEvent _ (dualExteriorState M x y))
      (frozenStateEvent_support (dualParameters θ) _ _ (dualExteriorState M x y)) := by
  have hevent : frozenStateEvent _ (exteriorState M x y) =
      (positiveRectangleDualConfigurationEquiv (x-(M : ℤ),0) (2*M-1) M) ⁻¹'
        frozenStateEvent _ (dualExteriorState M x y) := by
    ext C
    exact complementary_frozen_intersection_iff
      (rectangleDualEdgeEquiv (x-(M : ℤ),0) (2*M-1) M)
      (positiveRectangleDualConfigurationEquiv (x-(M : ℤ),0) (2*M-1) M)
      (fun A e => rectangleDualEdgeEquiv_mem_dualConfiguration A e) _ _ C
      (exteriorState M x y).property
  have hdual :
      (law (rectangleGraph (x-(M : ℤ),0) (2*M-1) M) θ (BoundaryCondition.free ∅)).map
        (positiveRectangleDualConfigurationEquiv (x-(M : ℤ),0) (2*M-1) M) =
      law (rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M) (dualParameters θ)
        (rectangleDualBoundaryCondition (x-(M : ℤ),0) (2*M-1) M) :=
    rectangleFKLaw_map_primalDualConfigurationEquiv θ (x-(M : ℤ),0) (2*M-1) M
  have h := pmf_map_filter_equiv _ _ _ _ hevent
    (frozenStateEvent_support θ (BoundaryCondition.free ∅) _ (exteriorState M x y))
    (by rw [hdual]; exact frozenStateEvent_support (dualParameters θ) _ _ (dualExteriorState M x y))
  simpa only [hdual] using h

end
end PottsContinuity.PlanarMixed.FiniteSlit
