module

public import PottsContinuity.Thm3.Prop4.RectangleFrozenDuality
public import PottsContinuity.Thm3.Prop4.FrozenOriginalConditioning
public import PottsContinuity.PD.FK.EdgeRestriction
public import PottsContinuity.PD.FK.BoundaryPartitionLaw
public import PottsContinuity.Thm3.RSW.SelfDualSetup

/-!
# The exact deleted-dual-graph law of the all-open reference fiber

Crossed revealed bonds are deleted on the dual side. All original dual
vertices and the rectangle exterior boundary partition are retained.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.Duality
noncomputable section

local instance dualRemainingPrimalEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _
local instance dualRemainingDualEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDualGraph a w h).edgeSet := Classical.decEq _

/-- The entire all-open primal reference fiber gives exactly the wired dual
FK law with the crossing revealed bonds deleted, at complementary parameters. -/
theorem frozen_all_open_reference_dual_deleted_law (θ : Parameters)
    (a : LatticeVertex) (w h : ℕ) (R : Configuration (rectangleGraph a w h)) :
    (frozenFiberLaw θ (BoundaryCondition.free ∅) R ⟨R,Finset.Subset.refl R⟩).map
      (fun A => (edgeRestrictionConfigurationEquiv (rectangleDualGraph a w h)
        (rectangleCrossedEdges a w h R)).symm
        (configurationSplitEquiv (rectangleDualGraph a w h) (rectangleCrossedEdges a w h R)
          (rectanglePrimalDualConfigurationEquiv a w h (A.val ∪ R))).1) =
      law (edgeRestriction (rectangleDualGraph a w h) (rectangleCrossedEdges a w h R))
        (dualParameters θ) (rectangleDualBoundaryCondition a w h) := by
  let D := rectanglePrimalDualConfigurationEquiv a w h
  let Rd := rectangleCrossedEdges a w h R
  let E := edgeRestrictionConfigurationEquiv (rectangleDualGraph a w h) Rd
  have hfull := congrArg (fun p : PMF (Configuration (rectangleGraph a w h)) => p.map D)
    (frozen_fiber_restore_eq_conditioned (rectangleGraph a w h) θ (BoundaryCondition.free ∅)
      R ⟨R,Finset.Subset.refl R⟩)
  have hdual := rectangle_free_all_open_filter_map_dual_closed θ a w h R
  change _ = _ at hfull
  rw [hdual] at hfull
  have hrem := congrArg (fun p : PMF (Configuration (rectangleDualGraph a w h)) =>
    p.map (fun C => (configurationSplitEquiv (rectangleDualGraph a w h) Rd C).1)) hfull
  rw [law_filter_frozen_map_remaining] at hrem
  have hdel := congrArg (fun p : PMF (RemainingConfiguration (rectangleDualGraph a w h) Rd) =>
    p.map E.symm) hrem
  rw [← law_edgeRestriction_map] at hdel
  simp only [PMF.map_comp] at hdel
  have hInv : E.symm ∘ E = id := by funext C; exact E.symm_apply_apply C
  rw [hInv,PMF.map_id] at hdel
  have hpart : (frozenBoundary (G := rectangleDualGraph a w h)
      (rectangleDualBoundaryCondition a w h) (∅ : Configuration (rectangleDualGraph a w h))).partition =
      (rectangleDualBoundaryCondition a w h).partition :=
    componentSetoid_empty _ _
  have hfinal := hdel.trans (law_eq_of_boundary_partition_eq
    (G := edgeRestriction (rectangleDualGraph a w h) Rd) (dualParameters θ) _ _ hpart)
  simpa only [D,Rd,E,Function.comp_def] using hfinal

/-- At the explicit self-dual parameter the reference dual law has the same
parameter record, for every real cluster weight at least one. -/
theorem selfDual_frozen_reference_dual_deleted_law (q : Set.Ici (1 : ℝ))
    (a : LatticeVertex) (w h : ℕ) (R : Configuration (rectangleGraph a w h)) :
    (frozenFiberLaw (RSW.selfDualParameters q) (BoundaryCondition.free ∅) R
      ⟨R,Finset.Subset.refl R⟩).map
      (fun A => (edgeRestrictionConfigurationEquiv (rectangleDualGraph a w h)
        (rectangleCrossedEdges a w h R)).symm
        (configurationSplitEquiv (rectangleDualGraph a w h) (rectangleCrossedEdges a w h R)
          (rectanglePrimalDualConfigurationEquiv a w h (A.val ∪ R))).1) =
      law (edgeRestriction (rectangleDualGraph a w h) (rectangleCrossedEdges a w h R))
        (RSW.selfDualParameters q) (rectangleDualBoundaryCondition a w h) := by
  simpa only [RSW.selfDualParameters_fixed] using
    frozen_all_open_reference_dual_deleted_law (RSW.selfDualParameters q) a w h R

end
end PottsContinuity.Thm3.Prop4
