module

public import PottsContinuity.Thm3.Prop4.FrozenDualRemainingLaw

/-!
# The literal deleted dual sample of the all-open primal reference fiber

Restoration opens exactly the prescribed original reveal. Its complementary
dual sample has every crossed revealed edge closed, so deleting those edges
retains the entire actual open graph and its exact wired-dual FK law.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

local instance referenceSamplePrimalEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _
local instance referenceSampleDualEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDualGraph a w h).edgeSet := Classical.decEq _

/-- The genuine complementary dual sample after restoring all revealed
original edges open and deleting their crossed closed dual bonds. -/
def frozenReferenceDualSample (a : LatticeVertex) (w h : ℕ)
    (R : Configuration (rectangleGraph a w h)) (A : RemainingConfiguration (rectangleGraph a w h) R) :
    Configuration (edgeRestriction (rectangleDualGraph a w h) (rectangleCrossedEdges a w h R)) :=
  (edgeRestrictionConfigurationEquiv (rectangleDualGraph a w h) (rectangleCrossedEdges a w h R)).symm
    (configurationSplitEquiv (rectangleDualGraph a w h) (rectangleCrossedEdges a w h R)
      (rectanglePrimalDualConfigurationEquiv a w h (A.val ∪ R))).1

/-- Deleting the prescribed closed dual bonds leaves the exact original dual
open graph of the restored primal sample, on all original finite face vertices. -/
theorem frozenReferenceDualSample_openGraph (a : LatticeVertex) (w h : ℕ)
    (R : Configuration (rectangleGraph a w h)) (A : RemainingConfiguration (rectangleGraph a w h) R) :
    openGraph _ (frozenReferenceDualSample a w h R A) =
      openGraph (rectangleDualGraph a w h) (rectanglePrimalDualConfigurationEquiv a w h (A.val ∪ R)) := by
  let Rd := rectangleCrossedEdges a w h R
  let C := (configurationSplitEquiv (rectangleDualGraph a w h) Rd
    (rectanglePrimalDualConfigurationEquiv a w h (A.val ∪ R))).1
  let E := edgeRestrictionConfigurationEquiv (rectangleDualGraph a w h) Rd
  have hdis : Disjoint (rectanglePrimalDualConfigurationEquiv a w h (A.val ∪ R)) Rd := by
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    apply (rectangle_all_open_state_iff_dual_closed a w h R (A.val ∪ R)).mp
    change (A.val ∪ R) ∩ R = R
    exact Finset.inter_eq_right.mpr Finset.subset_union_right
  change openGraph (edgeRestriction (rectangleDualGraph a w h) Rd) (E.symm C) = _
  calc
    _ = openGraph (rectangleDualGraph a w h) (E (E.symm C)).val :=
      openGraph_edgeRestriction _ _ _
    _ = openGraph (rectangleDualGraph a w h) C.val :=
      congrArg (fun B : RemainingConfiguration (rectangleDualGraph a w h) Rd => openGraph _ B.val)
        (E.apply_symm_apply C)
    _ = _ := by
      change openGraph (rectangleDualGraph a w h)
        (rectanglePrimalDualConfigurationEquiv a w h (A.val ∪ R) \ Rd) = _
      rw [Finset.sdiff_eq_self_of_disjoint hdis]

/-- The literal sample map has the exact same-parameter wired dual law at
the explicit self-dual value, for every real cluster weight at least one. -/
theorem selfDual_frozenReferenceDualSample_law (q : Set.Ici (1 : ℝ))
    (a : LatticeVertex) (w h : ℕ) (R : Configuration (rectangleGraph a w h)) :
    (frozenFiberLaw (RSW.selfDualParameters q) (BoundaryCondition.free ∅) R
      ⟨R,Finset.Subset.refl R⟩).map (frozenReferenceDualSample a w h R) =
      law (edgeRestriction (rectangleDualGraph a w h) (rectangleCrossedEdges a w h R))
        (RSW.selfDualParameters q) (rectangleDualBoundaryCondition a w h) :=
  selfDual_frozen_reference_dual_deleted_law q a w h R

/-- Every actual deleted-dual event transports exactly back to the normalized
all-open primal reference fiber by the literal sample map. -/
theorem selfDual_frozenReferenceDualSample_probability (q : Set.Ici (1 : ℝ))
    (a : LatticeVertex) (w h : ℕ) (R : Configuration (rectangleGraph a w h))
    (E : Set (Configuration (edgeRestriction (rectangleDualGraph a w h) (rectangleCrossedEdges a w h R)))) :
    ((frozenFiberLaw (RSW.selfDualParameters q) (BoundaryCondition.free ∅) R
      ⟨R,Finset.Subset.refl R⟩).toMeasure {A | frozenReferenceDualSample a w h R A ∈ E}).toReal =
    (measure (edgeRestriction (rectangleDualGraph a w h) (rectangleCrossedEdges a w h R))
      (RSW.selfDualParameters q) (rectangleDualBoundaryCondition a w h) E).toReal := by
  have hlaw := congrArg (fun ρ : PMF (Configuration
    (edgeRestriction (rectangleDualGraph a w h) (rectangleCrossedEdges a w h R))) => ρ.toMeasure E)
      (selfDual_frozenReferenceDualSample_law q a w h R)
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at hlaw
  exact congrArg ENNReal.toReal hlaw

end
end PottsContinuity.Thm3.Prop4
