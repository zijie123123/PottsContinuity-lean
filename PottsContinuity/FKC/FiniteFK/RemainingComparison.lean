-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/RemainingComparison.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.EdgeRestriction
public import PottsContinuity.FKC.FiniteFK.IncreasingEvents

/-!
# FKG and boundary comparison for the actual remaining-edge law

The exact configuration order isomorphism transports the complete finite FK
inequalities from the same-vertex deleted graph. The edge set R is arbitrary;
no prewiring, conditional independence, or comparison premise is added.
-/

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open scoped BigOperators
noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)

local instance remainingComparisonEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance remainingComparisonDeletedEdgeFintype (R : Configuration G) :
    Fintype (edgeRestriction G R).edgeSet := Fintype.ofFinite _
local instance remainingComparisonConfigurationFintype (R : Configuration G) :
    Fintype (RemainingConfiguration G R) := Fintype.ofFinite _

/-- Exact matching point masses under the proved configuration bijection. -/
theorem remainingLaw_apply_edgeRestriction (q : ClusterWeight) (ξ : BoundaryCondition V)
    (R : Configuration G) (A : Configuration (edgeRestriction G R)) :
    remainingLaw G q ξ R (edgeRestrictionConfigurationEquiv G R A) =
      law (edgeRestriction G R) q ξ A := by
  rw [← law_edgeRestriction_map, FiniteProbability.map_equiv_apply, Equiv.symm_apply_apply]

/-- Reindexing any real observable gives its actual expectation on the deleted graph. -/
theorem remainingLaw_sum_toReal (q : ClusterWeight) (ξ : BoundaryCondition V)
    (R : Configuration G) (f : RemainingConfiguration G R → ℝ) :
    (∑ A, (remainingLaw G q ξ R A).toReal * f A) =
      ∑ C, configurationProbability (edgeRestriction G R) q ξ C *
        f (edgeRestrictionConfigurationEquiv G R C) := by
  rw [← (edgeRestrictionConfigurationEquiv G R).sum_comp
    (fun A => (remainingLaw G q ξ R A).toReal * f A)]
  apply Finset.sum_congr rfl
  intro C hC
  rw [remainingLaw_apply_edgeRestriction, law_apply,
    ENNReal.toReal_ofReal (configurationProbability_pos _ _ _ _).le]

/-- Coarser boundary identifications increase every nonnegative increasing
observable of all actually sampled remaining edges. -/
theorem remainingLaw_boundary_comparison (q : ClusterWeight) (ξ η : BoundaryCondition V)
    (hξη : ξ.partition ≤ η.partition) (R : Configuration G)
    (f : RemainingConfiguration G R → ℝ) (hf0 : ∀ A, 0 ≤ f A) (hf : Monotone f) :
    (∑ A, (remainingLaw G q ξ R A).toReal * f A) ≤
      ∑ A, (remainingLaw G q η R A).toReal * f A := by
  rw [remainingLaw_sum_toReal, remainingLaw_sum_toReal]
  have hmono : Monotone (fun C => f (edgeRestrictionConfigurationEquiv G R C)) :=
    hf.comp (edgeRestrictionConfigurationOrderIso G R).monotone
  simpa only [mul_comm] using configurationProbability_boundary_comparison
    (G := edgeRestriction G R) q ξ η hξη
    (fun C => f (edgeRestrictionConfigurationEquiv G R C))
    (fun C => hf0 _) hmono

/-- Every subset of the finite remaining-configuration carrier is measurable. -/
abbrev remainingConfigurationMeasurableSpace (R : Configuration G) :
    MeasurableSpace (RemainingConfiguration G R) := ⊤

attribute [local instance] remainingConfigurationMeasurableSpace

local instance remainingComparisonDiscrete (R : Configuration G) :
    DiscreteMeasurableSpace (RemainingConfiguration G R) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The genuine probability measure induced by the existing remaining-edge PMF
on the full power-set sigma algebra. -/
def remainingMeasure (q : ClusterWeight) (ξ : BoundaryCondition V) (R : Configuration G) :
    MeasureTheory.Measure (RemainingConfiguration G R) := (remainingLaw G q ξ R).toMeasure

instance remainingMeasure_isProbabilityMeasure (q : ClusterWeight)
    (ξ : BoundaryCondition V) (R : Configuration G) :
    MeasureTheory.IsProbabilityMeasure (remainingMeasure G q ξ R) :=
  PMF.toMeasure.isProbabilityMeasure _

theorem remainingMeasure_apply (q : ClusterWeight) (ξ : BoundaryCondition V)
    (R : Configuration G) (s : Set (RemainingConfiguration G R)) :
    remainingMeasure G q ξ R s = ∑ A, s.indicator (remainingLaw G q ξ R) A :=
  PMF.toMeasure_apply_fintype _ _

/-- Every actual remaining-edge event is exactly its preimage event in the
same-vertex deleted graph. -/
theorem remainingMeasure_eq_edgeRestriction (q : ClusterWeight) (ξ : BoundaryCondition V)
    (R : Configuration G) (s : Set (RemainingConfiguration G R)) :
    remainingMeasure G q ξ R s =
      measure (edgeRestriction G R) q ξ (edgeRestrictionConfigurationEquiv G R ⁻¹' s) := by
  classical
  rw [remainingMeasure_apply, measure_apply,
    ← (edgeRestrictionConfigurationEquiv G R).sum_comp
      (fun A => s.indicator (remainingLaw G q ξ R) A)]
  apply Finset.sum_congr rfl
  intro C hC
  simp only [Set.indicator_apply, Set.mem_preimage, remainingLaw_apply_edgeRestriction]

omit [Finite V] in

end
end PottsContinuity.FKC.FiniteFK
