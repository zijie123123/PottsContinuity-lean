module

public import PottsContinuity.Thm3.Prop4.StableRecordDualArms

/-!
# Exact restoration of the original conditional record law

Restoring the recorded open edges after reading the remaining sample gives
the entire original configuration distribution conditioned on that record.
Thus an event in the reconstructed sample is the actual conditional event.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

local instance stableRecordOriginalEdgeDecidableEq (V : Finset LatticeVertex) :
    DecidableEq (squareLattice.induce (V : Set LatticeVertex)).edgeSet := Classical.decEq _

private theorem pmf_map_eq_on_support {α β : Type*} (p : PMF α) (f g : α → β)
    (h : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g := by
  classical
  ext b
  simp only [PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : p a = 0
  · simp only [ha,ite_self]
  · rw [h a ha]

/-- The actual original finite FK PMF conditioned on a complete attained stable record. -/
def stableRecordOriginalLaw (V : Finset LatticeVertex) (θ : Parameters)
    (ξ : BoundaryCondition (V : Set LatticeVertex))
    (reveal : Configuration (squareLattice.induce (V : Set LatticeVertex)) →
      Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (C₀ : Configuration (squareLattice.induce (V : Set LatticeVertex))) :
    PMF (Configuration (squareLattice.induce (V : Set LatticeVertex))) :=
  (law _ θ ξ).filter (Exploration.revealRecordEvent reveal C₀) (by
    rw [Exploration.revealRecordEvent_eq_frozenStateEvent reveal hstable C₀]
    exact frozenStateEvent_support θ ξ (reveal C₀) (Exploration.revealRecordConfiguration reveal C₀))

/-- Restoring the recorded edges reproduces the complete original conditional law. -/
theorem stable_record_restore_original_law (V : Finset LatticeVertex) (θ : Parameters)
    (ξ : BoundaryCondition (V : Set LatticeVertex))
    (reveal : Configuration (squareLattice.induce (V : Set LatticeVertex)) →
      Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (C₀ : Configuration (squareLattice.induce (V : Set LatticeVertex))) :
    (stableRecordRemainingLaw V θ ξ reveal hstable C₀).map
      (fun A => A.val ∪ (Exploration.revealRecordConfiguration reveal C₀).val) =
      stableRecordOriginalLaw V θ ξ reveal hstable C₀ := by
  let M := stableRecordOriginalLaw V θ ξ reveal hstable C₀
  change (M.map (fun C => (configurationSplitEquiv _ (reveal C₀) C).1)).map _ = M
  rw [PMF.map_comp]
  calc
    _ = M.map id := by
      apply pmf_map_eq_on_support
      intro C hC
      change C ∈ ((law _ θ ξ).filter _ _).support at hC
      have hs := ((PMF.mem_support_filter_iff _).mp hC).1
      have hstate : C ∩ reveal C₀ = C₀ ∩ reveal C₀ := hs.2
      change (C \ reveal C₀) ∪ (C₀ ∩ reveal C₀) = C
      rw [← hstate,Finset.sdiff_union_inter]
    _ = M := PMF.map_id M

/-- Every reconstructed event has exactly the actual original conditional probability. -/
theorem stable_record_original_event_probability_eq_reconstructed (V : Finset LatticeVertex) (θ : Parameters)
    (ξ : BoundaryCondition (V : Set LatticeVertex))
    (reveal : Configuration (squareLattice.induce (V : Set LatticeVertex)) →
      Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (C₀ : Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (E : Set (Configuration (squareLattice.induce (V : Set LatticeVertex)))) :
    (stableRecordOriginalLaw V θ ξ reveal hstable C₀).toMeasure E =
      (stableRecordRemainingLaw V θ ξ reveal hstable C₀).toMeasure
        {A | A.val ∪ (Exploration.revealRecordConfiguration reveal C₀).val ∈ E} := by
  rw [← stable_record_restore_original_law V θ ξ reveal hstable C₀]
  rw [PMF.toMeasure_map_apply]
  · rfl
  · exact fun _ _ => MeasurableSpace.measurableSet_top
  · exact MeasurableSpace.measurableSet_top

end
end PottsContinuity.Thm3.Prop4
