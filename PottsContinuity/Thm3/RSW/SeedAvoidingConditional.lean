module

public import PottsContinuity.Thm3.RSW.SeedAvoidingWitness
public import PottsContinuity.Thm3.RSW.SeedComplementFreeLaw
public import PottsContinuity.Thm3.RSW.InducedConfinedComparison

/-! # Conditional localization of a seed-separated confined witness -/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK Exploration
noncomputable section
variable {X : Type*} [Finite X] {G : SimpleGraph X}
local instance seedAvoidingConditionalEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance seedAvoidingConditionalEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace

/-- On each actual seed record a confined witness avoiding every seed has
probability at most its event probability in the full free reference window.
No disjointness of reference windows or numerical conditional bound is assumed. -/
theorem seedAvoidingConfinedWitness_record_probability_le
    (θ : Parameters) (S : Finset X) (W : Set X)
    (E : Set (Configuration G)) (hE : IsUpperSet E) (A₀ : Configuration G) :
    (((law G θ (BoundaryCondition.free ∅)).filter
      (revealRecordEvent (FKC.FiniteFK.actualMultiClusterReveal G S) A₀)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent (FKC.FiniteFK.actualMultiClusterReveal G S)
          (FKC.FiniteFK.actualMultiClusterReveal_consistent S) A₀]
        exact frozenStateEvent_support θ (BoundaryCondition.free ∅) _ _)).toMeasure
      (seedAvoidingConfinedWitnessEvent G S W E)).toReal ≤
    (measure (G.induce W) θ (BoundaryCondition.free ∅)
      {B | inducedConfigurationExtension W B ∈ E}).toReal := by
  let ξ : BoundaryCondition X := BoundaryCondition.free ∅
  let reveal := FKC.FiniteFK.actualMultiClusterReveal G S
  let C := FKC.FiniteFK.actualMultiClusterComplementSet G S A₀
  let hs : ∃ B ∈ revealRecordEvent reveal A₀, B ∈ (law G θ ξ).support := by
    rw [revealRecordEvent_eq_frozenStateEvent reveal
      (FKC.FiniteFK.actualMultiClusterReveal_consistent S) A₀]
    exact frozenStateEvent_support θ ξ _ _
  let ρ := (law G θ ξ).filter (revealRecordEvent reveal A₀) hs
  let T : Set (Configuration (G.induce C)) :=
    {B | inducedConfigurationExtension C B ∈ confinedWitnessEvent G W E}
  have hfree := law_filter_seedRecord_map_complement_free θ ξ S (by intro u hu; exact hu.elim) A₀
  change ρ.map (inducedConfigurationRestriction C) =
    law (G.induce C) θ (BoundaryCondition.free ∅) at hfree
  have hmap := congrArg (fun p : PMF (Configuration (G.induce C)) => p.toMeasure T) hfree
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    MeasurableSpace.measurableSet_top] at hmap
  have hsubset : ρ.toMeasure (seedAvoidingConfinedWitnessEvent G S W E) ≤
      ρ.toMeasure {A | inducedConfigurationRestriction C A ∈ T} := by
    apply ρ.toMeasure_mono MeasurableSpace.measurableSet_top
    intro A hA
    exact seedAvoidingConfinedWitness_erasure_of_record S W E A₀ A
      ((PMF.mem_support_filter_iff hs).mp hA.2).1 hA.1
  change (ρ.toMeasure (seedAvoidingConfinedWitnessEvent G S W E)).toReal ≤ _
  calc
    _ ≤ (ρ.toMeasure {A | inducedConfigurationRestriction C A ∈ T}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) hsubset
    _ = (measure (G.induce C) θ (BoundaryCondition.free ∅) T).toReal :=
      congrArg ENNReal.toReal hmap
    _ ≤ _ := free_induced_confinedWitness_probability_le θ C W E hE

end
end PottsContinuity.RSW
