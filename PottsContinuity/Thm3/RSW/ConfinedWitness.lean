module

public import PottsContinuity.Thm3.RSW.InducedComparison
public import PottsContinuity.Thm3.RSW.SeedComplementGeometry
public import PottsContinuity.Thm3.RSW.StoppingUpper

/-!
# Free localization of events with cluster-confined witnesses

The witness is a genuine subconfiguration of the sampled open bonds. Every
cluster incident to one of its bonds must stay in W. This is stronger than a
path being contained in W, and is the shielding supplied by a closed dual
screen. No monotonicity of the shielding condition is asserted.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK Exploration
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance confinedWitnessVertexFintype : Fintype V := Fintype.ofFinite V
local instance confinedWitnessEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace

/-- An event witnessed by actual open bonds whose entire ambient clusters
remain inside W. The witness may discard unrelated sampled bonds. -/
def confinedWitnessEvent (G : SimpleGraph V) (W : Set V)
    (E : Set (Configuration G)) : Set (Configuration G) :=
  {A | ∃ B : Configuration G, B ⊆ A ∧ B ∈ E ∧
    ∀ e ∈ B, ∀ v ∈ e.val, ∀ z, ActualConnected G A v z → z ∈ W}

/-- On an attained exterior-cluster record every confined witness survives
in its unexplored induced complement. -/
theorem confinedWitness_mem_erasure_of_record (W : Set V)
    (E : Set (Configuration G)) (hE : IsUpperSet E) (A₀ A : Configuration G)
    (hrecord : A ∈ revealRecordEvent
      (FKC.FiniteFK.wiredAvoidingClusterReveal G ∅ Wᶜ.toFinset) A₀)
    (hA : A ∈ confinedWitnessEvent G W E) :
    inducedConfigurationErasure
      (FKC.FiniteFK.wiredAvoidingComplementSet G ∅ Wᶜ.toFinset A₀) A ∈ E := by
  obtain ⟨B,hBA,hB,hconf⟩ := hA
  apply hE (b := inducedConfigurationErasure _ A) ?_ hB
  intro e he
  refine (mem_inducedConfigurationErasure _ A e).mpr ⟨hBA he, ?_⟩
  intro v hv
  have hclusters := FKC.FiniteFK.wiredAvoidingClusterSet_eq_of_record
    (W := (∅ : Set V)) Wᶜ.toFinset A₀ A hrecord
  have hmem := confinedCluster_mem_exteriorSeedComplement W A v (hconf e he v hv)
  change v ∉ FKC.FiniteFK.wiredAvoidingClusterSet G ∅ Wᶜ.toFinset A₀
  rw [← hclusters]
  exact hmem

/-- Recordwise localization into the full free region W. Neither the record
nor the witness is selected from an unattained conditioning event. -/
theorem confinedWitness_record_probability_le (θ : Parameters) (W : Set V)
    (E : Set (Configuration G)) (hE : IsUpperSet E) (A₀ : Configuration G) :
    (((law G θ (BoundaryCondition.free Wᶜ)).filter
      (revealRecordEvent (FKC.FiniteFK.wiredAvoidingClusterReveal G ∅ Wᶜ.toFinset) A₀)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent
          (FKC.FiniteFK.wiredAvoidingClusterReveal G ∅ Wᶜ.toFinset)
          (fun A B h => FKC.FiniteFK.wiredAvoidingClusterReveal_consistent
            (∅ : Set V) Wᶜ.toFinset A B h) A₀]
        exact frozenStateEvent_support θ (BoundaryCondition.free Wᶜ) _ _)).toMeasure
          (confinedWitnessEvent G W E)).toReal ≤
      (measure (G.induce W) θ (BoundaryCondition.free ∅)
        {B | inducedConfigurationExtension W B ∈ E}).toReal := by
  let ξ := BoundaryCondition.free Wᶜ
  let reveal := FKC.FiniteFK.wiredAvoidingClusterReveal G ∅ Wᶜ.toFinset
  let C := FKC.FiniteFK.wiredAvoidingComplementSet G ∅ Wᶜ.toFinset A₀
  let hs : ∃ B ∈ revealRecordEvent reveal A₀, B ∈ (law G θ ξ).support := by
    rw [revealRecordEvent_eq_frozenStateEvent reveal
      (fun A B h => FKC.FiniteFK.wiredAvoidingClusterReveal_consistent
        (∅ : Set V) Wᶜ.toFinset A B h) A₀]
    exact frozenStateEvent_support θ ξ _ _
  let ρ := (law G θ ξ).filter (revealRecordEvent reveal A₀) hs
  let S : Set (Configuration (G.induce C)) :=
    {B | inducedConfigurationExtension C B ∈ E}
  have hmap := congrArg (fun p : PMF (Configuration (G.induce C)) => p.toMeasure S)
    (law_filter_boundarySeedRecord_map_complement_eq_free_allq θ ξ A₀)
  change (ρ.map (inducedConfigurationRestriction C)).toMeasure S =
    (measure (G.induce C) θ (BoundaryCondition.free ∅) S) at hmap
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    MeasurableSpace.measurableSet_top] at hmap
  have hsubset : ρ.toMeasure (confinedWitnessEvent G W E) ≤
      ρ.toMeasure {A | inducedConfigurationRestriction C A ∈ S} := by
    apply ρ.toMeasure_mono MeasurableSpace.measurableSet_top
    intro A hA
    exact confinedWitness_mem_erasure_of_record W E hE A₀ A
      ((PMF.mem_support_filter_iff hs).mp hA.2).1 hA.1
  change (ρ.toMeasure (confinedWitnessEvent G W E)).toReal ≤ _
  calc
    _ ≤ (ρ.toMeasure {A | inducedConfigurationRestriction C A ∈ S}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) hsubset
    _ = (measure (G.induce C) θ (BoundaryCondition.free ∅) S).toReal :=
      congrArg ENNReal.toReal hmap
    _ ≤ _ := free_induced_event_probability_mono θ C W
      (exteriorSeedComplement_subset W A₀) E hE

/-- The free localization bound for any increasing event with a confined
witness. This is a finite-graph statement, with no planar or critical input. -/
theorem free_confinedWitness_probability_le (θ : Parameters) (W : Set V)
    (E : Set (Configuration G)) (hE : IsUpperSet E) :
    (measure G θ (BoundaryCondition.free ∅) (confinedWitnessEvent G W E)).toReal ≤
      (measure (G.induce W) θ (BoundaryCondition.free ∅)
        {B | inducedConfigurationExtension W B ∈ E}).toReal := by
  have h := stopped_event_upper_of_record_bounds θ (BoundaryCondition.free Wᶜ)
    (FKC.FiniteFK.wiredAvoidingClusterReveal G ∅ Wᶜ.toFinset)
    (fun A B h => FKC.FiniteFK.wiredAvoidingClusterReveal_consistent
      (∅ : Set V) Wᶜ.toFinset A B h)
    (confinedWitnessEvent G W E)
    (measure (G.induce W) θ (BoundaryCondition.free ∅)
      {B | inducedConfigurationExtension W B ∈ E}).toReal
    (fun A₀ => confinedWitness_record_probability_le θ W E hE A₀)
  have hlaw : law G θ (BoundaryCondition.free ∅) = law G θ (BoundaryCondition.free Wᶜ) :=
    law_eq_of_boundary_partition_eq θ _ _ rfl
  change ((law G θ (BoundaryCondition.free ∅)).toMeasure _).toReal ≤ _
  rw [hlaw]
  exact h

end
end PottsContinuity.RSW
