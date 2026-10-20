module

public import PottsContinuity.Thm3.RSW.RootedWitnessRecord

/-! # Confined witnesses outside every explored seed cluster -/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK Exploration
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance seedAvoidingWitnessEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance seedAvoidingWitnessEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- An actual witness whose ambient clusters stay in W and avoid all seeds.
This records geometric separation of clusters, without prescribing a circuit
selector or a second random interior. -/
def seedAvoidingConfinedWitnessEvent (G : SimpleGraph V) (S : Finset V)
    (W : Set V) (E : Set (Configuration G)) : Set (Configuration G) :=
  {A | ∃ B : Configuration G, B ⊆ A ∧ B ∈ E ∧
    ∀ e ∈ B, ∀ v ∈ e.val,
      (¬ FKC.FiniteFK.actualMultiClusterConnected G S A v) ∧
      ∀ z, ActualConnected G A v z → z ∈ W}

/-- On every attained seed record the separated witness survives the literal
edge erasure to its unexplored induced complement, together with confinement. -/
theorem seedAvoidingConfinedWitness_erasure_of_record
    (S : Finset V) (W : Set V) (E : Set (Configuration G))
    (A₀ A : Configuration G)
    (hr : A ∈ revealRecordEvent (FKC.FiniteFK.actualMultiClusterReveal G S) A₀)
    (hA : A ∈ seedAvoidingConfinedWitnessEvent G S W E) :
    inducedConfigurationErasure (FKC.FiniteFK.actualMultiClusterComplementSet G S A₀) A ∈
      confinedWitnessEvent G W E := by
  obtain ⟨B,hBA,hB,hsep⟩ := hA
  let C := FKC.FiniteFK.actualMultiClusterComplementSet G S A₀
  have hBC : B ⊆ inducedConfigurationErasure C A := by
    intro e he
    refine (mem_inducedConfigurationErasure C A e).mpr ⟨hBA he,?_⟩
    intro v hv
    change ¬ FKC.FiniteFK.actualMultiClusterConnected G S A₀ v
    intro hc
    exact (hsep e he v hv).1
      ((FKC.FiniteFK.actualMultiClusterConnected_iff_of_reveal_agreement
        S A₀ A hr.2 v).mpr hc)
  refine ⟨B,hBC,hB,?_⟩
  intro e he v hv z hz
  exact (hsep e he v hv).2 z
    (hz.mono (openGraph_mono (inducedConfigurationErasure_subset C A)))

end
end PottsContinuity.RSW
