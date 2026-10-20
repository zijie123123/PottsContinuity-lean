module

public import PottsContinuity.Thm3.RSW.ConfinedWitness

/-! # Open graph and confined witnesses after induced edge erasure -/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}

omit [Finite V] in
/-- Closing every bond outside W gives exactly the original open adjacency
between vertices that both belong to W. -/
theorem openGraph_inducedConfigurationErasure_adj (W : Set V)
    (A : Configuration G) (u v : V) :
    (openGraph G (inducedConfigurationErasure W A)).Adj u v ↔
      (openGraph G A).Adj u v ∧ u ∈ W ∧ v ∈ W := by
  constructor
  · intro huv
    obtain ⟨e,he,hev⟩ := (openGraph_adj G _ u v).mp huv
    obtain ⟨heA,hW⟩ := (mem_inducedConfigurationErasure W A e).mp he
    exact ⟨(openGraph_adj G A u v).mpr ⟨e,heA,hev⟩,
      hW u (by simp [hev]), hW v (by simp [hev])⟩
  · rintro ⟨huv,hu,hv⟩
    obtain ⟨e,he,hev⟩ := (openGraph_adj G A u v).mp huv
    apply (openGraph_adj G _ u v).mpr
    refine ⟨e,(mem_inducedConfigurationErasure W A e).mpr ⟨he,?_⟩,hev⟩
    intro z hz
    rw [hev] at hz
    rcases (Sym2.mem_iff').mp hz with rfl | rfl
    · exact hu
    · exact hv

omit [Finite V] in
/-- If an event is witnessed by the restriction to U, and every ambient
cluster from U is confined to W, then it has a cluster-confined witness in W.
This is purely deterministic; E is not required to be increasing here. -/
theorem confinedWitness_of_inner_shield (U W : Set V)
    (E : Set (Configuration G)) (A : Configuration G)
    (hE : inducedConfigurationErasure U A ∈ E)
    (hshield : ∀ v ∈ U, ∀ z, ActualConnected G A v z → z ∈ W) :
    A ∈ confinedWitnessEvent G W E := by
  refine ⟨inducedConfigurationErasure U A,
    inducedConfigurationErasure_subset U A, hE, ?_⟩
  intro e he v hv z hz
  exact hshield v (((mem_inducedConfigurationErasure U A e).mp he).2 v hv) z hz

end
end PottsContinuity.RSW
