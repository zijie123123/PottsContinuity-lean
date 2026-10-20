module

public import PottsContinuity.Thm3.RSW.MultiSeedComplementLaw
public import PottsContinuity.Thm3.RSW.ConfinedWitness

/-! # Seed-rooted confined witnesses are determined by the complete record -/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK Exploration
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance rootedWitnessRecordEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance rootedWitnessRecordEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- The complete seed-cluster record preserves each individual connection
from every seed, rather than merely membership in the union of seed clusters. -/
theorem seedRecord_connection_iff
    (S : Finset V) (A₀ A : Configuration G)
    (hr : A ∈ revealRecordEvent (FKC.FiniteFK.actualMultiClusterReveal G S) A₀)
    (s : V) (hs : s ∈ S) (v : V) :
    ActualConnected G A s v ↔ ActualConnected G A₀ s v := by
  have hsub := FKC.FiniteFK.actualClusterReveal_subset_multi (G := G) S A₀ hs
  have hag : A ∩ FKC.FiniteFK.actualClusterReveal G s A₀ =
      A₀ ∩ FKC.FiniteFK.actualClusterReveal G s A₀ := by
    ext e
    have heq := Finset.ext_iff.mp hr.2 e
    simp only [Finset.mem_inter] at heq ⊢
    exact ⟨fun h => ⟨(heq.mp ⟨h.1,hsub h.2⟩).1,h.2⟩,
      fun h => ⟨(heq.mpr ⟨h.1,hsub h.2⟩).1,h.2⟩⟩
  exact FKC.FiniteFK.actualConnected_iff_of_reveal_agreement G s A₀ A hag v

/-- A confined increasing-event witness whose event depends only on bonds
inside the seed set is measurable in the complete actual seed-cluster record.
The confinement region need not lie in the seed set or avoid another region. -/
theorem rooted_confinedWitnessEvent_seedRecord_iff
    (S : Finset V) (W : Set V) (E : Set (Configuration G))
    (hrooted : ∀ B : Configuration G,
      B ∈ E ↔ inducedConfigurationErasure (S : Set V) B ∈ E)
    (A₀ A : Configuration G)
    (hr : A ∈ revealRecordEvent (FKC.FiniteFK.actualMultiClusterReveal G S) A₀) :
    A ∈ confinedWitnessEvent G W E ↔ A₀ ∈ confinedWitnessEvent G W E := by
  have hforward (A₀ A : Configuration G)
      (hr : A ∈ revealRecordEvent (FKC.FiniteFK.actualMultiClusterReveal G S) A₀)
      (hA₀ : A₀ ∈ confinedWitnessEvent G W E) : A ∈ confinedWitnessEvent G W E := by
    obtain ⟨B,hBA,hB,hconf⟩ := hA₀
    let D := inducedConfigurationErasure (S : Set V) B
    have hDS : ∀ e ∈ D, ∀ v ∈ e.val, v ∈ S := by
      intro e he v hv
      exact ((mem_inducedConfigurationErasure (S : Set V) B e).mp he).2 v hv
    have hDB : D ⊆ B := inducedConfigurationErasure_subset _ _
    refine ⟨D,?_,(hrooted B).mp hB,?_⟩
    · intro e he
      obtain ⟨⟨u,v⟩,hrep⟩ := Quot.exists_rep e.val
      have hev : e.val = s(u,v) := hrep.symm
      have hu : u ∈ e.val := by simp [hev]
      have heR : e ∈ FKC.FiniteFK.actualMultiClusterReveal G S A₀ := by
        rw [FKC.FiniteFK.actualMultiClusterReveal_mem_iff]
        exact ⟨u,hu,u,hDS e he u hu,SimpleGraph.Reachable.refl u⟩
      have heq := Finset.ext_iff.mp hr.2 e
      simp only [Finset.mem_inter] at heq
      exact (heq.mpr ⟨hBA (hDB he),heR⟩).1
    · intro e he v hv z hz
      exact hconf e (hDB he) v hv z
        ((seedRecord_connection_iff S A₀ A hr v (hDS e he v hv) z).mp hz)
  have hrev : A₀ ∈ revealRecordEvent (FKC.FiniteFK.actualMultiClusterReveal G S) A := by
    refine ⟨hr.1.symm,?_⟩
    rw [hr.1]
    exact hr.2.symm
  exact ⟨hforward A A₀ hrev,hforward A₀ A hr⟩

end
end PottsContinuity.RSW
