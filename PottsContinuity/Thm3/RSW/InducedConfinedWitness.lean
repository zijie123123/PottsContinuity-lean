module

public import PottsContinuity.Thm3.RSW.ConfinedWitness

/-! # Transport cluster-confined witnesses through literal induced extensions -/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance inducedConfinedWitnessEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

omit [Finite V] in
/-- Every endpoint of an extended induced bond belongs to the induced region. -/
theorem inducedExtension_edge_endpoints (D : Set V)
    (A : Configuration (G.induce D)) (e : G.edgeSet)
    (he : e ∈ inducedConfigurationExtension D A) :
    ∀ v ∈ e.val, v ∈ D := by
  change e ∈ embeddedConfigurationEmbedding _ _ _ _ A at he
  rw [embeddedConfigurationEmbedding_eq_map] at he
  obtain ⟨d,hd,rfl⟩ := Finset.mem_map.mp he
  intro v hv
  rw [embeddedEdgeEmbedding_coe] at hv
  change v ∈ Sym2.map (inducedVertexEmbedding D) d.val at hv
  rw [Sym2.mem_map] at hv
  obtain ⟨u,hu,rfl⟩ := hv
  exact u.property

omit [Finite V] in
/-- A subconfiguration of an induced extension is unchanged by erasing to
that same induced region. No sampled bonds are inserted by this identity. -/
theorem inducedErasure_eq_of_subset_extension (D : Set V)
    (A : Configuration (G.induce D)) (B : Configuration G)
    (hBA : B ⊆ inducedConfigurationExtension D A) :
    inducedConfigurationErasure D B = B := by
  apply Finset.Subset.antisymm (inducedConfigurationErasure_subset D B)
  intro e he
  exact (mem_inducedConfigurationErasure D B e).mpr
    ⟨he,inducedExtension_edge_endpoints D A e (hBA he)⟩

omit [Finite V] in
/-- A confined ambient witness supported on an induced extension pulls back
to a confined witness for the actual induced sampled graph. -/
theorem confinedWitness_extension_pullback (D W : Set V)
    (E : Set (Configuration G)) (A : Configuration (G.induce D))
    (hA : inducedConfigurationExtension D A ∈ confinedWitnessEvent G W E) :
    A ∈ confinedWitnessEvent (G.induce D) {v : D | v.val ∈ W}
      {B | inducedConfigurationExtension D B ∈ E} := by
  obtain ⟨B,hBA,hB,hconf⟩ := hA
  let B' := inducedConfigurationRestriction D B
  have hext : inducedConfigurationExtension D B' = B :=
    inducedErasure_eq_of_subset_extension D A B hBA
  have hsub : B' ⊆ A := by
    have hh := embeddedConfigurationRestriction_monotone (G.induce D) G
      (inducedVertexEmbedding D) (inducedVertexEmbedding_map_le D) hBA
    simpa only [B',inducedConfigurationRestriction,inducedConfigurationExtension,
      embeddedConfigurationRestriction_embedding] using hh
  refine ⟨B',hsub,?_,?_⟩
  · change inducedConfigurationExtension D B' ∈ E
    rw [hext]
    exact hB
  · intro e he v hv z hz
    let f := inducedVertexEmbedding D
    let hmap := inducedVertexEmbedding_map_le (G := G) D
    let eG := embeddedEdgeEmbedding (G.induce D) G f hmap e
    have heG : eG ∈ B :=
      (mem_embeddedConfigurationRestriction (G.induce D) G f hmap B e).mp he
    have hvG : v.val ∈ eG.val := by
      rw [embeddedEdgeEmbedding_coe]
      change v.val ∈ Sym2.map f e.val
      rw [Sym2.mem_map]
      exact ⟨v,hv,rfl⟩
    have hz' : ActualConnected G (inducedConfigurationExtension D A) v.val z.val := by
      apply embedded_restriction_actualConnected_mono f hmap (inducedConfigurationExtension D A)
      simpa only [f,hmap,inducedConfigurationExtension,embeddedConfigurationRestriction_embedding] using hz
    exact hconf eG heG v.val hvG z.val hz'

end
end PottsContinuity.RSW
