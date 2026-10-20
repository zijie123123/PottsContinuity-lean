module

public import PottsContinuity.Thm3.RSW.InducedConfiguration
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.Real

/-! # Increasing events under enlargement of an induced free region -/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}

/-- Free induced laws increase with the vertex region, for every increasing
ambient event read after extension by closed edges. -/
theorem free_induced_event_probability_mono (θ : Parameters)
    (C W : Set V) (hCW : C ⊆ W)
    (E : Set (Configuration G)) (hE : IsUpperSet E) :
    (measure (G.induce C) θ (BoundaryCondition.free ∅)
      {B | inducedConfigurationExtension C B ∈ E}).toReal ≤
    (measure (G.induce W) θ (BoundaryCondition.free ∅)
      {B | inducedConfigurationExtension W B ∈ E}).toReal := by
  classical
  let f : C ↪ W := ⟨fun v => ⟨v.val, hCW v.property⟩,
    fun a b h => Subtype.ext (congrArg (fun z : W => z.val) h)⟩
  have hmap : (G.induce C).map f ≤ G.induce W := by
    intro a b hab
    obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj f _ a b).mp hab
    exact huv
  let S : Set (Configuration (G.induce C)) :=
    {B | inducedConfigurationExtension C B ∈ E}
  have hS : IsUpperSet S := hE.preimage (inducedConfigurationExtension_monotone C)
  have hcmp := embedded_free_probability_le (G.induce C) (G.induce W) f hmap θ S hS
  refine hcmp.trans (measureReal_mono ?_)
  intro B hB
  apply hE (b := inducedConfigurationExtension W B) ?_ hB
  change embeddedConfigurationEmbedding _ _ _ _ _ ⊆ embeddedConfigurationEmbedding _ _ _ _ B
  simp only [embeddedConfigurationEmbedding_eq_map]
  intro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp he
  have hdB := (mem_embeddedConfigurationRestriction _ _ f hmap B d).mp hd
  refine Finset.mem_map.mpr ⟨embeddedEdgeEmbedding _ _ f hmap d, hdB, ?_⟩
  apply Subtype.ext
  simp only [embeddedEdgeEmbedding_coe]
  change Sym2.map Subtype.val (Sym2.map f d.val) = Sym2.map Subtype.val d.val
  rw [Sym2.map_map]
  rfl

end
end PottsContinuity.RSW
