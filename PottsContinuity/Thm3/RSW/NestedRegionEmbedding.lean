module

public import PottsContinuity.Thm3.RSW.InducedComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-! # Literal embeddings for an intersection inside an induced region -/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section
variable {X : Type*} [Finite X] {G : SimpleGraph X}

/-- A vertex of D whose ambient vertex lies in W embeds literally in W. -/
def nestedRegionEmbedding (D W : Set X) : {v : D | v.val ∈ W} ↪ W where
  toFun v := ⟨v.val.val,v.property⟩
  inj' := by
    intro u v h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : W => x.val) h

omit [Finite X] in
/-- Original adjacency is retained through the nested induced inclusion. -/
theorem nestedRegionEmbedding_map_le (D W : Set X) :
    ((G.induce D).induce {v : D | v.val ∈ W}).map (nestedRegionEmbedding D W) ≤
      G.induce W := by
  intro a b hab
  obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ a b).mp hab
  exact huv

omit [Finite X] in
/-- Restricting the W sample to D∩W and extending twice only removes actual
sampled bonds, with both subtype levels and the original edge map retained. -/
theorem nested_induced_extension_restriction_subset (D W : Set X)
    (A : Configuration (G.induce W)) :
    inducedConfigurationExtension D
      (inducedConfigurationExtension {v : D | v.val ∈ W}
        (embeddedConfigurationRestriction
          ((G.induce D).induce {v : D | v.val ∈ W}) (G.induce W)
          (nestedRegionEmbedding D W) (nestedRegionEmbedding_map_le D W) A)) ⊆
      inducedConfigurationExtension W A := by
  classical
  change embeddedConfigurationEmbedding _ _ _ _
    (embeddedConfigurationEmbedding _ _ _ _ _) ⊆ embeddedConfigurationEmbedding _ _ _ _ A
  simp only [embeddedConfigurationEmbedding_eq_map]
  intro e he
  obtain ⟨d,hd,rfl⟩ := Finset.mem_map.mp he
  obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hd
  have hbA := (mem_embeddedConfigurationRestriction _ _ (nestedRegionEmbedding D W)
    (nestedRegionEmbedding_map_le (G := G) D W) A b).mp hb
  refine Finset.mem_map.mpr ⟨embeddedEdgeEmbedding _ _ (nestedRegionEmbedding D W)
    (nestedRegionEmbedding_map_le (G := G) D W) b,hbA,?_⟩
  apply Subtype.ext
  simp only [embeddedEdgeEmbedding_coe]
  change Sym2.map Subtype.val (Sym2.map (nestedRegionEmbedding D W) b.val) =
    Sym2.map Subtype.val (Sym2.map Subtype.val b.val)
  rw [Sym2.map_map,Sym2.map_map]
  rfl

end
end PottsContinuity.RSW
