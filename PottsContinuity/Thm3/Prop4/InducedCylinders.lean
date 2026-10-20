module

public import PottsContinuity.PD.RCInfinite.SubgraphComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Original-edge cylinders under finite induced embeddings

Public generalization of the private restriction argument in
PD/RCInfinite/SubgraphComparison.lean. The embedding may be any inclusion
preserving the original lattice vertices, including the actual tilted interval.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.RCInfinite

noncomputable section

variable {S T : Finset (ℤ × ℤ)}

/-- Embedding an induced edge and then reading it on the plane preserves its
actual original unordered edge. -/
theorem induced_edge_embedding_compatible
    (f : (S : Set (ℤ × ℤ)) ↪ (T : Set (ℤ × ℤ)))
    (hf : ∀ v, (f v).val = v.val)
    (hmap : (finiteLatticeGraph S).map f ≤ finiteLatticeGraph T)
    (e : (finiteLatticeGraph S).edgeSet) :
    frozenEdgeEmbedding T (embeddedEdgeEmbedding (finiteLatticeGraph S) (finiteLatticeGraph T) f hmap e) =
      frozenEdgeEmbedding S e := by
  apply Subtype.ext
  change Sym2.map Subtype.val (Sym2.map f e.val) = Sym2.map Subtype.val e.val
  rw [Sym2.map_map]
  congr 1
  exact funext hf

/-- A supported all-open plane cylinder is transported exactly by restriction
of the actual sampled edge configuration. -/
theorem induced_openEvent_restriction_iff
    (f : (S : Set (ℤ × ℤ)) ↪ (T : Set (ℤ × ℤ))) (hf : ∀ v, (f v).val = v.val)
    (hmap : (finiteLatticeGraph S).map f ≤ finiteLatticeGraph T)
    (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (frozenEdgeEmbedding S))
    (A : Configuration (finiteLatticeGraph T)) :
    A ∈ finiteSubgraphOpenEvent T F ↔
      embeddedConfigurationRestriction (finiteLatticeGraph S) (finiteLatticeGraph T) f hmap A ∈
        finiteSubgraphOpenEvent S F := by
  constructor
  · intro hA e he
    obtain ⟨x,hx⟩ := hF e he
    obtain ⟨y,hy,hye⟩ := Finset.mem_map.mp (hA he)
    have hcompat := induced_edge_embedding_compatible f hf hmap x
    have hyx : embeddedEdgeEmbedding (finiteLatticeGraph S) (finiteLatticeGraph T) f hmap x = y :=
      (frozenEdgeEmbedding T).injective (hcompat.trans (hx.trans hye.symm))
    apply Finset.mem_map.mpr
    refine ⟨x,?_,hx⟩
    exact (mem_embeddedConfigurationRestriction _ _ _ _ A x).mpr (hyx ▸ hy)
  · intro hA e he
    obtain ⟨x,hx,hxe⟩ := Finset.mem_map.mp (hA he)
    refine Finset.mem_map.mpr ⟨embeddedEdgeEmbedding _ _ f hmap x,
      (mem_embeddedConfigurationRestriction _ _ _ _ A x).mp hx,?_⟩
    exact (induced_edge_embedding_compatible f hf hmap x).trans hxe

end

end PottsContinuity.Thm3.Prop4
