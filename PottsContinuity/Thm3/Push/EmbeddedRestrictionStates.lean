module

public import PottsContinuity.Thm3.Push.RemainingRestore
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance embeddedStatesEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Literal composition of two original graph inclusions. -/
theorem graph_map_le_embedding_trans {U V W : Type*}
    (K : SimpleGraph U) (H : SimpleGraph V) (G : SimpleGraph W)
    (g : U ↪ V) (f : V ↪ W) (hKH : K.map g ≤ H) (hHG : H.map f ≤ G) :
    K.map (g.trans f) ≤ G := by
  intro x y hxy
  obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp hxy
  apply hHG
  exact (SimpleGraph.map_adj _ _ _ _).mpr
    ⟨g u,g v,hKH ((SimpleGraph.map_adj _ _ _ _).mpr ⟨u,v,huv,rfl,rfl⟩),rfl,rfl⟩

/-- Reading genuine original bond states commutes with successive graph
inclusions. This does not alter either boundary partition. -/
theorem embeddedConfigurationRestriction_comp {U V W : Type*}
    (K : SimpleGraph U) (H : SimpleGraph V) (G : SimpleGraph W)
    (g : U ↪ V) (f : V ↪ W) (hKH : K.map g ≤ H) (hHG : H.map f ≤ G)
    (A : Configuration G) :
    embeddedConfigurationRestriction K G (g.trans f)
      (graph_map_le_embedding_trans K H G g f hKH hHG) A =
    embeddedConfigurationRestriction K H g hKH (embeddedConfigurationRestriction H G f hHG A) := by
  classical
  ext e
  simp only [mem_embeddedConfigurationRestriction]
  have he : embeddedEdgeEmbedding K G (g.trans f)
      (graph_map_le_embedding_trans K H G g f hKH hHG) e =
      embeddedEdgeEmbedding H G f hHG (embeddedEdgeEmbedding K H g hKH e) := by
    apply Subtype.ext
    erw [embeddedEdgeEmbedding_coe,embeddedEdgeEmbedding_coe,embeddedEdgeEmbedding_coe]
    change Sym2.map (fun x => f (g x)) e.val = Sym2.map f (Sym2.map g e.val)
    rw [Sym2.map_map]
    rfl
  rw [he]

/-- Agreement on lifted original record bonds restricts to EXACT agreement
on the inner recorded states, including closed states. -/
theorem embedded_record_agreement_restrict {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)
    (R : Configuration G) (A B : Configuration H)
    (hrecord : B ∩ R.map (embeddedEdgeEmbedding G H f hGH) =
      A ∩ R.map (embeddedEdgeEmbedding G H f hGH)) :
    embeddedConfigurationRestriction G H f hGH B ∩ R =
      embeddedConfigurationRestriction G H f hGH A ∩ R := by
  classical
  ext e
  have hstates := Finset.ext_iff.mp hrecord (embeddedEdgeEmbedding G H f hGH e)
  simpa only [Finset.mem_inter,Finset.mem_map',mem_embeddedConfigurationRestriction] using hstates

/-- Restoration preserves every actual bond in ANY embedded unexamined
subgraph, without requiring that the embedding be induced. -/
theorem embedded_restriction_restore_remaining {U V : Type*}
    (K : SimpleGraph U) (G : SimpleGraph V) (R : Configuration G)
    (j : U ↪ V) (hKG : K.map j ≤ edgeRestriction G R)
    (F : RemovedConfiguration G R) (C : Configuration (edgeRestriction G R)) :
    embeddedConfigurationRestriction K G j (hKG.trans (edgeRestriction_le G R))
      (restoreRemainingConfiguration G R F C) =
    embeddedConfigurationRestriction K (edgeRestriction G R) j hKG C := by
  classical
  ext e
  rw [mem_embeddedConfigurationRestriction,mem_embeddedConfigurationRestriction]
  let g := embeddedEdgeEmbedding K (edgeRestriction G R) j hKG e
  let f := embeddedEdgeEmbedding K G j (hKG.trans (edgeRestriction_le G R)) e
  have hgf : edgeRestrictionEdgeEmbedding G R g=f := Subtype.ext rfl
  have hfR : f ∉ R := by
    have hnot := (edgeRestrictionEdgeEquiv G R g).property
    change edgeRestrictionEdgeEmbedding G R g ∉ R at hnot
    simpa only [hgf] using hnot
  have hfF : f ∉ F.val := fun hmem => hfR (F.property hmem)
  change f ∈ (edgeRestrictionConfigurationEquiv G R C).val ∪ F.val ↔ g ∈ C
  rw [Finset.mem_union,or_iff_left hfF,edgeRestrictionConfigurationEquiv_val,← hgf]
  exact Finset.mem_map' _

end
end PottsContinuity.Push
