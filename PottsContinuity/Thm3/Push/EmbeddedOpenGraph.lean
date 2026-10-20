module

public import PottsContinuity.PD.FK.SubgraphComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.Push
open PD.FK
noncomputable section

/-- An induced graph embedding preserves exactly the original open
adjacencies after literal restriction of the host edge states. -/
theorem embeddedRestriction_open_adj_iff {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)
    (hind : ∀ u v, H.Adj (f u) (f v) ↔ G.Adj u v)
    (C : Configuration H) (u v : V) :
    (openGraph G (embeddedConfigurationRestriction G H f hGH C)).Adj u v ↔
      (openGraph H C).Adj (f u) (f v) := by
  classical
  constructor
  · intro huv
    rw [openGraph_adj] at huv ⊢
    obtain ⟨e,he,hev⟩ := huv
    refine ⟨embeddedEdgeEmbedding G H f hGH e,
      (mem_embeddedConfigurationRestriction G H f hGH C e).mp he,?_⟩
    change Sym2.map f e.val = s(f u,f v)
    rw [hev]
    rfl
  · intro huv
    have hsmall : G.Adj u v := (hind u v).mp ((openGraph_le H C) huv)
    let e : G.edgeSet := ⟨s(u,v),G.mem_edgeSet.mpr hsmall⟩
    rw [openGraph_adj] at huv ⊢
    obtain ⟨d,hd,hdv⟩ := huv
    have hde : embeddedEdgeEmbedding G H f hGH e = d := by
      apply Subtype.ext
      change Sym2.map f s(u,v) = d.val
      exact hdv.symm
    exact ⟨e,(mem_embeddedConfigurationRestriction G H f hGH C e).mpr (hde ▸ hd),rfl⟩

/-- The actual open graph of a restricted induced domain embeds into the
sampled host open graph, retaining the same vertex map. -/
def embeddedRestrictionOpenEmbedding {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)
    (hind : ∀ u v, H.Adj (f u) (f v) ↔ G.Adj u v) (C : Configuration H) :
    openGraph G (embeddedConfigurationRestriction G H f hGH C) ↪g openGraph H C where
  toEmbedding := f
  map_rel_iff' := fun {u v} => (embeddedRestriction_open_adj_iff G H f hGH hind C u v).symm

end
end PottsContinuity.Push
