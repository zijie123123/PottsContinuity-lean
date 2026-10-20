module

public import PottsContinuity.PlanarMixed.IntersectingCrosscuts

/-! Actual open paths under literal embedded restriction and active transport.
The adjacency characterization retains the source graph, so a connection
inside an embedded square is never replaced by unrestricted host connectivity.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK
noncomputable section

/-- The restricted open graph is exactly the source edges whose embedded
original bonds are open in the host. -/
theorem embeddedRestriction_openGraph_adj_iff {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (h : G.map f ≤ H)
    (K : Configuration H) (u v : V) :
    (openGraph G (embeddedConfigurationRestriction G H f h K)).Adj u v ↔
      G.Adj u v ∧ (openGraph H K).Adj (f u) (f v) := by
  constructor
  · intro huv
    have hG := openGraph_le G _ huv
    let e : G.edgeSet := ⟨s(u,v), G.mem_edgeSet.mpr hG⟩
    have he : e ∈ embeddedConfigurationRestriction G H f h K :=
      (coe_mem_openEdges_iff G _ e).mp ((openGraph_adj G _ u v).mp huv)
    have heK := (mem_embeddedConfigurationRestriction G H f h K e).mp he
    refine ⟨hG, (openGraph_adj H K (f u) (f v)).mpr ?_⟩
    exact ⟨embeddedEdgeEmbedding G H f h e, heK, rfl⟩
  · rintro ⟨hG, hH⟩
    let e : G.edgeSet := ⟨s(u,v), G.mem_edgeSet.mpr hG⟩
    have hedge : (embeddedEdgeEmbedding G H f h e).val = s(f u,f v) := rfl
    have heK : embeddedEdgeEmbedding G H f h e ∈ K :=
      (coe_mem_openEdges_iff H K _).mp (by rw [hedge]; exact (openGraph_adj H K _ _).mp hH)
    apply (openGraph_adj G _ u v).mpr
    exact ⟨e, (mem_embeddedConfigurationRestriction G H f h K e).mpr heK, rfl⟩

/-- Map a restricted sampled walk along the actual original vertex embedding. -/
def embeddedOpenRestrictionHom {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (h : G.map f ≤ H)
    (K : Configuration H) :
    openGraph G (embeddedConfigurationRestriction G H f h K) →g openGraph H K where
  toFun := f
  map_rel' := fun huv => ((embeddedRestriction_openGraph_adj_iff G H f h K _ _).mp huv).2

end
end PottsContinuity.PlanarMixed
