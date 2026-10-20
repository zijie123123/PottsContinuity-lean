module

public import PottsContinuity.Thm3.Push.ArcInternalEdgeErasure
public import PottsContinuity.PD.FK.SubgraphComparison

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12
noncomputable section
variable {V W : Type*}
local instance embeddedArcSmallEdgeEq (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _
local instance embeddedArcLargeEdgeEq (H : SimpleGraph W) : DecidableEq H.edgeSet := Classical.decEq _

/-- Original-edge restriction commutes with literal erasure of host bonds. -/
theorem embeddedConfigurationRestriction_sdiff (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V ↪ W) (hGH : G.map f ≤ H) (C R : Configuration H) :
    embeddedConfigurationRestriction G H f hGH (C \ R) =
      embeddedConfigurationRestriction G H f hGH C \
        embeddedConfigurationRestriction G H f hGH R := by
  classical
  ext e
  simp only [mem_embeddedConfigurationRestriction,Finset.mem_sdiff]

/-- A confined actual connection is unchanged by deleting host bonds whose
restrictions lie internally in either of its endpoint arcs. Host bonds not
in the confined graph need no path assumption. -/
theorem embedded_arcsConnection_sdiff_internal_edges [Finite V]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)
    (A B : Set V) (R : Configuration H)
    (hR : ∀ (u v : V) (huv : G.Adj u v),
      embeddedEdgeEmbedding G H f hGH ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ ∈ R →
        (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B))
    (C : Configuration H) :
    embeddedConfigurationRestriction G H f hGH (C \ R) ∈ arcsConnectionEvent G A B ↔
      embeddedConfigurationRestriction G H f hGH C ∈ arcsConnectionEvent G A B := by
  rw [embeddedConfigurationRestriction_sdiff]
  apply arcsConnectionEvent_sdiff_internal_edges
  intro u v huv he
  exact hR u v huv ((mem_embeddedConfigurationRestriction G H f hGH R _).mp he)

end
end PottsContinuity.Push
