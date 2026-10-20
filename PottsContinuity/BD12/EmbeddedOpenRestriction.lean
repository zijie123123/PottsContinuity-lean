module

public import PottsContinuity.BD12.GraphInnerPartition
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Original open edges under an embedded finite graph restriction. This uses
only edge inclusion and actual sampled configurations, independently of the law. -/

@[expose] public section

namespace PottsContinuity.BD12
open FKC.FiniteFK
noncomputable section
variable {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)

omit [Finite V] [Finite W] in
/-- On an original inner edge, restriction reads exactly its outer sampled state. -/
theorem embeddedOpenRestriction_adj (A : Configuration H) (u v : V) (huv : G.Adj u v) :
    (openGraph G (embeddedConfigurationRestriction G H f hGH A)).Adj u v ↔
      (openGraph H A).Adj (f u) (f v) := by
  classical
  rw [openGraph_adj, openGraph_adj]
  let i := embeddedEdgeEmbedding G H f hGH
  have hmem (e : G.edgeSet) : e ∈ embeddedConfigurationRestriction G H f hGH A ↔ i e ∈ A :=
    mem_embeddedConfigurationRestriction G H f hGH A e
  constructor
  · rintro ⟨e, he, heval⟩
    refine ⟨i e, (hmem e).mp he, ?_⟩
    rw [embeddedEdgeEmbedding_coe, heval]
    rfl
  · rintro ⟨e, he, heval⟩
    let eI : G.edgeSet := ⟨s(u,v), huv⟩
    have hie : i eI = e := by
      apply Subtype.ext
      rw [embeddedEdgeEmbedding_coe, heval]
      rfl
    exact ⟨eI, (hmem eI).mpr (hie ▸ he), rfl⟩

omit [Finite V] [Finite W] in
/-- Every actual restricted connection is an actual outer connection along
the same embedded original edges. -/
theorem embeddedOpenRestriction_connected_map (A : Configuration H) {u v : V}
    (h : ActualConnected G (embeddedConfigurationRestriction G H f hGH A) u v) :
    ActualConnected H A (f u) (f v) := by
  let hom : openGraph G (embeddedConfigurationRestriction G H f hGH A) →g openGraph H A := {
    toFun := f
    map_rel' := by
      intro x y hxy
      exact (embeddedOpenRestriction_adj G H f hGH A x y
        ((openGraph_le G _) hxy)).mp hxy }
  exact h.map hom

end
end PottsContinuity.BD12
