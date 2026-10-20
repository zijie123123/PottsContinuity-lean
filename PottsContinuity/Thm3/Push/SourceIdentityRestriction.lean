module

public import PottsContinuity.PD.FK.SubgraphComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.Push
open PD.FK
noncomputable section

/-- The identity embedding retains exactly the original graph. -/
theorem sourceIdentity_map_le {V : Type*} (G : SimpleGraph V) :
    G.map (Function.Embedding.refl V) ≤ G := by
  change G.map id ≤ G
  rw [SimpleGraph.map_id]

/-- Literal restriction along the identity reads the original sampled state. -/
theorem embeddedConfigurationRestriction_sourceIdentity {V : Type*}
    (G : SimpleGraph V) (A : Configuration G) :
    embeddedConfigurationRestriction G G (Function.Embedding.refl V) (sourceIdentity_map_le G) A = A := by
  classical
  ext e
  rw [mem_embeddedConfigurationRestriction]
  have he : embeddedEdgeEmbedding G G (Function.Embedding.refl V) (sourceIdentity_map_le G) e = e := by
    apply Subtype.ext
    change Sym2.map id e.val = e.val
    exact congr_fun Sym2.map_id e.val
  rw [he]

end
end PottsContinuity.Push
