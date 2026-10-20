module

public import PottsContinuity.BD12.GraphInnerPartition
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-! Literal induced-subgraph restriction of a sampled finite configuration.
The open graph is exactly the induced outer open graph. -/

@[expose] public section

namespace PottsContinuity.BD12
open FKC.FiniteFK
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V) (S : Set V)

/-- Inclusion of the actual induced vertex carrier. -/
def inducedVertexInclusion : S ↪ V := Function.Embedding.subtype _

omit [Finite V] in
theorem inducedVertexInclusion_map_le : (G.induce S).map (inducedVertexInclusion S) ≤ G :=
  SimpleGraph.map_comap_le _ _

/-- Read all and only original edges of the induced subgraph. -/
def inducedConfigurationRestriction (A : Configuration G) : Configuration (G.induce S) :=
  embeddedConfigurationRestriction (G.induce S) G (inducedVertexInclusion S)
    (inducedVertexInclusion_map_le G S) A

end
end PottsContinuity.BD12
