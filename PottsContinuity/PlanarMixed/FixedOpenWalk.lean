module

public import PottsContinuity.PD.FK.Graph
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK

/-- A fixed geometric path becomes an open walk when every one of its bonds
is present in the sampled open-edge set. No other bonds are requested. -/
def fixedOpenWalk {V : Type*} (G : SimpleGraph V) (C : Configuration G)
    {a b : V} (p : G.Walk a b)
    (hopen : ∀ e ∈ p.edges, e ∈ openEdges G C) : (openGraph G C).Walk a b :=
  p.transfer (openGraph G C) (fun e he => by rw [openGraph_edgeSet]; exact hopen e he)

/-- The open lift has exactly the original vertex list. -/
theorem fixedOpenWalk_support {V : Type*} (G : SimpleGraph V) (C : Configuration G)
    {a b : V} (p : G.Walk a b) (hopen : ∀ e ∈ p.edges, e ∈ openEdges G C) :
    (fixedOpenWalk G C p hopen).support = p.support :=
  SimpleGraph.Walk.support_transfer _ _

end PottsContinuity.PlanarMixed
