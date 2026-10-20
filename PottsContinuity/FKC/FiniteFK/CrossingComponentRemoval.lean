-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/CrossingComponentRemoval.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ClusterComplementLaw
public import PottsContinuity.FKC.FiniteFK.Graph
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)
  (A : Configuration G) (s : V)

local instance removalOriginalEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance removalVertexDecidableEq : DecidableEq V := Classical.decEq _
local instance removalComplementEdgeFintype :
    Fintype ((G.induce (actualClusterComplementSet s A)).edgeSet) := Fintype.ofFinite _
local instance removalComplementGraphEdgeDecidableEq :
    DecidableEq (G.induce (actualClusterComplementSet s A)).edgeSet := Classical.decEq _
local instance removalComplementVertexFintype :
    Fintype (actualClusterComplementSet s A) := Fintype.ofFinite _
local instance removalComplementVertexDecidableEq :
    DecidableEq (actualClusterComplementSet s A) := Classical.decEq _
local instance removalClassicalDecidable {p : Prop} : Decidable p :=
  Classical.propDecidable p

omit [Finite V] in
theorem openGraph_adj_iff_openBond (K : SimpleGraph V) (D : Configuration K)
    (u v : V) :
    (openGraph K D).Adj u v ↔
      ∃ h : K.Adj u v, (⟨s(u, v), K.mem_edgeSet.mpr h⟩ : K.edgeSet) ∈ D := by
  constructor
  · intro h
    rcases (openGraph_adj K D u v).mp h with ⟨e, he, hev⟩
    have hadj : K.Adj u v := by
      exact K.mem_edgeSet.mp (hev ▸ e.property)
    refine ⟨hadj, ?_⟩
    have heq : e = ⟨s(u, v), K.mem_edgeSet.mpr hadj⟩ := Subtype.ext hev
    exact heq ▸ he
  · rintro ⟨h, he⟩
    apply (openGraph_adj K D u v).mpr
    exact (coe_mem_openEdges_iff K D ⟨s(u, v), K.mem_edgeSet.mpr h⟩).2 he

end
end PottsContinuity.FKC.FiniteFK
