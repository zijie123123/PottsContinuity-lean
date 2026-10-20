module

public import PottsContinuity.Thm3.Push.ActiveFrontierComparison
public import PottsContinuity.Thm3.Push.TwoArcAttachmentLabels
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.BD12
noncomputable section
local instance twoRevealCarrierEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- The literal original vertices incident to at least one recorded bond. -/
def revealIncidentVertices {V : Type*} (G : SimpleGraph V) (R : Configuration G) : Set V :=
  {u | ∃ e ∈ R, u ∈ e.val}

/-- Attachments of the active joint remaining graph to the left reveal. -/
abbrev twoRevealActiveLeftArc {V : Type*} (G : SimpleGraph V) (L R : Configuration G) :
    Set (unexaminedVertices G (L ∪ R)) :=
  Subtype.val ⁻¹' revealIncidentVertices G L

/-- Attachments of the active joint remaining graph to the right reveal. -/
abbrev twoRevealActiveRightArc {V : Type*} (G : SimpleGraph V) (L R : Configuration G) :
    Set (unexaminedVertices G (L ∪ R)) :=
  Subtype.val ⁻¹' revealIncidentVertices G R

/-- Exactly the two separately wired attachment arcs, retaining singleton
classes of every other active original vertex. -/
def twoRevealActiveBoundary {V : Type*} [Finite V] (G : SimpleGraph V)
    (L R : Configuration G)
    (hd : Disjoint (revealIncidentVertices G L) (revealIncidentVertices G R)) :
    BoundaryCondition (unexaminedVertices G (L ∪ R)) :=
  twoBlockBoundary (twoRevealActiveLeftArc G L R) (twoRevealActiveRightArc G L R)
    (hd.preimage Subtype.val)

/-- Omitting only vertices without remaining bonds preserves the exact
same-vertex remaining graph as an isolated extension. -/
theorem activeUnexaminedGraph_map_eq_edgeRestriction {V : Type*}
    (G : SimpleGraph V) (R : Configuration G) :
    (activeUnexaminedGraph G R).map (Function.Embedding.subtype _) = edgeRestriction G R := by
  apply le_antisymm (activeUnexaminedGraph_map_le_edgeRestriction G R)
  intro u v huv
  obtain ⟨hu,hv⟩ := edgeRestriction_adj_active G R huv
  exact (SimpleGraph.map_adj _ _ _ _).mpr ⟨⟨u,hu⟩,⟨v,hv⟩,huv,rfl,rfl⟩

/-- The active carrier deletes exactly the recorded original bonds, with
no additional hidden edge deletion at the omitted isolated vertices. -/
theorem activeUnexaminedGraph_removedEdges {V : Type*} [Finite V]
    (G : SimpleGraph V) (R : Configuration G) :
    subgraphRemovedEdges ((activeUnexaminedGraph G R).map (Function.Embedding.subtype _)) G = R := by
  classical
  ext e
  rw [mem_subgraphRemovedEdges,activeUnexaminedGraph_map_eq_edgeRestriction,edgeRestriction_edgeSet]
  simp only [Set.mem_sdiff,e.property,true_and,not_not,coe_mem_openEdges_iff]

/-- Every left arc vertex is a literal mixed attachment of the individual
left reveal, since it carries a bond outside BOTH reveals. -/
theorem twoRevealActiveLeftArc_mixed {V : Type*} (G : SimpleGraph V)
    (L R : Configuration G) (u : unexaminedVertices G (L ∪ R))
    (hu : u ∈ twoRevealActiveLeftArc G L R) :
    ∃ f ∈ L, ∃ g : G.edgeSet, g ∉ L ∧ u.val ∈ f.val ∧ u.val ∈ g.val := by
  obtain ⟨f,hf,huf⟩ := hu
  obtain ⟨g,hg,hug⟩ := u.property
  exact ⟨f,hf,g,(fun h => hg (Finset.mem_union_left _ h)),huf,hug⟩

/-- The corresponding exact individual-right mixed attachment statement. -/
theorem twoRevealActiveRightArc_mixed {V : Type*} (G : SimpleGraph V)
    (L R : Configuration G) (u : unexaminedVertices G (L ∪ R))
    (hu : u ∈ twoRevealActiveRightArc G L R) :
    ∃ f ∈ R, ∃ g : G.edgeSet, g ∉ R ∧ u.val ∈ f.val ∧ u.val ∈ g.val := by
  obtain ⟨f,hf,huf⟩ := hu
  obtain ⟨g,hg,hug⟩ := u.property
  exact ⟨f,hf,g,(fun h => hg (Finset.mem_union_right _ h)),huf,hug⟩

end
end PottsContinuity.Push
