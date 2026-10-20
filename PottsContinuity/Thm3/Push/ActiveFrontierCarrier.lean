module

public import PottsContinuity.Thm3.Push.ActiveFrontierLocality
public import PottsContinuity.PD.FK.EdgeRestriction
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- Vertices incident to a genuinely unexamined original bond. Isolated
vertices of the deleted graph are excluded, rather than artificially wired. -/
def unexaminedVertices {V : Type*} (G : SimpleGraph V) (R : Configuration G) : Set V :=
  {v | ∃ f : G.edgeSet, f ∉ R ∧ v ∈ f.val}

/-- The actual graph of unexamined original bonds on its active vertices. -/
def activeUnexaminedGraph {V : Type*} (G : SimpleGraph V) (R : Configuration G) :
    SimpleGraph (unexaminedVertices G R) :=
  (edgeRestriction G R).induce (unexaminedVertices G R)

/-- Every unexamined edge has both endpoints in the active carrier. -/
theorem edgeRestriction_adj_active {V : Type*} (G : SimpleGraph V)
    (R : Configuration G) {u v : V} (huv : (edgeRestriction G R).Adj u v) :
    u ∈ unexaminedVertices G R ∧ v ∈ unexaminedVertices G R := by
  classical
  let f : G.edgeSet := ⟨s(u,v),G.mem_edgeSet.mpr (edgeRestriction_le G R huv)⟩
  have hf : f ∉ R := by
    intro hmem
    exact (SimpleGraph.deleteEdges_adj.mp huv).2 ((coe_mem_openEdges_iff G R f).mpr hmem)
  exact ⟨⟨f,hf,(Sym2.mem_iff').mpr (Or.inl rfl)⟩,
    ⟨f,hf,(Sym2.mem_iff').mpr (Or.inr rfl)⟩⟩

/-- Inclusion of the active graph into the original graph retains literal
vertices and literal original edges. -/
theorem activeUnexaminedGraph_map_le {V : Type*} (G : SimpleGraph V)
    (R : Configuration G) :
    (activeUnexaminedGraph G R).map (Function.Embedding.subtype _) ≤ G := by
  intro u v huv
  obtain ⟨x,y,hxy,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  exact edgeRestriction_le G R hxy

/-- Away from the proved wired frontier, the active graph is closed under
ALL neighbors in the reference rectangle. No random-domain containment is
assumed: mixed revealed/unrevealed incidence is already ruled out locally. -/
theorem active_filledFrontier_neighbor_closed (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h))
    (hA : A ∈ rectangleHorizontalCrossingEvent a w h)
    {x : unexaminedVertices (rectangleGraph a w h) (rectangleFilledTopReveal a w h A)}
    (hx : x.val ∉ filledFrontierWiredVertices a w h A)
    {y : RectangleVertex a w h} (hxy : (rectangleGraph a w h).Adj x.val y) :
    ∃ z : unexaminedVertices (rectangleGraph a w h) (rectangleFilledTopReveal a w h A),
      z.val = y ∧ (activeUnexaminedGraph (rectangleGraph a w h)
        (rectangleFilledTopReveal a w h A)).Adj x z := by
  classical
  obtain ⟨g,hg,hxg⟩ := x.property
  let f : (rectangleGraph a w h).edgeSet :=
    ⟨s(x.val,y),(rectangleGraph a w h).mem_edgeSet.mpr hxy⟩
  have hxf : x.val ∈ f.val := (Sym2.mem_iff').mpr (Or.inl rfl)
  have hf : f ∉ rectangleFilledTopReveal a w h A := by
    intro hmem
    exact hx (active_mixed_vertex_mem_frontier_wiring a w h A hA x.val f g hmem hg hxf hxg)
  have hdel : (edgeRestriction (rectangleGraph a w h)
      (rectangleFilledTopReveal a w h A)).Adj x.val y := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hxy,?_⟩
    intro hmem
    exact hf ((coe_mem_openEdges_iff _ _ f).mp hmem)
  exact ⟨⟨y,(edgeRestriction_adj_active _ _ hdel).2⟩,rfl,hdel⟩

end
end PottsContinuity.Push
