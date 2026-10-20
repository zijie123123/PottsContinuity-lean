module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

@[expose] public section

namespace PottsContinuity.PlanarMixed

/-- Map the actual walk when all its own bonds are retained. No condition is
required on edges of the source graph that the walk does not use. -/
def retainedWalk {V W : Type*} {G : SimpleGraph V} (H : SimpleGraph W)
    (f : V → W) {a b : V} (p : G.Walk a b)
    (hret : ∀ {u v : V}, s(u,v) ∈ p.edges → H.Adj (f u) (f v)) :
    H.Walk (f a) (f b) := by
  let T := SimpleGraph.fromEdgeSet {e | e ∈ p.edges}
  have hre : ∀ e ∈ p.edges, e ∈ T.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      apply T.mem_edgeSet.mpr
      exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨he,(p.adj_of_mem_edges he).ne⟩
  let φ : T →g H := {
    toFun := f
    map_rel' := fun h => hret ((SimpleGraph.fromEdgeSet_adj _).mp h).1 }
  exact (p.transfer T hre).map φ

/-- The construction retains the complete vertex list, including endpoints
and repeated contacts. -/
theorem retainedWalk_support {V W : Type*} {G : SimpleGraph V} (H : SimpleGraph W)
    (f : V → W) {a b : V} (p : G.Walk a b)
    (hret : ∀ {u v : V}, s(u,v) ∈ p.edges → H.Adj (f u) (f v)) :
    (retainedWalk H f p hret).support = p.support.map f := by
  unfold retainedWalk
  rw [SimpleGraph.Walk.support_map,SimpleGraph.Walk.support_transfer]
  rfl

/-- Every edge is the original edge transported by the stated vertex map. -/
theorem retainedWalk_edges {V W : Type*} {G : SimpleGraph V} (H : SimpleGraph W)
    (f : V → W) {a b : V} (p : G.Walk a b)
    (hret : ∀ {u v : V}, s(u,v) ∈ p.edges → H.Adj (f u) (f v)) :
    (retainedWalk H f p hret).edges = p.edges.map (Sym2.map f) := by
  unfold retainedWalk
  rw [SimpleGraph.Walk.edges_map,SimpleGraph.Walk.edges_transfer]
  rfl

end PottsContinuity.PlanarMixed
