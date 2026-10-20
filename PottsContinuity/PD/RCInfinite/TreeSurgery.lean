-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/TreeSurgery.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.RCInfinite.ConnectorEmbedding
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.PD.RCInfinite
open FK
noncomputable section
open scoped Classical

def boxExitSubembedding {n : ℕ} (exits : Fin 3 → BoxExit n)
    (hdistinct : Function.Injective (fun j => boxExitOutside (exits j)))
    (U : Finset (BoxExitCarrier n)) : U ↪ LatticeVertex where
  toFun := fun u => boxExitCarrierEmbedding exits hdistinct u.val
  inj' := by
    intro u v huv
    apply Subtype.ext
    exact (boxExitCarrierEmbedding exits hdistinct).injective huv

/-- The prescribed state is open precisely on the image of the chosen finite
connector tree. -/
def boxTreeEdgeState {V : Type*} (H : SimpleGraph V) (f : V ↪ LatticeVertex)
    (e : Edge) : Bool := decide (e.val ∈ (H.map f).edgeSet)

theorem mapped_connector_tree_le_surgery_graph {n : ℕ}
    (exits : Fin 3 → BoxExit n)
    (hdistinct : Function.Injective (fun j => boxExitOutside (exits j)))
    (U : Finset (BoxExitCarrier n)) (H : SimpleGraph (U : Set (BoxExitCarrier n)))
    (hHG : H ≤ (boxExitConnectorGraph n exits).induce (U : Set (BoxExitCarrier n)))
    (ω : LatticeConfiguration) :
    H.map (boxExitSubembedding exits hdistinct U) ≤
      rcInfiniteOpenGraph
        (setEdges (boxIncidentEdges n) (boxTreeEdgeState H (boxExitSubembedding exits hdistinct U)) ω) := by
  classical
  let f := boxExitSubembedding exits hdistinct U
  intro x y hxy
  obtain ⟨u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj f H x y).mp hxy
  have hbase : (boxExitConnectorGraph n exits).Adj u.val v.val := hHG huv
  have hadj := boxExitConnector_adj_lattice exits u.val v.val hbase
  have hinc := boxExitConnector_adj_incident_box exits u.val v.val hbase
  let e : Edge := ⟨s(boxExitCarrierVertex exits u.val,
    boxExitCarrierVertex exits v.val), squareLattice.mem_edgeSet.mpr hadj⟩
  have heF : e ∈ boxIncidentEdges n := by
    apply edge_incident_box_mem_boxIncidentEdges
    obtain ⟨x₀, hx₀, hxe⟩ := hinc
    refine ⟨x₀, hx₀, ?_⟩
    change x₀ ∈ s(boxExitCarrierVertex exits u.val,
      boxExitCarrierVertex exits v.val)
    exact (Sym2.mem_toFinset).mp hxe
  have heTree : e.val ∈ (H.map f).edgeSet := by
    have hmapAdj : (H.map f).Adj (f u) (f v) :=
      (SimpleGraph.map_adj f H (f u) (f v)).2 ⟨u, v, huv, rfl, rfl⟩
    change s(f u, f v) ∈ (H.map f).edgeSet
    exact (SimpleGraph.mem_edgeSet (H.map f)).2 hmapAdj
  rw [rcInfiniteOpenGraph_adj]
  refine ⟨squareLattice.mem_edgeSet.mpr hadj, ?_⟩
  change setEdges (boxIncidentEdges n) (boxTreeEdgeState H f) ω e = true
  simp [setEdges, heF, boxTreeEdgeState, heTree]

/-- Every open edge after the finite prescription is either a chosen tree edge
or an unchanged edge wholly outside the box. -/
theorem surgery_graph_le_tree_sup_exterior {n : ℕ}
    (exits : Fin 3 → BoxExit n)
    (hdistinct : Function.Injective (fun j => boxExitOutside (exits j)))
    (U : Finset (BoxExitCarrier n)) (H : SimpleGraph (U : Set (BoxExitCarrier n)))
    (ω : LatticeConfiguration) :
    rcInfiniteOpenGraph
        (setEdges (boxIncidentEdges n) (boxTreeEdgeState H (boxExitSubembedding exits hdistinct U)) ω) ≤
      H.map (boxExitSubembedding exits hdistinct U) ⊔ exteriorOpenGraph ω n := by
  classical
  let f := boxExitSubembedding exits hdistinct U
  let G := H.map f
  let ξ := boxTreeEdgeState H f
  intro x y hxy
  obtain ⟨he, hopen⟩ := (rcInfiniteOpenGraph_adj _ x y).mp hxy
  let e : Edge := ⟨s(x, y), he⟩
  by_cases heF : e ∈ boxIncidentEdges n
  · have hopenTree : ξ e = true := by
      change setEdges (boxIncidentEdges n) ξ ω e = true at hopen
      simpa [setEdges, heF] using hopen
    have heTree : e.val ∈ G.edgeSet := by
      simpa [ξ, boxTreeEdgeState, G, f] using hopenTree
    have hTreeAdj : G.Adj x y := (SimpleGraph.mem_edgeSet G).1 heTree
    exact (SimpleGraph.sup_adj G (exteriorOpenGraph ω n) x y).mpr (Or.inl hTreeAdj)
  · have hxout : x ∉ latticeBox (0, 0) n := by
      intro hx
      apply heF
      apply edge_incident_box_mem_boxIncidentEdges n e
      exact ⟨x, hx, by simp [e]⟩
    have hyout : y ∉ latticeBox (0, 0) n := by
      intro hy
      apply heF
      apply edge_incident_box_mem_boxIncidentEdges n e
      exact ⟨y, hy, by simp [e]⟩
    have hωopen : ω e = true := by
      change setEdges (boxIncidentEdges n) ξ ω e = true at hopen
      simpa [setEdges, heF] using hopen
    have hωadj : (rcInfiniteOpenGraph ω).Adj x y :=
      (rcInfiniteOpenGraph_adj ω x y).mpr ⟨he, hωopen⟩
    exact (SimpleGraph.sup_adj G (exteriorOpenGraph ω n) x y).mpr
      (Or.inr ((exteriorOpenGraph_adj ω n x y).mpr ⟨hωadj, hxout, hyout⟩))

end
end PottsContinuity.PD.RCInfinite
