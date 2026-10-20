module

public import PottsContinuity.Thm3.Push.TwoRevealCrossingSegment
public import PottsContinuity.PlanarMixed.OmegaInterfaces
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.BD12 PottsContinuity.PlanarMixed
noncomputable section
local instance twoRevealRestrictionEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Every actual crossing between the exterior vertex sets gives an actual
connection between the attachment arcs in the exact remaining-edge graph. -/
theorem twoReveal_connection_restricts_to_active_arcs {V : Type*} [Finite V]
    (G : SimpleGraph V) (L R : Configuration G)
    (hd : Disjoint (revealIncidentVertices G L) (revealIncidentVertices G R))
    (C : Configuration G) {u v : V} (p : (openGraph G C).Walk u v)
    (hu : u ∈ revealIncidentVertices G L) (hv : v ∈ revealIncidentVertices G R) :
    embeddedConfigurationRestriction (activeUnexaminedGraph G (L ∪ R)) G
      (Function.Embedding.subtype _) (activeUnexaminedGraph_map_le G (L ∪ R)) C ∈
      arcsConnectionEvent _ (twoRevealActiveLeftArc G L R) (twoRevealActiveRightArc G L R) := by
  obtain ⟨x,hx,y,hy,q,hnot,hactive⟩ := twoReveal_crossing_remaining_segment G L R hd C p hu hv
  let Q := openGraph G C ⊓ edgeRestriction G (L ∪ R)
  have hQ : ∀ e, e ∈ q.edges → e ∈ Q.edgeSet := by
    intro e he
    rw [SimpleGraph.edgeSet_inf]
    have heC := q.edges_subset_edgeSet he
    refine ⟨heC,?_⟩
    rw [openGraph_edgeSet] at heC
    let f : G.edgeSet := ⟨e,openEdges_subset G C heC⟩
    rw [edgeRestriction_edgeSet]
    exact ⟨f.property,fun h => hnot f he ((coe_mem_openEdges_iff G (L ∪ R) f).mp h)⟩
  let D := embeddedConfigurationRestriction (activeUnexaminedGraph G (L ∪ R)) G
    (Function.Embedding.subtype _) (activeUnexaminedGraph_map_le G (L ∪ R)) C
  have hle : Q.induce (unexaminedVertices G (L ∪ R)) ≤
      openGraph (activeUnexaminedGraph G (L ∪ R)) D := by
    intro a b hab
    have hdel : (edgeRestriction G (L ∪ R)).Adj a.val b.val := hab.2
    have hopen : (openGraph G C).Adj a.val b.val := hab.1
    let e : (activeUnexaminedGraph G (L ∪ R)).edgeSet :=
      ⟨s(a,b),(activeUnexaminedGraph G (L ∪ R)).mem_edgeSet.mpr hdel⟩
    let f : G.edgeSet := ⟨s(a.val,b.val),G.mem_edgeSet.mpr (edgeRestriction_le G _ hdel)⟩
    have hmap : embeddedEdgeEmbedding _ _ (Function.Embedding.subtype _)
        (activeUnexaminedGraph_map_le G (L ∪ R)) e=f := Subtype.ext rfl
    apply (openGraph_adj _ _ a b).mpr
    refine ⟨e,?_,rfl⟩
    change e ∈ embeddedConfigurationRestriction _ _ (Function.Embedding.subtype _)
      (activeUnexaminedGraph_map_le G (L ∪ R)) C
    rw [mem_embeddedConfigurationRestriction,hmap]
    exact (coe_mem_openEdges_iff G C f).mp ((openGraph_adj G C a.val b.val).mp hopen)
  let qQ := q.transfer Q hQ
  have hactiveQ : ∀ z ∈ qQ.support, z ∈ unexaminedVertices G (L ∪ R) := by
    simpa only [qQ,SimpleGraph.Walk.support_transfer] using hactive
  let qA := qQ.induce (unexaminedVertices G (L ∪ R)) hactiveQ
  exact ⟨⟨x,hactiveQ x qQ.start_mem_support⟩,hx,
    ⟨y,hactiveQ y qQ.end_mem_support⟩,hy,(qA.mapLe hle).reachable⟩

/-- Physical side incidence suffices for the exact reference-square crossing
restriction, after the two exterior vertex sets have been proved disjoint. -/
theorem twoReveal_squareCrossingRestrictsToArcs
    (a : LatticeVertex) (N : ℕ)
    (L R : Configuration (rectangleGraph a N N))
    (hd : Disjoint (revealIncidentVertices (rectangleGraph a N N) L)
      (revealIncidentVertices (rectangleGraph a N N) R))
    (hleft : ∀ u ∈ Square.squareLeftArc a N, u ∈ revealIncidentVertices (rectangleGraph a N N) L)
    (hright : ∀ u ∈ Square.squareRightArc a N, u ∈ revealIncidentVertices (rectangleGraph a N N) R) :
    SquareCrossingRestrictsToArcs a N (activeUnexaminedGraph (rectangleGraph a N N) (L ∪ R))
      (Function.Embedding.subtype _) (activeUnexaminedGraph_map_le _ _)
      (twoRevealActiveLeftArc _ L R) (twoRevealActiveRightArc _ L R) := by
  rintro C ⟨u,hu,v,hv,⟨p⟩⟩
  exact twoReveal_connection_restricts_to_active_arcs (rectangleGraph a N N) L R hd C p
    (hleft u hu) (hright v hv)

end
end PottsContinuity.Push
