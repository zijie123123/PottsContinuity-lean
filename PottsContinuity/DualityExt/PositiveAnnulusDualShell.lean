module

public import PottsContinuity.DualityExt.PositiveRectangleSubgraphDuality
public import PottsContinuity.DualityExt.PositiveP5aAnnulusFit
public import PottsContinuity.DualityExt.AnnulusCounterexample
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial
open PottsContinuity.PD.Duality

noncomputable section

/-- The rectangular host for the primal annulus at scale `N`. -/
def annulusHostAnchor (N : ℕ) : LatticeVertex :=
  (-(2 * (N : ℤ)), -(2 * (N : ℤ)))

/-- The annulus graph on its exact lattice-vertex carrier. -/
def annulusSourceGraph (N : ℕ) :
    SimpleGraph {v : LatticeVertex // v ∈ annulusVertexSet N} :=
  squareLattice.induce (annulusVertexSet N : Set LatticeVertex)

/-- Inclusion of the source annulus carrier into its square host. -/
def annulusSourceEmbedding (N : ℕ) :
    {v : LatticeVertex // v ∈ annulusVertexSet N} ↪
      RectangleVertex (annulusHostAnchor N) (4 * N) (4 * N) where
  toFun v := ⟨v.1, by
    have hv := (mem_latticeBox (0, 0) v.1 (2 * N)).mp
      (Finset.mem_sdiff.mp v.2).1
    rw [mem_latticeRectangle]
    simp only [annulusHostAnchor]
    rcases hv with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
    constructor <;> constructor <;> omega⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : RectangleVertex
      (annulusHostAnchor N) (4 * N) (4 * N) => z.1) hxy

/-- Every annulus bond embeds as an actual host-rectangle bond. -/
theorem annulusSourceGraph_map_le_host (N : ℕ) :
    (annulusSourceGraph N).map (annulusSourceEmbedding N) ≤
      rectangleGraph (annulusHostAnchor N) (4 * N) (4 * N) := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  rcases hxy with ⟨u, v, huv, rfl, rfl⟩
  apply (rectangleGraph_adj_iff _ _ _ _ _).2
  change squareLattice.Adj u.1 v.1 at huv
  exact huv

/-- A bond incident to the removed inner box has both crossed dual
endpoints in the exact inner face box. -/
theorem dualBondOfPrimal_endpoints_mem_innerFaceBox_of_endpoint
    (N : ℕ) (hN : 1 ≤ N) (b : LatticeBond)
    (hb : b.source ∈ latticeBox (0, 0) (N - 1) ∨
      b.target ∈ latticeBox (0, 0) (N - 1)) :
    (dualBondOfPrimal b).source ∈ dualFaceBox N ∧
      (dualBondOfPrimal b).target ∈ dualFaceBox N := by
  rcases b with ⟨⟨x, y⟩, axis⟩
  cases axis
  · simp only [LatticeBond.source, LatticeBond.target, mem_latticeBox] at hb
    simp only [dualBondOfPrimal, LatticeBond.source, LatticeBond.target,
      mem_dualFaceBox]
    rcases hb with hs | ht
    · rcases hs with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
      constructor <;> omega
    · rcases ht with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
      constructor <;> omega
  · simp only [LatticeBond.source, LatticeBond.target, mem_latticeBox] at hb
    simp only [dualBondOfPrimal, LatticeBond.source, LatticeBond.target,
      mem_dualFaceBox]
    rcases hb with hs | ht
    · rcases hs with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
      constructor <;> omega
    · rcases ht with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
      constructor <;> omega

/-- The vertices of the host rectangle are exactly the outer box used by the
annulus definition. -/
private theorem annulusHost_mem_outerBox (N : ℕ) {v : LatticeVertex}
    (hv : v ∈ latticeRectangle (annulusHostAnchor N) (4 * N) (4 * N)) :
    v ∈ latticeBox (0, 0) (2 * N) := by
  rw [mem_latticeRectangle] at hv
  rw [mem_latticeBox]
  simp only [annulusHostAnchor] at hv ⊢
  rcases hv with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
  constructor <;> constructor <;> omega

/-- A host edge omitted by the annulus graph must touch the inner box. -/
theorem annulusHost_removedEdge_touches_innerBox (N : ℕ)
    (e : (rectangleGraph (annulusHostAnchor N) (4 * N) (4 * N)).edgeSet)
    (he : e ∈ subgraphRemovedEdges
      ((annulusSourceGraph N).map (annulusSourceEmbedding N))
      (rectangleGraph (annulusHostAnchor N) (4 * N) (4 * N))) :
    (rectanglePrimalEdgeBond (annulusHostAnchor N) (4 * N) (4 * N) e).source ∈
        latticeBox (0, 0) (N - 1) ∨
      (rectanglePrimalEdgeBond (annulusHostAnchor N) (4 * N) (4 * N) e).target ∈
        latticeBox (0, 0) (N - 1) := by
  let b := rectanglePrimalEdgeBond (annulusHostAnchor N) (4 * N) (4 * N) e
  have hbends := rectanglePrimalEdgeBond_endpoints_mem_public
    (annulusHostAnchor N) (4 * N) (4 * N) e
  have houterS : b.source ∈ latticeBox (0, 0) (2 * N) :=
    annulusHost_mem_outerBox N hbends.1
  have houterT : b.target ∈ latticeBox (0, 0) (2 * N) :=
    annulusHost_mem_outerBox N hbends.2
  by_contra hinner
  have hsnot : b.source ∉ latticeBox (0, 0) (N - 1) :=
    fun hs => hinner (Or.inl hs)
  have htnot : b.target ∉ latticeBox (0, 0) (N - 1) :=
    fun ht => hinner (Or.inr ht)
  have hsAnn : b.source ∈ annulusVertexSet N :=
    Finset.mem_sdiff.mpr ⟨houterS, hsnot⟩
  have htAnn : b.target ∈ annulusVertexSet N :=
    Finset.mem_sdiff.mpr ⟨houterT, htnot⟩
  let x : {v : LatticeVertex // v ∈ annulusVertexSet N} := ⟨b.source, hsAnn⟩
  let y : {v : LatticeVertex // v ∈ annulusVertexSet N} := ⟨b.target, htAnn⟩
  have hsourceAdj : (annulusSourceGraph N).Adj x y := by
    change squareLattice.Adj b.source b.target
    exact b.adjacent
  have hmapAdj :
      ((annulusSourceGraph N).map (annulusSourceEmbedding N)).Adj
        (annulusSourceEmbedding N x) (annulusSourceEmbedding N y) := by
    rw [SimpleGraph.map_adj]
    exact ⟨x, y, hsourceAdj, rfl, rfl⟩
  have hmapEdge :
      s(annulusSourceEmbedding N x, annulusSourceEmbedding N y) ∈
        ((annulusSourceGraph N).map (annulusSourceEmbedding N)).edgeSet :=
    ((annulusSourceGraph N).map (annulusSourceEmbedding N)).mem_edgeSet.mpr hmapAdj
  have heq :
      s(annulusSourceEmbedding N x, annulusSourceEmbedding N y) = e.val := by
    apply Sym2.map.injective Subtype.val_injective
    change s(b.source, b.target) = Sym2.map Subtype.val e.val
    have hbond := rectanglePrimalEdgeBond_toSym2_public
      (annulusHostAnchor N) (4 * N) (4 * N) e
    simpa [b, LatticeBond.toSym2] using hbond
  have hnot := (mem_subgraphRemovedEdges (G :=
    (annulusSourceGraph N).map (annulusSourceEmbedding N))
      (H := rectangleGraph (annulusHostAnchor N) (4 * N) (4 * N)) e).mp he
  exact hnot (by simpa [heq] using hmapEdge)

/-- Every dual bond deleted by the annulus restriction has both endpoints
inside the inner face box of the rectangular host. -/
theorem annulusHost_removedEdge_crossedDual_endpoints_mem_innerFaceBox
    (N : ℕ) (hN : 1 ≤ N)
    (e : (rectangleGraph (annulusHostAnchor N) (4 * N) (4 * N)).edgeSet)
    (he : e ∈ subgraphRemovedEdges
      ((annulusSourceGraph N).map (annulusSourceEmbedding N))
      (rectangleGraph (annulusHostAnchor N) (4 * N) (4 * N))) :
    let b := rectanglePrimalEdgeBond (annulusHostAnchor N) (4 * N) (4 * N) e
    (dualBondOfPrimal b).source ∈ dualFaceBox N ∧
      (dualBondOfPrimal b).target ∈ dualFaceBox N := by
  dsimp
  exact dualBondOfPrimal_endpoints_mem_innerFaceBox_of_endpoint N hN
    (rectanglePrimalEdgeBond (annulusHostAnchor N) (4 * N) (4 * N) e)
    (annulusHost_removedEdge_touches_innerBox N e he)

/-- The deleted dual carrier edges are precisely represented by crossing
bonds whose dual endpoints lie in the inner face box. -/
theorem annulusHost_removedDualEdge_has_innerFaceBox_carrier
    (N : ℕ) (hN : 1 ≤ N)
    (e : (rectangleDualGraph (annulusHostAnchor N) (4 * N) (4 * N)).edgeSet)
    (he : e ∈ rectangleSubgraphRemovedDualEdges
      (G := (annulusSourceGraph N).map (annulusSourceEmbedding N))
      (annulusSourceGraph_map_le_host N)) :
    ∃ d : RectangleDualEdgeCarrier (annulusHostAnchor N) (4 * N) (4 * N),
      rectangleDualGraphEdgeEquiv (annulusHostAnchor N) (4 * N) (4 * N) d = e ∧
        d.crossingBond.source ∈ dualFaceBox N ∧
        d.crossingBond.target ∈ dualFaceBox N := by
  let G := (annulusSourceGraph N).map (annulusSourceEmbedding N)
  let H := rectangleGraph (annulusHostAnchor N) (4 * N) (4 * N)
  have hG : G ≤ H := annulusSourceGraph_map_le_host N
  change e ∈ (subgraphRemovedEdges G H).map
    (rectangleDualEdgeEquiv (annulusHostAnchor N) (4 * N) (4 * N)).toEmbedding at he
  rcases Finset.mem_map.mp he with ⟨f, hf, hfe⟩
  let d := rectanglePrimalDualEdgeEquiv
    (annulusHostAnchor N) (4 * N) (4 * N) f
  have hde : rectangleDualGraphEdgeEquiv
      (annulusHostAnchor N) (4 * N) (4 * N) d = e := by
    change rectangleDualEdgeEquiv (annulusHostAnchor N) (4 * N) (4 * N) f = e
    exact hfe
  have hcross := annulusHost_removedEdge_crossedDual_endpoints_mem_innerFaceBox
    N hN f hf
  refine ⟨d, hde, ?_, ?_⟩
  · simpa [d, rectanglePrimalDualEdgeEquiv, rectangleCrossingDualBond] using hcross.1
  · simpa [d, rectanglePrimalDualEdgeEquiv, rectangleCrossingDualBond] using hcross.2

end
end PottsContinuity.DualityExt
