module

public import PottsContinuity.DualityExt.AnnulusOuterHostGeometry
public import PottsContinuity.PD.RCInfinite.BoxConnector

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial

noncomputable section

def annulusExpandedHostEmbedding (N : ℕ) :
    {v : LatticeVertex // v ∈ annulusVertexSet N} ↪
      RectangleVertex
        (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
        (4 * N + 2) (4 * N + 2) where
  toFun x := ⟨x.1, by
    have hx := (mem_latticeBox (0, 0) x.1 (2 * N)).mp
      (Finset.mem_sdiff.mp x.2).1
    rw [mem_latticeRectangle]
    simp only [PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor,
      annulusHostAnchor] at hx ⊢
    rcases hx with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
    constructor <;> constructor <;> omega⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2) => z.1) hxy

theorem annulusExpandedHostSourceMap_edge_bond_endpoints
    (N : ℕ)
    (e : (rectangleGraph
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)).edgeSet)
    (he : e.val ∈ ((annulusSourceGraph N).map
      (annulusExpandedHostEmbedding N)).edgeSet) :
    (rectanglePrimalEdgeBond
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2) e).source ∈ annulusVertexSet N ∧
    (rectanglePrimalEdgeBond
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2) e).target ∈ annulusVertexSet N := by
  let b := rectanglePrimalEdgeBond
    (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
    (4 * N + 2) (4 * N + 2) e
  let G := (annulusSourceGraph N).map (annulusExpandedHostEmbedding N)
  let p := e.val.out
  have hp : s(p.1, p.2) = e.val := Quot.out_eq _
  have hadj : G.Adj p.1 p.2 := by
    apply G.mem_edgeSet.mp
    rw [hp]
    exact he
  rw [SimpleGraph.map_adj] at hadj
  rcases hadj with ⟨x, y, hxy, hx, hy⟩
  have hp1 : p.1.val = x.1 := by
    have hh := congrArg (fun z : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2) => z.1) hx
    change x.1 = p.1.val at hh
    exact hh.symm
  have hp2 : p.2.val = y.1 := by
    have hh := congrArg (fun z : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2) => z.1) hy
    change y.1 = p.2.val at hh
    exact hh.symm
  have hbond := rectanglePrimalEdgeBond_toSym2_public
    (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
    (4 * N + 2) (4 * N + 2) e
  have hsym : s(b.source, b.target) = s(p.1.val, p.2.val) := by
    change b.toSym2 = s(p.1.val, p.2.val)
    calc
      b.toSym2 = Sym2.map (fun z : RectangleVertex
          (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
          (4 * N + 2) (4 * N + 2) => z.1) e.val := by
        simpa [b, LatticeBond.toSym2] using hbond
      _ = s(p.1.val, p.2.val) := by rw [← hp]; rfl
  rcases Sym2.eq_iff.mp hsym with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rw [hs, ht, hp1, hp2]
    exact ⟨x.property, y.property⟩
  · rw [hs, ht, hp1, hp2]
    exact ⟨y.property, x.property⟩

theorem annulusExpandedHost_innerEndpoint_edge_mem_removed
    (N : ℕ)
    (x y : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2))
    (hxy : (rectangleGraph
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)).Adj x y)
    (hx : x.1 ∈ latticeBox (0, 0) (N - 1)) :
    s(x, y) ∈ openEdges
      (rectangleGraph
        (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
        (4 * N + 2) (4 * N + 2))
      (subgraphRemovedEdges
        ((annulusSourceGraph N).map (annulusExpandedHostEmbedding N))
        (rectangleGraph
          (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
          (4 * N + 2) (4 * N + 2))) := by
  let H := rectangleGraph
    (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
    (4 * N + 2) (4 * N + 2)
  let G := (annulusSourceGraph N).map (annulusExpandedHostEmbedding N)
  let e : H.edgeSet := ⟨s(x, y), hxy⟩
  have hbond := rectanglePrimalEdgeBond_toSym2_public
    (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
    (4 * N + 2) (4 * N + 2) e
  have heq : (rectanglePrimalEdgeBond
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2) e).toSym2 = s(x.1, y.1) := by
    simpa [e, LatticeBond.toSym2] using hbond
  have hinner :
      (rectanglePrimalEdgeBond
        (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
        (4 * N + 2) (4 * N + 2) e).source ∈ latticeBox (0, 0) (N - 1) ∨
      (rectanglePrimalEdgeBond
        (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
        (4 * N + 2) (4 * N + 2) e).target ∈ latticeBox (0, 0) (N - 1) := by
    rcases Sym2.eq_iff.mp heq with ⟨hs, _⟩ | ⟨_, ht⟩
    · exact Or.inl (hs.symm ▸ hx)
    · exact Or.inr (ht.symm ▸ hx)
  have hnot : e.val ∉ G.edgeSet := by
    intro he
    have hend := annulusExpandedHostSourceMap_edge_bond_endpoints N e he
    rcases hinner with hs | ht
    · have hbad : (rectanglePrimalEdgeBond
          (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
          (4 * N + 2) (4 * N + 2) e).source ∉ annulusVertexSet N := by
        intro ha
        exact (Finset.mem_sdiff.mp ha).2 hs
      exact hbad hend.1
    · have hbad : (rectanglePrimalEdgeBond
          (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
          (4 * N + 2) (4 * N + 2) e).target ∉ annulusVertexSet N := by
        intro ha
        exact (Finset.mem_sdiff.mp ha).2 ht
      exact hbad hend.2
  have he' : e ∈ subgraphRemovedEdges G H :=
    (mem_subgraphRemovedEdges (G := G) (H := H) e).2 hnot
  rw [openEdges]
  exact ⟨e, he', rfl⟩

theorem annulusExpandedHost_innerBox_mem_host (N : ℕ) (hN : 1 ≤ N)
    {z : LatticeVertex} (hz : z ∈ latticeBox (0, 0) (N - 1)) :
    z ∈ PottsContinuity.PD.FK.latticeRectangle
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2) := by
  have hz' := (mem_latticeBox (0, 0) z (N - 1)).mp hz
  rw [PottsContinuity.PD.FK.mem_latticeRectangle]
  simp only [PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor,
    annulusHostAnchor] at hz' ⊢
  rcases hz' with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
  constructor <;> constructor <;> omega

def annulusExpandedHostBoxVertex (N : ℕ) (hN : 1 ≤ N)
    (z : BoxVertex (0, 0) (N - 1)) :
    RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2) :=
  ⟨z.1, annulusExpandedHost_innerBox_mem_host N hN z.2⟩

private theorem annulusExpandedHost_boxEdge_mem_removed (N : ℕ) (hN : 1 ≤ N)
    {x y : BoxVertex (0, 0) (N - 1)}
    (hxy : (boxGraph (0, 0) (N - 1)).Adj x y) :
    s(annulusExpandedHostBoxVertex N hN x,
      annulusExpandedHostBoxVertex N hN y) ∈ openEdges
      (rectangleGraph
        (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
        (4 * N + 2) (4 * N + 2))
      (subgraphRemovedEdges
        ((annulusSourceGraph N).map (annulusExpandedHostEmbedding N))
        (rectangleGraph
          (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
          (4 * N + 2) (4 * N + 2))) := by
  apply annulusExpandedHost_innerEndpoint_edge_mem_removed N
  · exact (rectangleGraph_adj_iff _ _ _ _ _).2
      ((boxGraph_adj_iff (0, 0) (N - 1) x y).mp hxy)
  · exact x.2

def annulusExpandedHost_boxGraph_to_openHom (N : ℕ) (hN : 1 ≤ N) :
    boxGraph (0, 0) (N - 1) →g
      openGraph
        (rectangleGraph
          (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
          (4 * N + 2) (4 * N + 2))
        (subgraphRemovedEdges
          ((annulusSourceGraph N).map (annulusExpandedHostEmbedding N))
          (rectangleGraph
            (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
            (4 * N + 2) (4 * N + 2))) where
  toFun := annulusExpandedHostBoxVertex N hN
  map_rel' := by
    intro x y hxy
    rw [openGraph_adj]
    exact annulusExpandedHost_boxEdge_mem_removed N hN hxy

theorem annulusExpandedHost_innerBox_connected_to_center
    (N : ℕ) (hN : 1 ≤ N) (z : BoxVertex (0, 0) (N - 1)) :
    (openGraph
      (rectangleGraph
        (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
        (4 * N + 2) (4 * N + 2))
      (subgraphRemovedEdges
        ((annulusSourceGraph N).map (annulusExpandedHostEmbedding N))
        (rectangleGraph
          (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
          (4 * N + 2) (4 * N + 2)))).Reachable
      (annulusExpandedHostBoxVertex N hN ⟨(0, 0), by
        rw [mem_latticeBox]
        simp only [zero_sub, zero_add]
        omega⟩)
      (annulusExpandedHostBoxVertex N hN z) := by
  let c : BoxVertex (0, 0) (N - 1) := ⟨(0, 0), by
    rw [mem_latticeBox]
    simp only [zero_sub, zero_add]
    omega⟩
  have hpath : (boxGraph (0, 0) (N - 1)).Reachable c z :=
    (PottsContinuity.PD.RCInfinite.boxGraph_connected (N - 1)).preconnected c z
  have hmap := hpath.map (annulusExpandedHost_boxGraph_to_openHom N hN)
  simpa [annulusExpandedHost_boxGraph_to_openHom, annulusExpandedHostBoxVertex, c]
    using hmap

def annulusExpandedHostPrimalInnerClass (N : ℕ) :
    Set (RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)) :=
  {v | v.1 ∈ latticeBox (0, 0) (N - 1) ∨
    ∃ u, u ∈ latticeBox (0, 0) (N - 1) ∧ squareLattice.Adj u v.1}

def annulusExpandedHostPrimalEmptyWiring (N : ℕ) :
    BoundaryCondition (RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)) :=
  BoundaryCondition.wired ∅

def annulusExpandedHostPrimalFrozenPartition (N : ℕ) :
    Setoid (RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)) :=
  componentSetoid
    (rectangleGraph
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2))
    (annulusExpandedHostPrimalEmptyWiring N)
    (subgraphRemovedEdges
      ((annulusSourceGraph N).map (annulusExpandedHostEmbedding N))
      (rectangleGraph
        (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
        (4 * N + 2) (4 * N + 2)))

theorem annulusExpandedHost_innerClass_connected_to_center
    (N : ℕ) (hN : 1 ≤ N)
    (z : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2))
    (hz : z ∈ annulusExpandedHostPrimalInnerClass N) :
    (annulusExpandedHostPrimalFrozenPartition N).r
      (annulusExpandedHostBoxVertex N hN ⟨(0, 0),
        center_mem_latticeBox (0, 0) (N - 1)⟩) z := by
  let H := rectangleGraph
    (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
    (4 * N + 2) (4 * N + 2)
  let R := subgraphRemovedEdges
    ((annulusSourceGraph N).map (annulusExpandedHostEmbedding N)) H
  let ξ := annulusExpandedHostPrimalEmptyWiring N
  let c : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2) :=
    annulusExpandedHostBoxVertex N hN
      ⟨(0, 0), center_mem_latticeBox (0, 0) (N - 1)⟩
  rcases hz with hzbox | ⟨u, hu, hadj⟩
  · let zBox : BoxVertex (0, 0) (N - 1) := ⟨z.1, hzbox⟩
    have hbox := annulusExpandedHost_innerBox_connected_to_center N hN zBox
    have hbox' : (openGraph H R).Reachable c z := by
      simpa [c, H, R, annulusExpandedHostBoxVertex] using hbox
    exact actualConnected_component H ξ R hbox'
  · let uBox : BoxVertex (0, 0) (N - 1) := ⟨u, hu⟩
    let uHost := annulusExpandedHostBoxVertex N hN uBox
    have hadj' : H.Adj uHost z :=
      (rectangleGraph_adj_iff _ _ _ _ _).2 hadj
    have hopen : (openGraph H R).Adj uHost z :=
      (openGraph_adj H R uHost z).2
        (annulusExpandedHost_innerEndpoint_edge_mem_removed N uHost z hadj' hu)
    have hstep := actualConnected_component H ξ R
      (actualConnected_of_adj H R hopen)
    have hbase := actualConnected_component H ξ R
      (annulusExpandedHost_innerBox_connected_to_center N hN uBox)
    exact (componentSetoid H ξ R).iseqv.trans hbase hstep

end
end PottsContinuity.DualityExt
