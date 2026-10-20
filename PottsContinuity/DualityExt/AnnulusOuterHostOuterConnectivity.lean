module

public import PottsContinuity.DualityExt.AnnulusOuterHostInnerConnectivity

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial

noncomputable section

def expandedHostOuterBoundaryCoord (N : ℕ) : Set LatticeVertex :=
  PottsContinuity.PD.vertexBoundary
    (PottsContinuity.PD.FK.latticeRectangle
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2))

def expandedHostOuterBoundary (N : ℕ) : Set (RectangleVertex
    (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
    (4 * N + 2) (4 * N + 2)) :=
  {z | z.1 ∈ expandedHostOuterBoundaryCoord N}

def annulusExpandedHostPrimalOuterClass (N : ℕ) :
    Set (RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)) :=
  {v | v.1 ∈ expandedHostOuterBoundaryCoord N ∨
    ∃ w, w.1 ∈ expandedHostOuterBoundaryCoord N ∧
      (rectangleGraph
        (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
        (4 * N + 2) (4 * N + 2)).Adj v w}

private theorem expandedHost_rect_mem_outerBox (N : ℕ)
    (z : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)) :
    z.1 ∈ latticeBox (0, 0) (2 * N + 1) := by
  have hz := z.2
  rw [PottsContinuity.PD.FK.mem_latticeRectangle] at hz
  rw [PottsContinuity.PD.FK.mem_latticeBox]
  simp only [PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor,
    annulusHostAnchor] at hz ⊢
  rcases hz with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
  constructor <;> constructor <;> omega

private theorem expandedHost_boundary_not_oldBox (N : ℕ)
    (z : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2))
    (hz : z.1 ∈ expandedHostOuterBoundaryCoord N) :
    z.1 ∉ latticeBox (0, 0) (2 * N) := by
  intro hzbox
  change z.1 ∈ PottsContinuity.PD.vertexBoundary _ at hz
  rw [PottsContinuity.PD.vertexBoundary] at hz
  rcases hz with ⟨_, y, hadj, hyout⟩
  have hzcoords := (PottsContinuity.PD.FK.mem_latticeBox
    (0, 0) z.1 (2 * N)).mp hzbox
  have hadj' := (PottsContinuity.PD.FK.squareLattice_adj_iff
    z.1 y).mp hadj
  have hyRect : y ∈ PottsContinuity.PD.FK.latticeRectangle
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2) := by
    rw [PottsContinuity.PD.FK.mem_latticeRectangle]
    simp only [PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor,
      annulusHostAnchor]
    rcases hzcoords with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
    rcases hadj' with ⟨h | h, hy⟩ | ⟨hx, h | h⟩ <;>
      constructor <;> constructor <;> omega
  exact hyout hyRect

private theorem expandedHost_not_oldBox_boundary (N : ℕ)
    (z : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2))
    (hz : z.1 ∉ latticeBox (0, 0) (2 * N)) :
    z.1 ∈ expandedHostOuterBoundaryCoord N := by
  have hzbox := expandedHost_rect_mem_outerBox N z
  have hcoords := (PottsContinuity.PD.FK.mem_latticeBox
    (0, 0) z.1 (2 * N + 1)).mp hzbox
  have hside : z.1.1 = 2 * (N : ℤ) + 1 ∨
      z.1.1 = -(2 * (N : ℤ) + 1) ∨
      z.1.2 = 2 * (N : ℤ) + 1 ∨
      z.1.2 = -(2 * (N : ℤ) + 1) := by
    by_contra h
    push Not at h
    apply hz
    rw [PottsContinuity.PD.FK.mem_latticeBox]
    rcases hcoords with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
    constructor <;> constructor <;> omega
  have hzrect : z.1 ∈ PottsContinuity.PD.FK.latticeRectangle
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2) := z.2
  change z.1 ∈ PottsContinuity.PD.vertexBoundary _
  rw [PottsContinuity.PD.vertexBoundary]
  rcases hside with hx | hx | hy | hy
  · refine ⟨hzrect, (z.1.1 + 1, z.1.2), ?_, ?_⟩
    · rw [PottsContinuity.PD.FK.squareLattice_adj_iff]
      exact Or.inl ⟨by omega, rfl⟩
    · intro hmem
      rw [PottsContinuity.PD.FK.mem_latticeRectangle] at hmem
      simp only [PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor,
        annulusHostAnchor] at hmem
      omega
  · refine ⟨hzrect, (z.1.1 - 1, z.1.2), ?_, ?_⟩
    · rw [PottsContinuity.PD.FK.squareLattice_adj_iff]
      exact Or.inl ⟨Or.inr (by omega), rfl⟩
    · intro hmem
      rw [PottsContinuity.PD.FK.mem_latticeRectangle] at hmem
      simp only [PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor,
        annulusHostAnchor] at hmem
      omega
  · refine ⟨hzrect, (z.1.1, z.1.2 + 1), ?_, ?_⟩
    · rw [PottsContinuity.PD.FK.squareLattice_adj_iff]
      exact Or.inr ⟨rfl, by omega⟩
    · intro hmem
      rw [PottsContinuity.PD.FK.mem_latticeRectangle] at hmem
      simp only [PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor,
        annulusHostAnchor] at hmem
      omega
  · refine ⟨hzrect, (z.1.1, z.1.2 - 1), ?_, ?_⟩
    · rw [PottsContinuity.PD.FK.squareLattice_adj_iff]
      exact Or.inr ⟨rfl, Or.inr (by omega)⟩
    · intro hmem
      rw [PottsContinuity.PD.FK.mem_latticeRectangle] at hmem
      simp only [PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor,
        annulusHostAnchor] at hmem
      omega

theorem annulusExpandedHost_outerClass_disjoint (N : ℕ) (hN : 1 ≤ N) :
    Disjoint (annulusExpandedHostPrimalInnerClass N)
      (annulusExpandedHostPrimalOuterClass N) := by
  rw [Set.disjoint_left]
  intro z hzI hzO
  have hzSmall : z.1 ∈ latticeBox (0, 0) N := by
    rcases hzI with hzbox | ⟨u, hu, hadj⟩
    · exact PottsContinuity.PD.FK.latticeBox_mono (0, 0)
        (Nat.sub_le N 1) hzbox
    · have hu' := (PottsContinuity.PD.FK.mem_latticeBox
        (0, 0) u (N - 1)).mp hu
      have hadj' := (PottsContinuity.PD.FK.squareLattice_adj_iff
        u z.1).mp hadj
      rw [PottsContinuity.PD.FK.mem_latticeBox]
      rcases hu' with ⟨⟨huxl, huxu⟩, ⟨huyl, huyu⟩⟩
      rcases hadj' with ⟨h | h, hy⟩ | ⟨hx, h | h⟩ <;>
        constructor <;> constructor <;> omega
  rcases hzO with hzB | ⟨w, hwB, hadj⟩
  · exact (expandedHost_boundary_not_oldBox N z hzB)
      (PottsContinuity.PD.FK.latticeBox_mono (0, 0)
        (show N ≤ 2 * N by omega) hzSmall)
  · have hwnot := expandedHost_boundary_not_oldBox N w hwB
    have hadj' := (PottsContinuity.PD.FK.squareLattice_adj_iff
      z.1 w.1).mp
      ((PottsContinuity.PD.FK.rectangleGraph_adj_iff _ _ _ _ _).mp hadj)
    have hwbox : w.1 ∈ latticeBox (0, 0) (2 * N) := by
      rw [PottsContinuity.PD.FK.mem_latticeBox]
      have hzc := (PottsContinuity.PD.FK.mem_latticeBox
        (0, 0) z.1 N).mp hzSmall
      rcases hzc with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
      rcases hadj' with ⟨h | h, hy⟩ | ⟨hx, h | h⟩ <;>
        constructor <;> constructor <;> omega
    exact hwnot hwbox

private theorem expandedHost_boundaryAdjacent_edge_mem_removed
    (N : ℕ)
    (z w : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2))
    (hzw : (rectangleGraph
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)).Adj z w)
    (hw : w.1 ∈ expandedHostOuterBoundaryCoord N) :
    s(z, w) ∈ openEdges
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
  let R := subgraphRemovedEdges G H
  let e : H.edgeSet := ⟨s(z, w), hzw⟩
  have hnot : e.val ∉ G.edgeSet := by
    intro he
    have hAdj : G.Adj z w := G.mem_edgeSet.mp he
    rw [SimpleGraph.map_adj] at hAdj
    rcases hAdj with ⟨x, y, hxy, hx, hy⟩
    have hval := congrArg (fun v : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2) => v.1) hy
    change y.1 = w.1 at hval
    have hyAnn : w.1 ∈ annulusVertexSet N := by
      simpa [hval] using y.2
    have hwBox : w.1 ∈ latticeBox (0, 0) (2 * N) :=
      (Finset.mem_sdiff.mp hyAnn).1
    exact (expandedHost_boundary_not_oldBox N w hw) hwBox
  have he : e ∈ subgraphRemovedEdges G H :=
    (mem_subgraphRemovedEdges (G := G) (H := H) e).2 hnot
  rw [openEdges]
  exact ⟨e, he, rfl⟩

theorem annulusExpandedHost_outerClass_component_connected
    (N : ℕ) :
    ∀ ⦃u v : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)⦄,
      u ∈ annulusExpandedHostPrimalOuterClass N →
      v ∈ annulusExpandedHostPrimalOuterClass N →
      (componentSetoid
        (rectangleGraph
          (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
          (4 * N + 2) (4 * N + 2))
        (BoundaryCondition.wired (expandedHostOuterBoundary N))
        (subgraphRemovedEdges
          ((annulusSourceGraph N).map (annulusExpandedHostEmbedding N))
          (rectangleGraph
            (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
            (4 * N + 2) (4 * N + 2)))).r u v := by
  intro u v hu hv
  let H := rectangleGraph
    (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
    (4 * N + 2) (4 * N + 2)
  let ξ := BoundaryCondition.wired (expandedHostOuterBoundary N)
  let R := subgraphRemovedEdges
    ((annulusSourceGraph N).map (annulusExpandedHostEmbedding N)) H
  have huB : ∃ x : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2), x.1 ∈ expandedHostOuterBoundaryCoord N ∧
        (componentSetoid H ξ R).r u x := by
    rcases hu with hu | ⟨x, hx, hadj⟩
    · exact ⟨u, hu, (componentSetoid H ξ R).iseqv.refl u⟩
    · have hopen : (openGraph H R).Adj u x := by
        apply (openGraph_adj H R u x).2
        exact expandedHost_boundaryAdjacent_edge_mem_removed N u x hadj hx
      exact ⟨x, hx, actualConnected_component H ξ R
        (actualConnected_of_adj H R hopen)⟩
  have hvB : ∃ x : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2), x.1 ∈ expandedHostOuterBoundaryCoord N ∧
        (componentSetoid H ξ R).r v x := by
    rcases hv with hv | ⟨x, hx, hadj⟩
    · exact ⟨v, hv, (componentSetoid H ξ R).iseqv.refl v⟩
    · have hopen : (openGraph H R).Adj v x := by
        apply (openGraph_adj H R v x).2
        exact expandedHost_boundaryAdjacent_edge_mem_removed N v x hadj hx
      exact ⟨x, hx, actualConnected_component H ξ R
        (actualConnected_of_adj H R hopen)⟩
  rcases huB with ⟨x, hx, hux⟩
  rcases hvB with ⟨y, hy, hvy⟩
  have hxW : x ∈ expandedHostOuterBoundary N := hx
  have hyW : y ∈ expandedHostOuterBoundary N := hy
  have hxy : ξ.partition.r x y := by
    exact (BoundaryCondition.wired_rel (expandedHostOuterBoundary N) x y).2
      (Or.inr ⟨hxW, hyW⟩)
  have hwire := boundary_component H ξ R hxy
  exact (componentSetoid H ξ R).iseqv.trans
    hux ((componentSetoid H ξ R).iseqv.trans hwire
      ((componentSetoid H ξ R).iseqv.symm hvy))

end
end PottsContinuity.DualityExt

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial

noncomputable section

private theorem expandedHost_map_annulusBond_mem
    (N : ℕ) (e : (rectangleGraph
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)).edgeSet)
    (hs : (rectanglePrimalEdgeBond
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2) e).source ∈ annulusVertexSet N)
    (ht : (rectanglePrimalEdgeBond
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2) e).target ∈ annulusVertexSet N) :
    e.1 ∈ ((annulusSourceGraph N).map (annulusExpandedHostEmbedding N)).edgeSet := by
  let b := rectanglePrimalEdgeBond
    (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
    (4 * N + 2) (4 * N + 2) e
  let x : {v : LatticeVertex // v ∈ annulusVertexSet N} := ⟨b.source, hs⟩
  let y : {v : LatticeVertex // v ∈ annulusVertexSet N} := ⟨b.target, ht⟩
  have hsourceAdj : (annulusSourceGraph N).Adj x y := by
    change squareLattice.Adj b.source b.target
    exact b.adjacent
  have hmapAdj : ((annulusSourceGraph N).map (annulusExpandedHostEmbedding N)).Adj
      (annulusExpandedHostEmbedding N x) (annulusExpandedHostEmbedding N y) := by
    rw [SimpleGraph.map_adj]
    exact ⟨x, y, hsourceAdj, rfl, rfl⟩
  have hbond := rectanglePrimalEdgeBond_toSym2_public
    (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
    (4 * N + 2) (4 * N + 2) e
  have heq : s(annulusExpandedHostEmbedding N x,
      annulusExpandedHostEmbedding N y) = e.1 := by
    apply Sym2.map.injective Subtype.val_injective
    change s(b.source, b.target) = Sym2.map Subtype.val e.1
    simpa [b, LatticeBond.toSym2] using hbond
  have hmem := ((annulusSourceGraph N).map
    (annulusExpandedHostEmbedding N)).mem_edgeSet.mpr hmapAdj
  rw [← heq]
  exact hmem

private theorem annulusExpandedHost_removedEdge_twoBlock
    (N : ℕ)
    {e : (rectangleGraph
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)).edgeSet}
    (he : e ∈ subgraphRemovedEdges
      ((annulusSourceGraph N).map (annulusExpandedHostEmbedding N))
      (rectangleGraph
        (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
        (4 * N + 2) (4 * N + 2))) :
    (∀ ⦃u : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)⦄,
      u ∈ e.1 → u ∈ annulusExpandedHostPrimalInnerClass N) ∨
    (∀ ⦃u : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)⦄,
      u ∈ e.1 → u ∈ annulusExpandedHostPrimalOuterClass N) := by
  let b := rectanglePrimalEdgeBond
    (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
    (4 * N + 2) (4 * N + 2) e
  have hbond := rectanglePrimalEdgeBond_toSym2_public
    (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
    (4 * N + 2) (4 * N + 2) e
  have hpair : s(b.source, b.target) = Sym2.map Subtype.val e.1 := by
    simpa [b, LatticeBond.toSym2] using hbond
  let p := e.1.out
  have hp : s(p.1, p.2) = e.1 := Quot.out_eq _
  have hbondPair : s(b.source, b.target) = s(p.1.1, p.2.1) := by
    calc
      s(b.source, b.target) = Sym2.map Subtype.val e.1 := hpair
      _ = s(p.1.1, p.2.1) := by rw [← hp]; rfl
  have hendpoint : ∀ ⦃u : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)⦄, u ∈ e.1 →
      u.1 = b.source ∨ u.1 = b.target := by
    intro u hu
    rw [← hp] at hu
    have huPair := (Sym2.mem_iff').mp hu
    rcases Sym2.eq_iff.mp hbondPair with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · rcases huPair with hu1 | hu2
      · exact Or.inl ((congrArg Subtype.val hu1).trans hs.symm)
      · exact Or.inr ((congrArg Subtype.val hu2).trans ht.symm)
    · rcases huPair with hu1 | hu2
      · exact Or.inr ((congrArg Subtype.val hu1).trans ht.symm)
      · exact Or.inl ((congrArg Subtype.val hu2).trans hs.symm)
  have hends := rectanglePrimalEdgeBond_endpoints_mem_public
    (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
    (4 * N + 2) (4 * N + 2) e
  let x : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2) := ⟨b.source, hends.1⟩
  let y : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2) := ⟨b.target, hends.2⟩
  by_cases hsI : b.source ∈ latticeBox (0, 0) (N - 1)
  · left
    intro u hu
    rcases hendpoint hu with huS | huT
    · change u.1 ∈ latticeBox (0, 0) (N - 1) ∨ _
      rw [huS]
      exact Or.inl hsI
    · change u.1 ∈ latticeBox (0, 0) (N - 1) ∨ _
      rw [huT]
      exact Or.inr ⟨b.source, hsI, b.adjacent⟩
  · by_cases htI : b.target ∈ latticeBox (0, 0) (N - 1)
    · left
      intro u hu
      rcases hendpoint hu with huS | huT
      · change u.1 ∈ latticeBox (0, 0) (N - 1) ∨ _
        rw [huS]
        exact Or.inr ⟨b.target, htI, b.adjacent.symm⟩
      · change u.1 ∈ latticeBox (0, 0) (N - 1) ∨ _
        rw [huT]
        exact Or.inl htI
    · by_cases hsOut : b.source ∉ latticeBox (0, 0) (2 * N)
      · right
        intro u hu
        rcases hendpoint hu with huS | huT
        · have hxNot : x.1 ∉ latticeBox (0, 0) (2 * N) := by
            change b.source ∉ latticeBox (0, 0) (2 * N)
            exact hsOut
          have hxB := expandedHost_not_oldBox_boundary N x hxNot
          change u.1 ∈ expandedHostOuterBoundaryCoord N ∨ _
          rw [huS]
          exact Or.inl hxB
        · have hxNot : x.1 ∉ latticeBox (0, 0) (2 * N) := by
            change b.source ∉ latticeBox (0, 0) (2 * N)
            exact hsOut
          have hxB := expandedHost_not_oldBox_boundary N x hxNot
          change u.1 ∈ expandedHostOuterBoundaryCoord N ∨ _
          rw [huT]
          refine Or.inr ⟨x, hxB, ?_⟩
          apply (PottsContinuity.PD.FK.rectangleGraph_adj_iff _ _ _ _ _).2
          simpa only [huT] using b.adjacent.symm
      · by_cases htOut : b.target ∉ latticeBox (0, 0) (2 * N)
        · right
          intro u hu
          rcases hendpoint hu with huS | huT
          · change u.1 ∈ expandedHostOuterBoundaryCoord N ∨ _
            rw [huS]
            have hyNot : y.1 ∉ latticeBox (0, 0) (2 * N) := by
              change b.target ∉ latticeBox (0, 0) (2 * N)
              exact htOut
            refine Or.inr ⟨y, expandedHost_not_oldBox_boundary N y hyNot, ?_⟩
            apply (PottsContinuity.PD.FK.rectangleGraph_adj_iff _ _ _ _ _).2
            simpa only [huS] using b.adjacent
          · change u.1 ∈ expandedHostOuterBoundaryCoord N ∨ _
            rw [huT]
            have hyNot : y.1 ∉ latticeBox (0, 0) (2 * N) := by
              change b.target ∉ latticeBox (0, 0) (2 * N)
              exact htOut
            exact Or.inl (expandedHost_not_oldBox_boundary N y hyNot)
        · have hsBox : b.source ∈ latticeBox (0, 0) (2 * N) := by
            exact Classical.byContradiction fun h => hsOut h
          have htBox : b.target ∈ latticeBox (0, 0) (2 * N) := by
            exact Classical.byContradiction fun h => htOut h
          have hsAnn : b.source ∈ annulusVertexSet N :=
            Finset.mem_sdiff.mpr ⟨hsBox, hsI⟩
          have htAnn : b.target ∈ annulusVertexSet N :=
            Finset.mem_sdiff.mpr ⟨htBox, htI⟩
          have hGedge := expandedHost_map_annulusBond_mem N e hsAnn htAnn
          have hnot := (mem_subgraphRemovedEdges
            (G := (annulusSourceGraph N).map (annulusExpandedHostEmbedding N))
            (H := rectangleGraph
              (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
              (4 * N + 2) (4 * N + 2)) e).1 he
          exact False.elim (hnot hGedge)

theorem annulusExpandedHost_sourceMissingEdge_twoBlock
    (N : ℕ)
    (e : (rectangleGraph
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)).edgeSet)
    (hmiss : e.1 ∉ ((annulusSourceGraph N).map
      (annulusExpandedHostEmbedding N)).edgeSet) :
    (∀ ⦃u : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)⦄,
      u ∈ e.1 → u ∈ annulusExpandedHostPrimalInnerClass N) ∨
    (∀ ⦃u : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)⦄,
      u ∈ e.1 → u ∈ annulusExpandedHostPrimalOuterClass N) := by
  have he : e ∈ subgraphRemovedEdges
      ((annulusSourceGraph N).map (annulusExpandedHostEmbedding N))
      (rectangleGraph
        (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
        (4 * N + 2) (4 * N + 2)) :=
    (mem_subgraphRemovedEdges
      (G := (annulusSourceGraph N).map (annulusExpandedHostEmbedding N))
      (H := rectangleGraph
        (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
        (4 * N + 2) (4 * N + 2)) e).2 hmiss
  exact annulusExpandedHost_removedEdge_twoBlock N he

theorem annulusCandidateActive_toExpandedHostEmbedding_eq
    (N : ℕ) (hN : 2 ≤ N)
    (u : {v : LatticeVertex // v ∈ annulusVertexSet N}) :
    (annulusCandidateDualOuterHostVertexEquiv N
      (positiveActiveInclusion (rectangleSubgraphDualGraph
        (PottsContinuity.Thm3.Easy.annulusExpandedHostDualCandidateGraph_le_rectangle N))
        ((PottsContinuity.Thm3.Easy.annulusCandidateDoubleDualActiveVertexEquiv N hN).symm u))).1 =
      (annulusExpandedHostEmbedding N u).1 := by
  change (((PottsContinuity.Thm3.Easy.annulusCandidateDoubleDualActiveVertexEquiv N hN).symm u).1.1.1 + 1,
      ((PottsContinuity.Thm3.Easy.annulusCandidateDoubleDualActiveVertexEquiv N hN).symm u).1.1.2 + 1) = u.1
  have he := congrArg Subtype.val
    (Equiv.apply_symm_apply
      (PottsContinuity.Thm3.Easy.annulusCandidateDoubleDualActiveVertexEquiv N hN) u)
  have hs := PottsContinuity.Thm3.Easy.annulusCandidateDoubleDualActiveVertexEquiv_apply_val
    N hN ((PottsContinuity.Thm3.Easy.annulusCandidateDoubleDualActiveVertexEquiv N hN).symm u)
  exact hs.trans he

theorem annulusCandidateActive_innerClass_iff
    (N : ℕ) (hN : 2 ≤ N)
    (u : {v : LatticeVertex // v ∈ annulusVertexSet N}) :
    annulusCandidateDualOuterHostVertexEquiv N
        (positiveActiveInclusion (rectangleSubgraphDualGraph
          (PottsContinuity.Thm3.Easy.annulusExpandedHostDualCandidateGraph_le_rectangle N))
          ((PottsContinuity.Thm3.Easy.annulusCandidateDoubleDualActiveVertexEquiv N hN).symm u)) ∈
      annulusExpandedHostPrimalInnerClass N ↔
    u ∈ annulusPrimalInnerBoundaryClass N (by omega) := by
  change (((annulusCandidateDualOuterHostVertexEquiv N
      (positiveActiveInclusion (rectangleSubgraphDualGraph
        (PottsContinuity.Thm3.Easy.annulusExpandedHostDualCandidateGraph_le_rectangle N))
        ((PottsContinuity.Thm3.Easy.annulusCandidateDoubleDualActiveVertexEquiv N hN).symm u))).1 ∈
      latticeBox (0, 0) (N - 1) ∨
      ∃ v, v ∈ latticeBox (0, 0) (N - 1) ∧
        squareLattice.Adj v
          (annulusCandidateDualOuterHostVertexEquiv N
            (positiveActiveInclusion (rectangleSubgraphDualGraph
              (PottsContinuity.Thm3.Easy.annulusExpandedHostDualCandidateGraph_le_rectangle N))
              ((PottsContinuity.Thm3.Easy.annulusCandidateDoubleDualActiveVertexEquiv N hN).symm u))).1)) ↔
    u.1 ∈ latticeBox (0, 0) (N - 1) ∨
      ∃ v, v ∈ latticeBox (0, 0) (N - 1) ∧ squareLattice.Adj v u.1
  rw [annulusCandidateActive_toExpandedHostEmbedding_eq N hN u]
  rfl

private theorem annulusBox_boundary_iff (r : ℕ) (z : LatticeVertex) :
    z ∈ PottsContinuity.PD.vertexBoundary (latticeBox (0, 0) r) ↔
      z ∈ latticeBox (0, 0) r ∧
        (z.1 = (r : ℤ) ∨ z.1 = -(r : ℤ) ∨ z.2 = (r : ℤ) ∨ z.2 = -(r : ℤ)) := by
  rw [PottsContinuity.PD.vertexBoundary]
  constructor
  · rintro ⟨hz, y, hadj, hy⟩
    have hc := (PottsContinuity.PD.FK.mem_latticeBox (0, 0) z r).mp hz
    have ha := (PottsContinuity.PD.FK.squareLattice_adj_iff z y).mp hadj
    have hout : y.1 < -(r : ℤ) ∨ (r : ℤ) < y.1 ∨
        y.2 < -(r : ℤ) ∨ (r : ℤ) < y.2 := by
      by_contra h
      push Not at h
      apply hy
      rw [PottsContinuity.PD.FK.mem_latticeBox]
      simp only [zero_sub, zero_add]
      omega
    rcases hc with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
    rcases ha with ⟨h | h, hyz⟩ | ⟨hxz, h | h⟩ <;>
      rcases hout with ho | ho | ho | ho <;>
      refine ⟨hz, ?_⟩ <;> omega
  · rintro ⟨hz, hx | hx | hy | hy⟩
    · refine ⟨hz, (z.1 + 1, z.2), ?_, ?_⟩
      · rw [PottsContinuity.PD.FK.squareLattice_adj_iff]
        exact Or.inl ⟨Or.inl rfl, rfl⟩
      · rw [PottsContinuity.PD.FK.mem_latticeBox] at *
        rcases hz with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
        omega
    · refine ⟨hz, (z.1 - 1, z.2), ?_, ?_⟩
      · rw [PottsContinuity.PD.FK.squareLattice_adj_iff]
        exact Or.inl ⟨Or.inr (by omega), rfl⟩
      · rw [PottsContinuity.PD.FK.mem_latticeBox] at *
        rcases hz with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
        omega
    · refine ⟨hz, (z.1, z.2 + 1), ?_, ?_⟩
      · rw [PottsContinuity.PD.FK.squareLattice_adj_iff]
        exact Or.inr ⟨rfl, Or.inl rfl⟩
      · rw [PottsContinuity.PD.FK.mem_latticeBox] at *
        rcases hz with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
        omega
    · refine ⟨hz, (z.1, z.2 - 1), ?_, ?_⟩
      · rw [PottsContinuity.PD.FK.squareLattice_adj_iff]
        exact Or.inr ⟨rfl, Or.inr (by omega)⟩
      · rw [PottsContinuity.PD.FK.mem_latticeBox] at *
        rcases hz with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
        omega

private theorem annulusExpandedHost_rect_eq_box (N : ℕ) :
    PottsContinuity.PD.FK.latticeRectangle
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2) = latticeBox (0, 0) (2 * N + 1) := by
  ext z
  rw [PottsContinuity.PD.FK.mem_latticeRectangle,
    PottsContinuity.PD.FK.mem_latticeBox]
  simp only [PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor,
    annulusHostAnchor, zero_sub, zero_add]
  omega

private theorem annulusHost_rect_eq_box_outer (N : ℕ) :
    PottsContinuity.PD.FK.latticeRectangle
      (annulusHostAnchor N) (4 * N) (4 * N) = latticeBox (0, 0) (2 * N) := by
  ext z
  rw [PottsContinuity.PD.FK.mem_latticeRectangle,
    PottsContinuity.PD.FK.mem_latticeBox]
  simp only [annulusHostAnchor, zero_sub, zero_add]
  omega

private theorem annulusExpandedOuterClass_restrict_iff
    (N : ℕ) (z : LatticeVertex) (hz : z ∈ latticeBox (0, 0) (2 * N)) :
    (z ∈ expandedHostOuterBoundaryCoord N ∨
      ∃ w : LatticeVertex, w ∈ expandedHostOuterBoundaryCoord N ∧
        PottsContinuity.PD.FK.squareLattice.Adj z w) ↔
      z ∈ PottsContinuity.PD.vertexBoundary (latticeBox (0, 0) (2 * N)) := by
  have hExpanded : expandedHostOuterBoundaryCoord N =
      PottsContinuity.PD.vertexBoundary (latticeBox (0, 0) (2 * N + 1)) := by
    unfold expandedHostOuterBoundaryCoord
    rw [annulusExpandedHost_rect_eq_box]
  rw [hExpanded]
  constructor
  · rintro (hb | ⟨w, hw, hzw⟩)
    · have hface := (annulusBox_boundary_iff (2 * N + 1) z).mp hb
      have hzC := (PottsContinuity.PD.FK.mem_latticeBox
        (0, 0) z (2 * N)).mp hz
      have hfalse : False := by
        rcases hface.2 with hx | hnx | hy | hny
        all_goals
          rcases hzC with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
          omega
      exact False.elim hfalse
    · have hwf := (annulusBox_boundary_iff (2 * N + 1) w).mp hw
      have hwC := (PottsContinuity.PD.FK.mem_latticeBox
        (0, 0) w (2 * N + 1)).mp hwf.1
      have hzC := (PottsContinuity.PD.FK.mem_latticeBox
        (0, 0) z (2 * N)).mp hz
      have hadj := (PottsContinuity.PD.FK.squareLattice_adj_iff z w).mp hzw
      have hsmallFace : z.1 = (2 * N : ℤ) ∨ z.1 = -(2 * N : ℤ) ∨
          z.2 = (2 * N : ℤ) ∨ z.2 = -(2 * N : ℤ) := by
        rcases hwf.2 with hwx | hwnx | hwy | hwny
        all_goals
          rcases hadj with ⟨hstep | hstep, heq⟩ | ⟨heq, hstep | hstep⟩
          all_goals
            rcases hwC with ⟨⟨wxl, wxu⟩, ⟨wyl, wyu⟩⟩
            rcases hzC with ⟨⟨zxl, zxu⟩, ⟨zyl, zyu⟩⟩
            omega
      exact (annulusBox_boundary_iff (2 * N) z).2 ⟨hz, hsmallFace⟩
  · intro hb
    have hface := (annulusBox_boundary_iff (2 * N) z).mp hb
    rcases hface with ⟨hzbox, hx | hnx | hy | hny⟩
    · have hzc := (PottsContinuity.PD.FK.mem_latticeBox
        (0, 0) z (2 * N)).mp hzbox
      refine Or.inr ⟨(z.1 + 1, z.2), ?_, ?_⟩
      · apply (annulusBox_boundary_iff (2 * N + 1) (z.1 + 1, z.2)).mpr
        constructor
        · rw [PottsContinuity.PD.FK.mem_latticeBox]
          rcases hzc with ⟨⟨a,b⟩,⟨c,d⟩⟩
          simp only [zero_sub, zero_add] at a b c d ⊢
          constructor <;> constructor <;> omega
        · exact Or.inl (by omega)
      · exact (PottsContinuity.PD.FK.squareLattice_adj_iff _ _).mpr
          (Or.inl ⟨Or.inl rfl, rfl⟩)
    · have hzc := (PottsContinuity.PD.FK.mem_latticeBox
        (0, 0) z (2 * N)).mp hzbox
      refine Or.inr ⟨(z.1 - 1, z.2), ?_, ?_⟩
      · apply (annulusBox_boundary_iff (2 * N + 1) (z.1 - 1, z.2)).mpr
        constructor
        · rw [PottsContinuity.PD.FK.mem_latticeBox]
          rcases hzc with ⟨⟨a,b⟩,⟨c,d⟩⟩
          simp only [zero_sub, zero_add] at a b c d ⊢
          constructor <;> constructor <;> omega
        · exact Or.inr (Or.inl (by omega))
      · exact (PottsContinuity.PD.FK.squareLattice_adj_iff _ _).mpr
          (Or.inl ⟨Or.inr (by omega), rfl⟩)
    · have hzc := (PottsContinuity.PD.FK.mem_latticeBox
        (0, 0) z (2 * N)).mp hzbox
      refine Or.inr ⟨(z.1, z.2 + 1), ?_, ?_⟩
      · apply (annulusBox_boundary_iff (2 * N + 1) (z.1, z.2 + 1)).mpr
        constructor
        · rw [PottsContinuity.PD.FK.mem_latticeBox]
          rcases hzc with ⟨⟨a,b⟩,⟨c,d⟩⟩
          simp only [zero_sub, zero_add] at a b c d ⊢
          constructor <;> constructor <;> omega
        · exact Or.inr (Or.inr (Or.inl (by omega)))
      · exact (PottsContinuity.PD.FK.squareLattice_adj_iff _ _).mpr
          (Or.inr ⟨rfl, Or.inl rfl⟩)
    · have hzc := (PottsContinuity.PD.FK.mem_latticeBox
        (0, 0) z (2 * N)).mp hzbox
      refine Or.inr ⟨(z.1, z.2 - 1), ?_, ?_⟩
      · apply (annulusBox_boundary_iff (2 * N + 1) (z.1, z.2 - 1)).mpr
        constructor
        · rw [PottsContinuity.PD.FK.mem_latticeBox]
          rcases hzc with ⟨⟨a,b⟩,⟨c,d⟩⟩
          simp only [zero_sub, zero_add] at a b c d ⊢
          constructor <;> constructor <;> omega
        · exact Or.inr (Or.inr (Or.inr (by omega)))
      · exact (PottsContinuity.PD.FK.squareLattice_adj_iff _ _).mpr
          (Or.inr ⟨rfl, Or.inr (by omega)⟩)

theorem annulusCandidateActive_outerClass_iff
    (N : ℕ) (hN : 2 ≤ N)
    (u : {v : LatticeVertex // v ∈ annulusVertexSet N}) :
    annulusCandidateDualOuterHostVertexEquiv N
        (positiveActiveInclusion (rectangleSubgraphDualGraph
          (PottsContinuity.Thm3.Easy.annulusExpandedHostDualCandidateGraph_le_rectangle N))
          ((PottsContinuity.Thm3.Easy.annulusCandidateDoubleDualActiveVertexEquiv N hN).symm u)) ∈
      annulusExpandedHostPrimalOuterClass N ↔
    u ∈ annulusPrimalOuterBoundaryClass N (by omega) := by
  let c : RectangleVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2) := annulusCandidateDualOuterHostVertexEquiv N
        (positiveActiveInclusion (rectangleSubgraphDualGraph
          (PottsContinuity.Thm3.Easy.annulusExpandedHostDualCandidateGraph_le_rectangle N))
          ((PottsContinuity.Thm3.Easy.annulusCandidateDoubleDualActiveVertexEquiv N hN).symm u))
  have hc : c.1 = u.1 := by
    calc
      c.1 = (annulusExpandedHostEmbedding N u).1 := by
        dsimp [c]
        exact annulusCandidateActive_toExpandedHostEmbedding_eq N hN u
      _ = u.1 := rfl
  have huBox : u.1 ∈ latticeBox (0, 0) (2 * N) :=
    (Finset.mem_sdiff.mp u.2).1
  have hrestrict := annulusExpandedOuterClass_restrict_iff N u.1 huBox
  have hclass : c ∈ annulusExpandedHostPrimalOuterClass N ↔
      (c.1 ∈ expandedHostOuterBoundaryCoord N ∨
        ∃ w : LatticeVertex, w ∈ expandedHostOuterBoundaryCoord N ∧
          PottsContinuity.PD.FK.squareLattice.Adj c.1 w) := by
    change (c.1 ∈ expandedHostOuterBoundaryCoord N ∨
      ∃ w : RectangleVertex
        (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
        (4 * N + 2) (4 * N + 2),
        w.1 ∈ expandedHostOuterBoundaryCoord N ∧
          (rectangleGraph
            (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
            (4 * N + 2) (4 * N + 2)).Adj c w) ↔ _
    constructor
    · rintro (hB | ⟨w, hwB, hadj⟩)
      · exact Or.inl hB
      · exact Or.inr ⟨w.1, hwB,
          (PottsContinuity.PD.FK.rectangleGraph_adj_iff
            (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
            (4 * N + 2) (4 * N + 2) c w).mp hadj⟩
    · rintro (hB | ⟨w, hwB, hadj⟩)
      · exact Or.inl hB
      · have hwRect : w ∈ PottsContinuity.PD.FK.latticeRectangle
          (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
          (4 * N + 2) (4 * N + 2) := by
          change w ∈ PottsContinuity.PD.vertexBoundary
            (PottsContinuity.PD.FK.latticeRectangle
              (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
              (4 * N + 2) (4 * N + 2)) at hwB
          rw [PottsContinuity.PD.vertexBoundary] at hwB
          exact hwB.1
        exact Or.inr ⟨⟨w, hwRect⟩, hwB,
          (PottsContinuity.PD.FK.rectangleGraph_adj_iff
            (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
            (4 * N + 2) (4 * N + 2) c ⟨w, hwRect⟩).mpr hadj⟩
  have hrestrictOld := hrestrict
  rw [← annulusHost_rect_eq_box_outer N] at hrestrictOld
  change c ∈ annulusExpandedHostPrimalOuterClass N ↔
    annulusSourceEmbedding N u ∈ annulusHostPrimalOuterClass N
  rw [hclass]
  change (c.1 ∈ expandedHostOuterBoundaryCoord N ∨
      ∃ w : LatticeVertex, w ∈ expandedHostOuterBoundaryCoord N ∧
        PottsContinuity.PD.FK.squareLattice.Adj c.1 w) ↔
    u.1 ∈ PottsContinuity.PD.vertexBoundary
      (PottsContinuity.PD.FK.latticeRectangle
        (annulusHostAnchor N) (4 * N) (4 * N))
  rw [hc]
  exact hrestrictOld

end
end PottsContinuity.DualityExt
