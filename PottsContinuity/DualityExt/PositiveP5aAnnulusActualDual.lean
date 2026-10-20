module

public import PottsContinuity.DualityExt.PositiveAnnulusDualShell
public import PottsContinuity.DualityExt.PositiveP5aAnnulusFit
public import PottsContinuity.DualityExt.PositiveRectangleSubgraphDuality
public import PottsContinuity.DualityExt.PositiveDualSubgraphLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial
open MeasureTheory

noncomputable section

local instance p5aActualFaceGraphEdgeFintype (N : ℕ) :
    Fintype (p5aAnnulusFaceGraph N).edgeSet := Fintype.ofFinite _

local instance p5aActualAnnulusDualEdgeFintype (N : ℕ) :
    Fintype (rectangleSubgraphDualGraph
      (annulusSourceGraph_map_le_host N)).edgeSet := Fintype.ofFinite _

/-- P5a face-base coordinates viewed in the exact host carrier used by the
primal annulus dual graph. -/
def p5aAnnulusFaceBaseEmbeddingActual (N : ℕ) (hN : 2 ≤ N) :
    {v : LatticeVertex // v ∈ p5aAnnulusVertexSet (N - 1)} ↪
      RectangleDualVertex (annulusHostAnchor N) (4 * N) (4 * N) where
  toFun v := ⟨v.1, by
    have hv := p5a_annulus_vertex_mem_dualHost N hN v.2
    simpa only [p5aAnnulusHostAnchor, annulusHostAnchor] using hv⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : RectangleDualVertex
      (annulusHostAnchor N) (4 * N) (4 * N) => z.1) hxy

/-- A P5a face-base vertex lies outside the filled inner face box. -/
theorem p5a_annulus_vertex_not_mem_dualFaceBox
    (N : ℕ) (hN : 2 ≤ N)
    {v : LatticeVertex} (hv : v ∈ p5aAnnulusVertexSet (N - 1)) :
    v ∉ dualFaceBox N := by
  intro hface
  have hbox : v ∈ latticeBox (0, 0) N := by
    rw [mem_latticeBox]
    have hv' := (mem_dualFaceBox N v).mp hface
    omega
  have hnot : v ∉ latticeBox (0, 0) N := by
    intro h
    have hscale : (N - 1) + 1 = N := Nat.sub_add_cancel (by omega)
    have h' : v ∈ latticeBox (0, 0) ((N - 1) + 1) := by
      simpa [hscale] using h
    exact (Finset.mem_sdiff.mp hv).2 h'
  exact hnot hbox

/-- Every P5a annulus edge is retained in the actual edge-deleted dual graph
of the primal annulus. -/
theorem p5aAnnulusFaceGraph_map_le_annulusSourceDualGraph
    (N : ℕ) (hN : 2 ≤ N) :
    (p5aAnnulusFaceGraph N).map (p5aAnnulusFaceBaseEmbedding N hN) ≤
      rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N) := by
  intro u v huv
  rw [SimpleGraph.map_adj] at huv
  rcases huv with ⟨x, y, hxy, rfl, rfl⟩
  let H := rectangleDualGraph (annulusHostAnchor N) (4 * N) (4 * N)
  let R := rectangleSubgraphRemovedDualEdges
    (annulusSourceGraph_map_le_host N)
  let K := edgeRestriction H R
  have hmap : ((p5aAnnulusFaceGraph N).map (p5aAnnulusFaceBaseEmbedding N hN)).Adj
      (p5aAnnulusFaceBaseEmbedding N hN x) (p5aAnnulusFaceBaseEmbedding N hN y) := by
    rw [SimpleGraph.map_adj]
    exact ⟨x, y, hxy, rfl, rfl⟩
  have hfull : H.Adj (p5aAnnulusFaceBaseEmbedding N hN x)
      (p5aAnnulusFaceBaseEmbedding N hN y) := by
    simpa only [H, annulusHostAnchor, p5aAnnulusHostAnchor] using
      (p5a_annulus_faceGraph_map_le_dualHost N hN hmap)
  have hbase : s(p5aAnnulusFaceBaseEmbedding N hN x,
      p5aAnnulusFaceBaseEmbedding N hN y) ∈ H.edgeSet := H.mem_edgeSet.mpr hfull
  let e : H.edgeSet := ⟨s(p5aAnnulusFaceBaseEmbedding N hN x,
      p5aAnnulusFaceBaseEmbedding N hN y), hbase⟩
  have hnot : e ∉ R := by
    intro her
    rcases annulusHost_removedDualEdge_has_innerFaceBox_carrier N (by omega)
        e her with ⟨d, hde, hs, ht⟩
    have hpair : rectangleDualCarrierPair (annulusHostAnchor N)
        (4 * N) (4 * N) d =
          s(p5aAnnulusFaceBaseEmbedding N hN x,
            p5aAnnulusFaceBaseEmbedding N hN y) := by
      have hval := congrArg (fun z : H.edgeSet => z.1) hde
      change rectangleDualCarrierPair (annulusHostAnchor N)
          (4 * N) (4 * N) d = e.1 at hval
      exact hval
    rcases Sym2.eq_iff.mp hpair with ⟨hsx, hty⟩ | ⟨hsy, htx⟩
    · have hsource : d.crossingBond.source = x.1 := by
        have hh := congrArg Subtype.val hsx
        have hh' : d.crossingBond.source =
            (p5aAnnulusFaceBaseEmbedding N hN x).1 := by
          simpa only [rectangleDualEdgeSource_val] using hh
        exact hh'.trans rfl
      exact p5a_annulus_vertex_not_mem_dualFaceBox N hN x.2 (hsource ▸ hs)
    · have htarget : d.crossingBond.target = x.1 := by
        have hh := congrArg Subtype.val htx
        have hh' : d.crossingBond.target =
            (p5aAnnulusFaceBaseEmbedding N hN x).1 := by
          simpa only [rectangleDualEdgeTarget_val] using hh
        exact hh'.trans rfl
      exact p5a_annulus_vertex_not_mem_dualFaceBox N hN x.2 (htarget ▸ ht)
  have hedge : s(p5aAnnulusFaceBaseEmbedding N hN x,
      p5aAnnulusFaceBaseEmbedding N hN y) ∈ K.edgeSet := by
    rw [edgeRestriction_edgeSet]
    exact ⟨hbase, fun hopen => hnot ((coe_mem_openEdges_iff H R e).mp hopen)⟩
  change K.Adj (p5aAnnulusFaceBaseEmbedding N hN x)
      (p5aAnnulusFaceBaseEmbedding N hN y)
  exact K.mem_edgeSet.mpr hedge

/-- The same edge inclusion with the face-base embedding expressed directly in
the annulus host's dual carrier. -/
theorem p5aAnnulusFaceGraphActual_map_le_annulusSourceDualGraph
    (N : ℕ) (hN : 2 ≤ N) :
    (p5aAnnulusFaceGraph N).map (p5aAnnulusFaceBaseEmbeddingActual N hN) ≤
      rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N) := by
  intro u v huv
  rcases (SimpleGraph.map_adj _ _ _ _).mp huv with ⟨x, y, hxy, hxu, hyv⟩
  have hmap : ((p5aAnnulusFaceGraph N).map
      (p5aAnnulusFaceBaseEmbedding N hN)).Adj
      (p5aAnnulusFaceBaseEmbedding N hN x)
      (p5aAnnulusFaceBaseEmbedding N hN y) := by
    rw [SimpleGraph.map_adj]
    exact ⟨x, y, hxy, rfl, rfl⟩
  have hactual := p5aAnnulusFaceGraph_map_le_annulusSourceDualGraph N hN hmap
  have hfx : p5aAnnulusFaceBaseEmbeddingActual N hN x =
      p5aAnnulusFaceBaseEmbedding N hN x := by
    apply Subtype.ext
    rfl
  have hfy : p5aAnnulusFaceBaseEmbeddingActual N hN y =
      p5aAnnulusFaceBaseEmbedding N hN y := by
    apply Subtype.ext
    rfl
  rw [← hxu, ← hyv]
  rw [hfx, hfy]
  exact hactual

end

end PottsContinuity.DualityExt
