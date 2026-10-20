module

public import PottsContinuity.DualityExt.AnnulusCandidateBoundaryPartition
public import PottsContinuity.DualityExt.AnnulusOuterHostGeometry
public import PottsContinuity.Thm3.Easy.P5AnnulusDoubleDualActiveGeometry

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial

noncomputable section

/-- The candidate active dual graph transported into the expanded rectangle
is exactly the annulus source graph in its expanded-host embedding. -/
theorem annulusCandidateDualOuterHostGraph_map_toExpandedHost_eq
    (N : ℕ) (hN : 2 ≤ N) :
    let hK := PottsContinuity.Thm3.Easy.annulusExpandedHostDualCandidateGraph_le_rectangle N
    let J := rectangleSubgraphDualGraph hK
    J.map (annulusCandidateDualOuterHostVertexEquiv N).toEmbedding =
      (annulusSourceGraph N).map (annulusExpandedHostEmbedding N) := by
  dsimp
  let hK := PottsContinuity.Thm3.Easy.annulusExpandedHostDualCandidateGraph_le_rectangle N
  let J := rectangleSubgraphDualGraph hK
  let A := positiveActiveGraph J
  let i := positiveActiveInclusion J
  let e := PottsContinuity.Thm3.Easy.annulusCandidateDoubleDualActiveVertexEquiv N hN
  let phi := annulusCandidateDualOuterHostVertexEquiv N
  let f := annulusExpandedHostEmbedding N
  let gamma : positiveActiveVertexSet J ↪ _ := i.trans phi.toEmbedding
  let delta : positiveActiveVertexSet J ↪ _ := e.toEmbedding.trans f
  have hpoint (z : positiveActiveVertexSet J) : phi (i z) = f (e z) := by
    apply Subtype.ext
    have hp := annulusCandidateActive_toExpandedHostEmbedding_eq N hN (e z)
    rw [Equiv.symm_apply_apply] at hp
    exact hp
  have hgamma : gamma = delta := by
    apply Function.Embedding.ext
    exact hpoint
  have hactive : A.map e.toEmbedding = annulusSourceGraph N := by
    simpa [hK, J, A, e] using
      PottsContinuity.Thm3.Easy.annulusCandidateDoubleDualActiveGraph_map_eq N hN
  calc
    J.map phi.toEmbedding = (A.map i).map phi.toEmbedding := by
      rw [positiveActiveGraph_map_subtype J]
    _ = A.map gamma := by
      rw [SimpleGraph.map_map]
      rfl
    _ = A.map delta := by rw [hgamma]
    _ = (A.map e.toEmbedding).map f := by
      rw [SimpleGraph.map_map]
      change A.map (e.toEmbedding.trans f) = A.map (f ∘ e.toEmbedding)
      rfl
    _ = (annulusSourceGraph N).map f := by rw [hactive]

/-- Each removed edge of the annulus candidate dual graph maps to an edge
missing from the embedded source graph. Its endpoints lie together in one of
the enlarged-host inner and outer classes. -/
theorem annulusCandidateRemovedDualEdge_missingAndTwoBlock
    (N : ℕ) (hN : 2 ≤ N)
    (d : (rectangleDualGraph
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1)).edgeSet)
    (hd : d ∈ rectangleSubgraphRemovedDualEdges
      (PottsContinuity.Thm3.Easy.annulusExpandedHostDualCandidateGraph_le_rectangle N)) :
    (Sym2.mk (annulusCandidateDualOuterHostVertexEquiv N d.1.out.1)
        (annulusCandidateDualOuterHostVertexEquiv N d.1.out.2) ∉
          ((annulusSourceGraph N).map (annulusExpandedHostEmbedding N)).edgeSet ∧
      (∀ ⦃u : RectangleVertex
        (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
        (4 * N + 2) (4 * N + 2)⦄,
        u ∈ Sym2.mk (annulusCandidateDualOuterHostVertexEquiv N d.1.out.1)
          (annulusCandidateDualOuterHostVertexEquiv N d.1.out.2) →
        u ∈ annulusExpandedHostPrimalInnerClass N)) ∨
    (Sym2.mk (annulusCandidateDualOuterHostVertexEquiv N d.1.out.1)
        (annulusCandidateDualOuterHostVertexEquiv N d.1.out.2) ∉
          ((annulusSourceGraph N).map (annulusExpandedHostEmbedding N)).edgeSet ∧
      (∀ ⦃u : RectangleVertex
        (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
        (4 * N + 2) (4 * N + 2)⦄,
        u ∈ Sym2.mk (annulusCandidateDualOuterHostVertexEquiv N d.1.out.1)
          (annulusCandidateDualOuterHostVertexEquiv N d.1.out.2) →
        u ∈ annulusExpandedHostPrimalOuterClass N)) := by
  let a := PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N
  let w := 4 * N + 1
  let hK := PottsContinuity.Thm3.Easy.annulusExpandedHostDualCandidateGraph_le_rectangle N
  let J := rectangleSubgraphDualGraph hK
  let H := rectangleDualGraph a w w
  let phi := annulusCandidateDualOuterHostVertexEquiv N
  let f := annulusExpandedHostEmbedding N
  have hnotJ : d.1 ∉ J.edgeSet := by
    change d.1 ∉ (edgeRestriction H (rectangleSubgraphRemovedDualEdges hK)).edgeSet
    rw [edgeRestriction_edgeSet]
    intro hdJ
    have hopen : d.1 ∈ openEdges H (rectangleSubgraphRemovedDualEdges hK) := by
      rw [openEdges]
      exact ⟨d, hd, rfl⟩
    exact hdJ.2 hopen
  have hpairD : Sym2.mk d.1.out.1 d.1.out.2 = d.1 := Quot.out_eq _
  have hmemD : Sym2.mk d.1.out.1 d.1.out.2 ∈ H.edgeSet := by
    rw [hpairD]
    exact d.property
  have hadjD : H.Adj d.1.out.1 d.1.out.2 := H.mem_edgeSet.mp hmemD
  have hadjAmb : (rectangleDualAmbientGraph a w w).Adj d.1.out.1 d.1.out.2 :=
    rectangleDualGraph_le_ambient a w w hadjD
  have hadjHost : (rectangleGraph
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)).Adj (phi d.1.out.1) (phi d.1.out.2) := by
    have hmapAmbient := annulusCandidateDualAmbientGraph_map_toOuterRectangle_eq N
    have hadjMapped :
        ((rectangleDualAmbientGraph a w w).map phi.toEmbedding).Adj
          (phi d.1.out.1) (phi d.1.out.2) := by
      rw [SimpleGraph.map_adj]
      exact ⟨d.1.out.1, d.1.out.2, hadjAmb, rfl, rfl⟩
    rw [hmapAmbient] at hadjMapped
    exact hadjMapped
  let edgeHost : (rectangleGraph
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)).edgeSet :=
    ⟨Sym2.mk (phi d.1.out.1) (phi d.1.out.2), hadjHost⟩
  have hmiss : edgeHost.1 ∉ ((annulusSourceGraph N).map f).edgeSet := by
    intro he
    have hepair : Sym2.mk (phi d.1.out.1) (phi d.1.out.2) ∈ ((annulusSourceGraph N).map f).edgeSet := by
      change Sym2.mk (phi d.1.out.1) (phi d.1.out.2) ∈ ((annulusSourceGraph N).map f).edgeSet at he
      exact he
    have hsourceAdj : ((annulusSourceGraph N).map f).Adj
        (phi d.1.out.1) (phi d.1.out.2) :=
      ((annulusSourceGraph N).map f).mem_edgeSet.mp hepair
    have hmap := annulusCandidateDualOuterHostGraph_map_toExpandedHost_eq N hN
    rw [← hmap, SimpleGraph.map_adj] at hsourceAdj
    rcases hsourceAdj with ⟨x, y, hxy, hx, hy⟩
    have hx' : x = d.1.out.1 := phi.injective hx
    have hy' : y = d.1.out.2 := phi.injective hy
    subst x
    subst y
    apply hnotJ
    rw [← hpairD]
    exact J.mem_edgeSet.mpr hxy
  have hclasses := annulusExpandedHost_sourceMissingEdge_twoBlock N edgeHost hmiss
  rcases hclasses with hI | hO
  · left
    refine ⟨?_, ?_⟩
    · change edgeHost.1 ∉ ((annulusSourceGraph N).map f).edgeSet
      exact hmiss
    intro u hu
    change u ∈ edgeHost.1 at hu
    exact hI hu
  · right
    refine ⟨?_, ?_⟩
    · change edgeHost.1 ∉ ((annulusSourceGraph N).map f).edgeSet
      exact hmiss
    intro u hu
    change u ∈ edgeHost.1 at hu
    exact hO hu

end
end PottsContinuity.DualityExt
