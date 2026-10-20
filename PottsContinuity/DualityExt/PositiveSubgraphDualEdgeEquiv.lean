module

public import PottsContinuity.DualityExt.PositiveEmbeddedDualEdgeState
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK

noncomputable section

variable {a : PD.FK.LatticeVertex} {w h : ℕ}
variable {G : SimpleGraph (RectangleVertex a w h)}

/-- The edge set of the dual graph of a rectangle subgraph is in bijection
with the edge set of the primal subgraph. -/
noncomputable def rectangleSubgraphDualEdgeEquiv
    (hG : G ≤ rectangleGraph a w h) :
    G.edgeSet ≃ (rectangleSubgraphDualGraph hG).edgeSet := by
  classical
  let H := rectangleDualGraph a w h
  let R := rectangleSubgraphRemovedDualEdges hG
  let f := rectangleSubgraphDualEdgeEmbedding hG
  have hHost (g : G.edgeSet) :
      edgeRestrictionEdgeEmbedding H R (f g) =
        rectangleDualEdgeEquiv a w h (subgraphEdgeEmbedding hG g) := by
    apply Subtype.ext
    rfl
  refine Equiv.ofBijective f ?_
  constructor
  · intro g g' hgg'
    have hh := congrArg (edgeRestrictionEdgeEmbedding H R) hgg'
    rw [hHost, hHost] at hh
    have hdual := (rectangleDualEdgeEquiv a w h).injective hh
    have hsub := (subgraphEdgeEmbedding hG).injective hdual
    exact hsub
  · intro d
    let dHost : H.edgeSet := edgeRestrictionEdgeEmbedding H R d
    let eHost : (rectangleGraph a w h).edgeSet :=
      (rectangleDualEdgeEquiv a w h).symm dHost
    have hdHost_not_removed : dHost ∉ R := by
      let hpair := edgeRestrictionEdgeEquiv H R d
      have hpairVal : hpair.val.val = d.val := by
        change ((edgeRestrictionEdgeEquiv H R d).val).val = d.val
        rfl
      have heq : dHost = hpair.val := by
        apply Subtype.ext
        calc
          dHost.val = d.val := edgeRestrictionEdgeEmbedding_coe H R d
          _ = hpair.val.val := hpairVal.symm
      rw [heq]
      exact hpair.property
    have heHost_not_removed :
        eHost ∉ subgraphRemovedEdges G (rectangleGraph a w h) := by
      intro he
      have hd : rectangleDualEdgeEquiv a w h eHost ∈ R := by
        unfold R rectangleSubgraphRemovedDualEdges
        rw [Finset.mem_map]
        exact ⟨eHost, he, rfl⟩
      have hEq : rectangleDualEdgeEquiv a w h eHost = dHost :=
        Equiv.apply_symm_apply (rectangleDualEdgeEquiv a w h) dHost
      exact hdHost_not_removed (hEq ▸ hd)
    have heHost_mem : eHost.val ∈ G.edgeSet := by
      by_contra hnot
      exact heHost_not_removed
        ((mem_subgraphRemovedEdges (G := G)
          (H := rectangleGraph a w h) eHost).2 hnot)
    let g : G.edgeSet := ⟨eHost.val, heHost_mem⟩
    refine ⟨g, ?_⟩
    apply (edgeRestrictionEdgeEmbedding H R).injective
    rw [hHost]
    have hgHost : subgraphEdgeEmbedding hG g = eHost := by
      apply Subtype.ext
      rfl
    rw [hgHost]
    exact Equiv.apply_symm_apply (rectangleDualEdgeEquiv a w h) dHost

/-- The edge bijection labels each retained dual edge by the actual dual bond
crossing its primal source edge. -/
theorem rectangleSubgraphDualEdgeEquiv_crossingBond
    (hG : G ≤ rectangleGraph a w h) (g : G.edgeSet) :
    Sym2.map (fun z : RectangleDualVertex a w h => z.1)
        (rectangleSubgraphDualEdgeEquiv hG g).val =
      (PD.FK.Medial.dualBondOfPrimal
        (rectanglePrimalEdgeBond a w h (subgraphEdgeEmbedding hG g))).toSym2 := by
  change Sym2.map (fun z : RectangleDualVertex a w h => z.1)
      (rectangleSubgraphDualEdgeEmbedding hG g).val = _
  exact rectangleSubgraphDualEdgeEmbedding_crossingBond hG g

end

end PottsContinuity.DualityExt
