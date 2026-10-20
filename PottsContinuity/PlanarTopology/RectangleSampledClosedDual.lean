module

public import PottsContinuity.PlanarTopology.RectangleBoundaryArcExclusion
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial
noncomputable section

/-- The actual sampled rectangle closed-dual graph on original whole-plane
face labels. Its only edges cross closed ORIGINAL rectangle bonds. Faces
outside the sampled dual graph remain isolated; no exterior cap is supplied. -/
def rectangleSampledClosedDualGraph (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) : SimpleGraph LatticeVertex where
  Adj s t := ∃ e : RectangleDualEdgeCarrier a w h, e.primalEdge ∉ A ∧
    ((s = e.crossingBond.source ∧ t = e.crossingBond.target) ∨
      (s = e.crossingBond.target ∧ t = e.crossingBond.source))
  symm := ⟨by
    rintro s t ⟨e,he,⟨hs,ht⟩ | ⟨hs,ht⟩⟩
    · exact ⟨e,he,Or.inr ⟨ht,hs⟩⟩
    · exact ⟨e,he,Or.inl ⟨ht,hs⟩⟩⟩
  loopless := ⟨by
    rintro s ⟨e,_,⟨hs,ht⟩ | ⟨hs,ht⟩⟩
    · exact e.crossingBond.source_ne_target (hs.symm.trans ht)
    · exact e.crossingBond.source_ne_target (ht.symm.trans hs)⟩

/-- Every genuine sampled dual edge has both endpoints in the expanded face carrier. -/
theorem rectangleSampledClosedDualGraph_adj_mem (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) {s t : LatticeVertex}
    (hadj : (rectangleSampledClosedDualGraph a w h A).Adj s t) :
    s ∈ rectangleDualExpanded a w h ∧ t ∈ rectangleDualExpanded a w h := by
  obtain ⟨e,_,⟨hs,ht⟩ | ⟨hs,ht⟩⟩ := hadj
  · exact ⟨hs ▸ (rectangleDualEdgeSource a w h e).property,
      ht ▸ (rectangleDualEdgeTarget a w h e).property⟩
  · exact ⟨hs ▸ (rectangleDualEdgeTarget a w h e).property,
      ht ▸ (rectangleDualEdgeSource a w h e).property⟩

/-- Restore the finite carrier without changing an original sampled dual edge. -/
theorem rectangleSampledClosedDualGraph_adj_finite (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) {s t : LatticeVertex}
    (hs : s ∈ rectangleDualExpanded a w h) (ht : t ∈ rectangleDualExpanded a w h)
    (hadj : (rectangleSampledClosedDualGraph a w h A).Adj s t) :
    (openGraph (rectangleDualGraph a w h) (rectangleDualConfiguration a w h A)).Adj
      ⟨s,hs⟩ ⟨t,ht⟩ := by
  obtain ⟨e,he,hst⟩ := hadj
  apply (openGraph_adj _ _ _ _).mpr
  refine ⟨rectangleDualGraphEdgeEquiv a w h e,
    (mem_rectangleDualConfiguration a w h A e).mpr he,?_⟩
  change rectangleDualCarrierPair a w h e = s(⟨s,hs⟩,⟨t,ht⟩)
  apply Sym2.map.injective Subtype.val_injective
  change s(e.crossingBond.source,e.crossingBond.target) = s(s,t)
  rcases hst with ⟨hs,ht⟩ | ⟨hs,ht⟩
  · exact Sym2.eq_iff.mpr (Or.inl ⟨hs.symm,ht.symm⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨ht.symm,hs.symm⟩)

/-- A sampled dual walk on face labels lifts to the finite dual graph, retaining
its original sampled configuration and literal endpoints. -/
theorem rectangleSampledClosedDualGraph_walk_finite (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) {s t : LatticeVertex}
    (p : (rectangleSampledClosedDualGraph a w h A).Walk s t)
    (hs : s ∈ rectangleDualExpanded a w h) (ht : t ∈ rectangleDualExpanded a w h) :
    Nonempty ((openGraph (rectangleDualGraph a w h) (rectangleDualConfiguration a w h A)).Walk
      ⟨s,hs⟩ ⟨t,ht⟩) := by
  induction p with
  | nil => exact ⟨.nil⟩
  | @cons s r t hsr p ih =>
    have hr := (rectangleSampledClosedDualGraph_adj_mem a w h A hsr).2
    obtain ⟨q⟩ := ih hr ht
    exact ⟨.cons (rectangleSampledClosedDualGraph_adj_finite a w h A hs hr hsr) q⟩

/-- Closing an original sampled bond supplies its genuine crossing dual edge. -/
theorem rectangleSampledClosedDualGraph_adj_of_closed_bond (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (b : RectanglePrimalBond a w h)
    (hb : rectanglePrimalBondToEdge a w h b ∉ A) :
    (rectangleSampledClosedDualGraph a w h A).Adj
      (dualBondOfPrimal b.val).source (dualBondOfPrimal b.val).target := by
  let e := rectanglePrimalBondToEdge a w h b
  let d := rectanglePrimalDualEdgeEquiv a w h e
  have he : rectanglePrimalEdgeBond a w h e = b.val :=
    congrArg Subtype.val ((rectanglePrimalEdgeBondEquiv a w h).right_inv b)
  have hd : d.crossingBond = dualBondOfPrimal b.val := by
    change rectangleCrossingDualBond a w h e = dualBondOfPrimal b.val
    rw [rectangleCrossingDualBond,he]
  refine ⟨d,hb,Or.inl ?_⟩
  rw [hd]
  exact ⟨rfl,rfl⟩

end
end PottsContinuity.PlanarTopology
