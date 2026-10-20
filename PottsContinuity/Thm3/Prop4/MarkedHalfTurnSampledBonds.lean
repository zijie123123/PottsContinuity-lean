module

public import PottsContinuity.Thm3.Prop4.MarkedRectangleHalfTurn

/-! # Exact original-bond labels under the sampled dual half-turn -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section

/-- The normalized original bond transforms by its literal coordinate rotation. -/
theorem rectanglePrimalEdgeBond_markedHalfTurn (a : LatticeVertex) (w h : ℕ)
    (e : (rectangleGraph a w h).edgeSet) :
    rectanglePrimalEdgeBond (markedHalfTurnAnchor a w h) w h
      (configurationIsoEdgeEquiv (markedRectangleHalfTurnIso a w h) e) =
    markedBondHalfTurn (rectanglePrimalEdgeBond a w h e) := by
  apply LatticeBond.toSym2_injective
  rw [markedBondHalfTurn_toSym2]
  erw [rectanglePrimalEdgeBond_toSym2_public,rectanglePrimalEdgeBond_toSym2_public]
  change (e.val.map (markedRectangleHalfTurnIso a w h)).map Subtype.val =
    (e.val.map Subtype.val).map (fun x => -x)
  rw [Sym2.map_map,Sym2.map_map]
  rfl

/-- The rotated crossing source is the transformed original crossing target. -/
theorem rectangleCrossingDualBond_markedHalfTurn_source (a : LatticeVertex) (w h : ℕ)
    (e : (rectangleGraph a w h).edgeSet) :
    (rectangleCrossingDualBond (markedHalfTurnAnchor a w h) w h
      (configurationIsoEdgeEquiv (markedRectangleHalfTurnIso a w h) e)).source =
      markedFaceHalfTurn (rectangleCrossingDualBond a w h e).target := by
  unfold rectangleCrossingDualBond
  rw [rectanglePrimalEdgeBond_markedHalfTurn,dualBondOfPrimal_source,dualBondOfPrimal_target]
  have hp := markedBondHalfTurn_faceBase (rectanglePrimalEdgeBond a w h e) true
  simp only [Bool.not_true] at hp
  exact hp

/-- The rotated crossing target is the transformed original crossing source. -/
theorem rectangleCrossingDualBond_markedHalfTurn_target (a : LatticeVertex) (w h : ℕ)
    (e : (rectangleGraph a w h).edgeSet) :
    (rectangleCrossingDualBond (markedHalfTurnAnchor a w h) w h
      (configurationIsoEdgeEquiv (markedRectangleHalfTurnIso a w h) e)).target =
      markedFaceHalfTurn (rectangleCrossingDualBond a w h e).source := by
  unfold rectangleCrossingDualBond
  rw [rectanglePrimalEdgeBond_markedHalfTurn,dualBondOfPrimal_target,dualBondOfPrimal_source]
  have hp := markedBondHalfTurn_faceBase (rectanglePrimalEdgeBond a w h e) false
  simp only [Bool.not_false] at hp
  exact hp

/-- The actual sampled closed-dual graph rotates on its literal face labels,
with the SAME transformed original closed-bond witness on every step. -/
def markedHalfTurnSampledClosedDualHom (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    PlanarTopology.rectangleSampledClosedDualGraph a w h A →g
      PlanarTopology.rectangleSampledClosedDualGraph (markedHalfTurnAnchor a w h) w h
        (configurationIso (markedRectangleHalfTurnIso a w h) A) where
  toFun := markedFaceHalfTurn
  map_rel' := by
    intro x y hxy
    obtain ⟨d,hd,hpair⟩ := hxy
    let e := configurationIsoEdgeEquiv (markedRectangleHalfTurnIso a w h) d.primalEdge
    let d' := rectanglePrimalDualEdgeEquiv (markedHalfTurnAnchor a w h) w h e
    have heClosed : e ∉ configurationIso (markedRectangleHalfTurnIso a w h) A := by
      intro he
      change e ∈ A.map (configurationIsoEdgeEquiv (markedRectangleHalfTurnIso a w h)).toEmbedding at he
      obtain ⟨f,hf,hfe⟩ := Finset.mem_map.mp he
      have heq : f = d.primalEdge := (configurationIsoEdgeEquiv (markedRectangleHalfTurnIso a w h)).injective hfe
      exact hd (heq ▸ hf)
    refine ⟨d',heClosed,?_⟩
    have hs := rectangleCrossingDualBond_markedHalfTurn_source a w h d.primalEdge
    have ht := rectangleCrossingDualBond_markedHalfTurn_target a w h d.primalEdge
    rw [← d.crossingBond_eq] at hs ht
    rcases hpair with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · right
      exact ⟨hx ▸ ht.symm,hy ▸ hs.symm⟩
    · left
      exact ⟨hx ▸ hs.symm,hy ▸ ht.symm⟩

end
end PottsContinuity.Thm3.Prop4
