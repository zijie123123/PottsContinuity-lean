module

public import PottsContinuity.Thm3.Prop4.MarkedHalfTurnSampledBonds

/-! # Exact half-turn covariance of raw sampled explorations -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- The sampled closed-dual graph transforms in BOTH directions, including
all original bond labels and isolated exterior face labels. -/
theorem markedFaceHalfTurn_sampledClosed_adj_iff (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (x y : LatticeVertex) :
    (PlanarTopology.rectangleSampledClosedDualGraph (markedHalfTurnAnchor a w h) w h
      (configurationIso (markedRectangleHalfTurnIso a w h) A)).Adj
      (markedFaceHalfTurn x) (markedFaceHalfTurn y) ↔
      (PlanarTopology.rectangleSampledClosedDualGraph a w h A).Adj x y := by
  constructor
  · rintro ⟨d,hd,hpair⟩
    let e := (configurationIsoEdgeEquiv (markedRectangleHalfTurnIso a w h)).symm d.primalEdge
    have heMap : configurationIsoEdgeEquiv (markedRectangleHalfTurnIso a w h) e = d.primalEdge :=
      (configurationIsoEdgeEquiv (markedRectangleHalfTurnIso a w h)).apply_symm_apply _
    have heClosed : e ∉ A := by
      intro he
      apply hd
      exact Finset.mem_map.mpr ⟨e,he,heMap⟩
    have hs : d.crossingBond.source = markedFaceHalfTurn (rectangleCrossingDualBond a w h e).target := by
      rw [d.crossingBond_eq,← heMap]
      exact rectangleCrossingDualBond_markedHalfTurn_source a w h e
    have ht : d.crossingBond.target = markedFaceHalfTurn (rectangleCrossingDualBond a w h e).source := by
      rw [d.crossingBond_eq,← heMap]
      exact rectangleCrossingDualBond_markedHalfTurn_target a w h e
    have hinj := markedFaceHalfTurn_involutive.injective
    refine ⟨rectanglePrimalDualEdgeEquiv a w h e,heClosed,?_⟩
    rcases hpair with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact Or.inr ⟨hinj (hx.trans hs),hinj (hy.trans ht)⟩
    · exact Or.inl ⟨hinj (hx.trans ht),hinj (hy.trans hs)⟩
  · exact (markedHalfTurnSampledClosedDualHom a w h A).map_adj

/-- The literal dual face involution is an isomorphism of the sampled
closed-dual graphs, not merely a map of a convenient auxiliary graph. -/
def markedHalfTurnSampledClosedDualIso (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    PlanarTopology.rectangleSampledClosedDualGraph a w h A ≃g
      PlanarTopology.rectangleSampledClosedDualGraph (markedHalfTurnAnchor a w h) w h
        (configurationIso (markedRectangleHalfTurnIso a w h) A) where
  toEquiv := {
    toFun := markedFaceHalfTurn
    invFun := markedFaceHalfTurn
    left_inv := markedFaceHalfTurn_involutive
    right_inv := markedFaceHalfTurn_involutive }
  map_rel_iff' := markedFaceHalfTurn_sampledClosed_adj_iff a w h A _ _

/-- The entire reached seed region transforms exactly under the half-turn. -/
theorem sampledDualSeedRegion_markedHalfTurn_iff (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (S : Set LatticeVertex) (f : LatticeVertex) :
    sampledDualSeedRegion (markedHalfTurnAnchor a w h) w h
      (configurationIso (markedRectangleHalfTurnIso a w h) A)
      (markedFaceHalfTurn '' S) (markedFaceHalfTurn f) ↔ sampledDualSeedRegion a w h A S f := by
  constructor
  · rintro ⟨s,⟨t,ht,rfl⟩,hp⟩
    have hback := hp.map (markedHalfTurnSampledClosedDualIso a w h A).symm.toHom
    change (PlanarTopology.rectangleSampledClosedDualGraph a w h A).Reachable
      (markedFaceHalfTurn (markedFaceHalfTurn t)) (markedFaceHalfTurn (markedFaceHalfTurn f)) at hback
    rw [markedFaceHalfTurn_involutive t,markedFaceHalfTurn_involutive f] at hback
    exact ⟨t,ht,hback⟩
  · rintro ⟨s,hs,hp⟩
    exact ⟨markedFaceHalfTurn s,⟨s,hs,rfl⟩,hp.map (markedHalfTurnSampledClosedDualIso a w h A).toHom⟩

/-- The exact raw queried edge set transforms without adding or removing
any original sampled bond. -/
theorem sampledRawDualReveal_markedHalfTurn (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (S : Set LatticeVertex) :
    configurationIso (markedRectangleHalfTurnIso a w h) (sampledRawDualReveal a w h S A) =
      sampledRawDualReveal (markedHalfTurnAnchor a w h) w h (markedFaceHalfTurn '' S)
        (configurationIso (markedRectangleHalfTurnIso a w h) A) := by
  classical
  ext e'
  obtain ⟨e,rfl⟩ := (configurationIsoEdgeEquiv (markedRectangleHalfTurnIso a w h)).surjective e'
  have hmem : configurationIsoEdgeEquiv (markedRectangleHalfTurnIso a w h) e ∈
      configurationIso (markedRectangleHalfTurnIso a w h) (sampledRawDualReveal a w h S A) ↔
      e ∈ sampledRawDualReveal a w h S A := by
    change _ ∈ (sampledRawDualReveal a w h S A).map
      (configurationIsoEdgeEquiv (markedRectangleHalfTurnIso a w h)).toEmbedding ↔ _
    constructor
    · intro he
      obtain ⟨f,hf,hfe⟩ := Finset.mem_map.mp he
      exact ((configurationIsoEdgeEquiv (markedRectangleHalfTurnIso a w h)).injective hfe) ▸ hf
    · intro he
      exact Finset.mem_map.mpr ⟨e,he,rfl⟩
  rw [hmem]
  simp only [sampledRawDualReveal,rawFaceRegionReveal,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [rectangleCrossingDualBond_markedHalfTurn_source,rectangleCrossingDualBond_markedHalfTurn_target,
    sampledDualSeedRegion_markedHalfTurn_iff,sampledDualSeedRegion_markedHalfTurn_iff]
  exact or_comm

/-- The original upper seed arc transforms to the lower arc at the actual
rotated exchanged marks, as an equality of whole face-label sets. -/
theorem markedFaceHalfTurn_image_upper_arc (a : LatticeVertex) (w h : ℕ) (u v : LatticeVertex) :
    markedFaceHalfTurn '' PlanarTopology.rectangleUpperDualArc a w h u v =
      PlanarTopology.rectangleLowerDualArc (markedHalfTurnAnchor a w h) w h (-v) (-u) := by
  ext f
  constructor
  · rintro ⟨s,hs,rfl⟩
    exact (markedFaceHalfTurn_lower_arc_iff a w h u v s).mpr hs
  · intro hf
    refine ⟨markedFaceHalfTurn f,?_,markedFaceHalfTurn_involutive f⟩
    apply (markedFaceHalfTurn_lower_arc_iff a w h u v (markedFaceHalfTurn f)).mp
    rwa [markedFaceHalfTurn_involutive f]

/-- The ACTUAL upper raw exploration is exactly the inverse-rotated lower
raw exploration at the exchanged marks, with the sampled original law retained. -/
theorem sampledUpperRawReveal_markedHalfTurn (a : LatticeVertex) (w h : ℕ)
    (u v : LatticeVertex) (A : Configuration (rectangleGraph a w h)) :
    configurationIso (markedRectangleHalfTurnIso a w h)
      (sampledRawDualReveal a w h (PlanarTopology.rectangleUpperDualArc a w h u v) A) =
      sampledRawDualReveal (markedHalfTurnAnchor a w h) w h
        (PlanarTopology.rectangleLowerDualArc (markedHalfTurnAnchor a w h) w h (-v) (-u))
        (configurationIso (markedRectangleHalfTurnIso a w h) A) := by
  rw [sampledRawDualReveal_markedHalfTurn,markedFaceHalfTurn_image_upper_arc]

end
end PottsContinuity.Thm3.Prop4
