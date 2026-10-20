module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.RawQueryOriginalIndex
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.ClosedQueryStar

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.FK.Medial PD.Duality Push
noncomputable section

theorem rectangle_auxiliary_edge_original_pair
    (a : LatticeVertex) (w h : ℕ) (e : (rectangleGraph a w h).edgeSet) :
    Sym2.map (fun v : RectangleDualVertex a w h => faceIndexMark v.val)
      (DualityExt.rectangleDualEdgeEquiv a w h e).val =
      (primalBondOfDual (rectanglePrimalEdgeBond a w h e)).toSym2 := by
  let d := rectanglePrimalDualEdgeEquiv a w h e
  let b := rectanglePrimalEdgeBond a w h e
  change s(faceIndexMark (rectangleDualEdgeSource a w h d).val,
    faceIndexMark (rectangleDualEdgeTarget a w h d).val)=_
  rw [rectangleDualEdgeSource_faceBase,rectangleDualEdgeTarget_faceBase]
  change s(faceIndexMark (b.faceBase false),faceIndexMark (b.faceBase true))=(primalBondOfDual b).toSym2
  rw [← (primalBondOfDual_endpoints_faceIndexMark b).1,
    ← (primalBondOfDual_endpoints_faceIndexMark b).2]
  rfl


/-- Literal original endpoint sets agree with the translated auxiliary pair. -/
theorem rectangle_auxiliary_pair_of_original_edge
    (V : Finset LatticeVertex) (a : LatticeVertex) (w h : ℕ)
    (e : (rectangleGraph a w h).edgeSet)
    (b : (squareLattice.induce (V : Set LatticeVertex)).edgeSet)
    (hb : rectangleDualOriginalEdge V a w h e=some b) :
    Sym2.map (fun v : RectangleDualVertex a w h => faceIndexMark v.val)
      (DualityExt.rectangleDualEdgeEquiv a w h e).val = Sym2.map Subtype.val b.val := by
  rw [rectangle_auxiliary_edge_original_pair]
  exact (congrArg Subtype.val ((originalEdgeOfBond_eq_some_iff V _ b).mp hb)).symm

/-- A queried OPEN original bond forces the query of every other represented
original bond sharing an endpoint. This is about the actual queried carrier. -/
theorem complementary_raw_open_query_incident_query
    (V : Finset LatticeVertex) (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (seeds : Finset (RectangleDualVertex a w h))
    (b : (squareLattice.induce (V : Set LatticeVertex)).edgeSet) (hbA : b ∈ A)
    (hb : b ∈ complementaryRevealPullback _ _ (rectangleDualOriginalEdge V a w h)
      (closedClusterReveal (DualityExt.rectangleDualEdgeEquiv a w h) seeds
        (originalClosedDualRectangleRead V a w h A)))
    (d : (squareLattice.induce (V : Set LatticeVertex)).edgeSet)
    (f : (rectangleGraph a w h).edgeSet)
    (hf : rectangleDualOriginalEdge V a w h f=some d)
    (u : (V : Set LatticeVertex)) (hub : u ∈ b.val) (hud : u ∈ d.val) :
    d ∈ complementaryRevealPullback _ _ (rectangleDualOriginalEdge V a w h)
      (closedClusterReveal (DualityExt.rectangleDualEdgeEquiv a w h) seeds
        (originalClosedDualRectangleRead V a w h A)) := by
  obtain ⟨e,he,heb⟩ := (mem_complementaryRevealPullback _ _ _ _ b).mp hb
  have heclosed : e ∉ originalClosedDualRectangleRead V a w h A := by
    intro hm
    exact (mem_complementaryEdgeRead _ _ _ A e).mp hm b heb hbA
  have hub' : u.val ∈ Sym2.map Subtype.val b.val := Sym2.mem_map.mpr ⟨u,hub,rfl⟩
  have hud' : u.val ∈ Sym2.map Subtype.val d.val := Sym2.mem_map.mpr ⟨u,hud,rfl⟩
  rw [← rectangle_auxiliary_pair_of_original_edge V a w h e b heb] at hub'
  rw [← rectangle_auxiliary_pair_of_original_edge V a w h f d hf] at hud'
  obtain ⟨v,hv,hvu⟩ := Sym2.mem_map.mp hub'
  obtain ⟨t,ht,htu⟩ := Sym2.mem_map.mp hud'
  have hvt : v=t := by
    apply Subtype.ext
    have hmark := hvu.trans htu.symm
    have hx := congrArg Prod.fst hmark
    have hy := congrArg Prod.snd hmark
    apply Prod.ext
    · simpa only [faceIndexMark,Prod.fst,add_left_inj] using hx
    · simpa only [faceIndexMark,Prod.snd,add_left_inj] using hy
  have hfquery := closedClusterReveal_closed_edge_incident_query
    (DualityExt.rectangleDualEdgeEquiv a w h) seeds
    (originalClosedDualRectangleRead V a w h A) e he heclosed v hv f (hvt ▸ ht)
  exact (mem_complementaryRevealPullback _ _ _ _ d).mpr ⟨f,hfquery,hf⟩

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
