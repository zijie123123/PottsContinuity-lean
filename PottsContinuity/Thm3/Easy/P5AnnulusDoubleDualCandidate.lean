module

public import PottsContinuity.Thm3.Easy.P5AnnulusCarrierErratum
public import PottsContinuity.DualityExt.PositiveP5aAnnulusMergeActualDual
public import PottsContinuity.DualityExt.PositiveP5aAnnulusMapByEdge

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open PottsContinuity.PD.FK
open PottsContinuity.DualityExt
open PottsContinuity.PD.FK.Medial

noncomputable section

private theorem doubleDualBond_source_shift (b : LatticeBond) :
    let d := dualBondOfPrimal (dualBondOfPrimal b)
    (d.source.1 + 1, d.source.2 + 1) = b.source := by
  rcases b with ⟨⟨x, y⟩, axis⟩
  cases axis <;> simp [dualBondOfPrimal, LatticeBond.source]

private theorem doubleDualBond_target_shift (b : LatticeBond) :
    let d := dualBondOfPrimal (dualBondOfPrimal b)
    (d.target.1 + 1, d.target.2 + 1) = b.target := by
  rcases b with ⟨⟨x, y⟩, axis⟩
  cases axis <;> simp [dualBondOfPrimal, LatticeBond.target]

noncomputable def annulusCandidateDoubleDualEdgeEquiv (N : ℕ) :
    (annulusSourceGraph N).edgeSet ≃
      (rectangleSubgraphDualGraph
        (annulusExpandedHostDualCandidateGraph_le_rectangle N)).edgeSet := by
  let hK := annulusExpandedHostDualCandidateGraph_le_rectangle N
  let f := annulusExpandedHostCarrierEquiv N
  let hIso := annulusExpandedHostDualCandidateGraph_map_eq N
  exact (p5aSourceToActualDualEdgeEquiv N).trans
    ((p5aCandidateToActualDualEdgeEquiv N f hIso).symm.trans
      (rectangleSubgraphDualEdgeEquiv hK))

noncomputable def annulusCandidatePrimalBond (N : ℕ)
    (g : (annulusExpandedHostDualCandidateGraph N).edgeSet) : LatticeBond := by
  let e : rectanglePrimalEdgeCarrier (annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1) :=
    ⟨(subgraphEdgeEmbedding (annulusExpandedHostDualCandidateGraph_le_rectangle N) g).val,
      by simpa [rectanglePrimalEdgeCarrier] using
        (subgraphEdgeEmbedding (annulusExpandedHostDualCandidateGraph_le_rectangle N) g).property⟩
  exact rectanglePrimalEdgeBond (annulusDualExpandedHostAnchor N)
    (4 * N + 1) (4 * N + 1) e

noncomputable def annulusSourceHostPrimalBond (N : ℕ)
    (b : (annulusSourceGraph N).edgeSet) : LatticeBond := by
  let bHost := isolatedExtensionEdgeEquiv (annulusSourceGraph N)
    (annulusSourceEmbedding N) b
  let e : rectanglePrimalEdgeCarrier (annulusHostAnchor N) (4 * N) (4 * N) := by
    exact ⟨(subgraphEdgeEmbedding (annulusSourceGraph_map_le_host N) bHost).val,
      by simpa [rectanglePrimalEdgeCarrier] using
        (subgraphEdgeEmbedding (annulusSourceGraph_map_le_host N) bHost).property⟩
  exact rectanglePrimalEdgeBond (annulusHostAnchor N) (4 * N) (4 * N) e

private theorem annulusCandidatePrimalBond_toSym2 (N : ℕ)
    (g : (annulusExpandedHostDualCandidateGraph N).edgeSet) :
    (annulusCandidatePrimalBond N g).toSym2 =
      Sym2.map (fun z : RectangleVertex (annulusDualExpandedHostAnchor N)
        (4 * N + 1) (4 * N + 1) => z.1)
        (subgraphEdgeEmbedding (annulusExpandedHostDualCandidateGraph_le_rectangle N) g).val := by
  unfold annulusCandidatePrimalBond
  exact rectanglePrimalEdgeBond_toSym2_public _ _ _ _

private theorem annulusSourceHostPrimalBond_toSym2 (N : ℕ)
    (b : (annulusSourceGraph N).edgeSet) :
    (annulusSourceHostPrimalBond N b).toSym2 =
      Sym2.map (fun z : RectangleVertex (annulusHostAnchor N) (4 * N) (4 * N) => z.1)
        (subgraphEdgeEmbedding (annulusSourceGraph_map_le_host N)
          (isolatedExtensionEdgeEquiv (annulusSourceGraph N)
            (annulusSourceEmbedding N) b)).val := by
  unfold annulusSourceHostPrimalBond
  exact rectanglePrimalEdgeBond_toSym2_public _ _ _ _

private theorem annulusCandidateDoubleDualEdge_pair (N : ℕ)
    (b : (annulusSourceGraph N).edgeSet) :
    let _hK := annulusExpandedHostDualCandidateGraph_le_rectangle N
    let d := annulusCandidateDoubleDualEdgeEquiv N b
    Sym2.map (fun z : RectangleDualVertex (annulusDualExpandedHostAnchor N)
        (4 * N + 1) (4 * N + 1) => z.1) d.val =
      (dualBondOfPrimal (dualBondOfPrimal
        (annulusSourceHostPrimalBond N b))).toSym2 := by
  let hK := annulusExpandedHostDualCandidateGraph_le_rectangle N
  let f := annulusExpandedHostCarrierEquiv N
  let hIso := annulusExpandedHostDualCandidateGraph_map_eq N
  let hSource := annulusSourceGraph_map_le_host N
  let gH := p5aSourceToActualDualEdgeEquiv N b
  let gK := (p5aCandidateToActualDualEdgeEquiv N f hIso).symm gH
  let gD := rectangleSubgraphDualEdgeEquiv hK gK
  let bHost := isolatedExtensionEdgeEquiv (annulusSourceGraph N)
    (annulusSourceEmbedding N) b
  have himage : p5aCandidateToActualDualEdgeEquiv N f hIso gK = gH :=
    Equiv.apply_symm_apply _ _
  have hKpair : (annulusCandidatePrimalBond N gK).toSym2 =
      (dualBondOfPrimal (annulusSourceHostPrimalBond N b)).toSym2 := by
    rw [annulusCandidatePrimalBond_toSym2]
    have himageVal :
        (isolatedExtensionEdgeEquiv
          (annulusExpandedHostDualCandidateGraph N) f.toEmbedding gK).val = gH.val := by
      have h := congrArg Subtype.val himage
      simpa [p5aCandidateToActualDualEdgeEquiv] using h
    have hpairMap := rectangleSubgraphDualEdgeEquiv_crossingBond hSource bHost
    have hGHEdge : gH = rectangleSubgraphDualEdgeEquiv hSource bHost := by
      dsimp [gH, p5aSourceToActualDualEdgeEquiv, bHost]
    have hKmap :
        Sym2.map (fun z : RectangleVertex (annulusDualExpandedHostAnchor N)
            (4 * N + 1) (4 * N + 1) => (f z).1)
            (subgraphEdgeEmbedding hK gK).val =
          Sym2.map (fun z : RectangleDualVertex (annulusHostAnchor N)
            (4 * N) (4 * N) => z.1) gH.val := by
      calc
        _ = Sym2.map (fun z : RectangleDualVertex (annulusHostAnchor N)
              (4 * N) (4 * N) => z.1)
              (isolatedExtensionEdgeEquiv
                (annulusExpandedHostDualCandidateGraph N) f.toEmbedding gK).val := by
          rw [subgraphEdgeEmbedding_coe, isolatedExtensionEdgeEquiv_coe,
            Function.Embedding.sym2Map_apply, Sym2.map_map]
          rfl
        _ = Sym2.map (fun z : RectangleDualVertex (annulusHostAnchor N)
              (4 * N) (4 * N) => z.1) gH.val := by rw [himageVal]
    have hKmap' :
        Sym2.map (fun z : RectangleVertex (annulusDualExpandedHostAnchor N)
            (4 * N + 1) (4 * N + 1) => z.1)
            (subgraphEdgeEmbedding hK gK).val =
          Sym2.map (fun z : RectangleDualVertex (annulusHostAnchor N)
            (4 * N) (4 * N) => z.1) gH.val := by
      simpa [f, annulusExpandedHostCarrierEquiv] using hKmap
    calc
      _ = Sym2.map (fun z : RectangleVertex (annulusDualExpandedHostAnchor N)
            (4 * N + 1) (4 * N + 1) => z.1)
            (subgraphEdgeEmbedding hK gK).val := by
              simp only
      _ = Sym2.map (fun z : RectangleDualVertex (annulusHostAnchor N)
            (4 * N) (4 * N) => z.1) gH.val := hKmap'
      _ = Sym2.map (fun z : RectangleDualVertex (annulusHostAnchor N)
            (4 * N) (4 * N) => z.1)
            (rectangleSubgraphDualEdgeEquiv hSource bHost).val := by rw [hGHEdge]
      _ = (dualBondOfPrimal (annulusSourceHostPrimalBond N b)).toSym2 := by
        have hbondHost : annulusSourceHostPrimalBond N b =
            rectanglePrimalEdgeBond (annulusHostAnchor N) (4 * N) (4 * N)
              (subgraphEdgeEmbedding hSource bHost) := by
          unfold annulusSourceHostPrimalBond
          congr 1
        rw [hbondHost]
        exact hpairMap
  have hdouble := rectangleSubgraphDualEdgeEquiv_crossingBond hK gK
  rw [show annulusCandidateDoubleDualEdgeEquiv N b = gD from rfl]
  change Sym2.map (fun z : RectangleDualVertex
      (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1) => z.1)
      gD.val = _
  have hdouble' : Sym2.map (fun z : RectangleDualVertex
      (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1) => z.1) gD.val =
      (dualBondOfPrimal (annulusCandidatePrimalBond N gK)).toSym2 := by
    change Sym2.map (fun z : RectangleDualVertex
        (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1) => z.1) gD.val =
      (dualBondOfPrimal (rectanglePrimalEdgeBond
        (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1)
        (subgraphEdgeEmbedding hK gK))).toSym2
    exact hdouble
  rw [hdouble']
  have hbond := LatticeBond.toSym2_injective hKpair
  rw [congrArg (fun c : LatticeBond => (dualBondOfPrimal c).toSym2) hbond]

theorem p5aAnnulusCandidate_doubleDual_edge_pair (N : ℕ)
    (b : (annulusSourceGraph N).edgeSet) :
    let d := annulusCandidateDoubleDualEdgeEquiv N b
    Sym2.map (fun z : RectangleDualVertex (annulusDualExpandedHostAnchor N)
        (4 * N + 1) (4 * N + 1) => (z.1.1 + 1, z.1.2 + 1)) d.val =
      (annulusSourceHostPrimalBond N b).toSym2 := by
  classical
  change Sym2.map (fun z : RectangleDualVertex (annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1) => (z.1.1 + 1, z.1.2 + 1))
      (annulusCandidateDoubleDualEdgeEquiv N b).val = _
  have hp := annulusCandidateDoubleDualEdge_pair N b
  change Sym2.map (fun z : RectangleDualVertex (annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1) => z.1)
      (annulusCandidateDoubleDualEdgeEquiv N b).val = _ at hp
  have hp' := congrArg (Sym2.map (fun z : LatticeVertex =>
      (z.1 + 1, z.2 + 1))) hp
  change Sym2.map (fun z : RectangleDualVertex
      (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1) =>
        (z.1.1 + 1, z.1.2 + 1))
      (annulusCandidateDoubleDualEdgeEquiv N b).val = _ at hp'
  have hshift : Sym2.map (fun z : LatticeVertex => (z.1 + 1, z.2 + 1))
      (dualBondOfPrimal (dualBondOfPrimal
        (annulusSourceHostPrimalBond N b))).toSym2 =
      (annulusSourceHostPrimalBond N b).toSym2 := by
    let c := annulusSourceHostPrimalBond N b
    have hsource :
        ((dualBondOfPrimal (dualBondOfPrimal c)).source.1 + 1,
          (dualBondOfPrimal (dualBondOfPrimal c)).source.2 + 1) = c.source :=
      doubleDualBond_source_shift c
    have htarget :
        ((dualBondOfPrimal (dualBondOfPrimal c)).target.1 + 1,
          (dualBondOfPrimal (dualBondOfPrimal c)).target.2 + 1) = c.target :=
      doubleDualBond_target_shift c
    rw [LatticeBond.toSym2, LatticeBond.toSym2, Sym2.map_mk]
    rw [hsource, htarget]
  exact (hp'.trans hshift)

theorem p5aAnnulusCandidate_doubleDual_edge_pair_source (N : ℕ)
    (b : (annulusSourceGraph N).edgeSet) :
    Sym2.map (fun z : RectangleDualVertex (annulusDualExpandedHostAnchor N)
        (4 * N + 1) (4 * N + 1) => (z.1.1 + 1, z.1.2 + 1))
        (annulusCandidateDoubleDualEdgeEquiv N b).val =
      Sym2.map (fun z : {v : LatticeVertex // v ∈ annulusVertexSet N} => z.1)
        b.val := by
  rw [p5aAnnulusCandidate_doubleDual_edge_pair]
  rw [annulusSourceHostPrimalBond_toSym2]
  rw [subgraphEdgeEmbedding_coe, isolatedExtensionEdgeEquiv_coe]
  change Sym2.map (fun z : RectangleVertex (annulusHostAnchor N)
      (4 * N) (4 * N) => z.1)
      ((annulusSourceEmbedding N).sym2Map b.val) = _
  rw [Function.Embedding.sym2Map_apply, Sym2.map_map]
  rfl

end

end PottsContinuity.Thm3.Easy
