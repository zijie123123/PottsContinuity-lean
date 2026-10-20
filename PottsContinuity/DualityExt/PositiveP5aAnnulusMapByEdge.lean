module

public import PottsContinuity.DualityExt.PositiveWiredDualEdgeState
public import PottsContinuity.DualityExt.PositiveP5aAnnulusDualMapBridge
public import PottsContinuity.DualityExt.PositiveEmbeddedDualEdgeState

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK

noncomputable section

local instance p5aEdgeMapSourceConfigFintype (N : ℕ) :
    Fintype (Configuration (annulusSourceGraph N)) := Fintype.ofFinite _

local instance p5aEdgeMapCandidateConfigFintype
    {a : LatticeVertex} {w h : ℕ}
    {K : SimpleGraph (RectangleVertex a w h)} :
    Fintype (Configuration K) := Fintype.ofFinite _

local instance p5aEdgeMapActualConfigFintype (N : ℕ) :
    Fintype (Configuration
      (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))) :=
  Fintype.ofFinite _

/-- Edge labels on a candidate graph and the annulus host dual carrier. -/
noncomputable def p5aCandidateToActualDualEdgeEquiv
    (N : ℕ) {a : LatticeVertex} {w h : ℕ}
    {K : SimpleGraph (RectangleVertex a w h)}
    (f : RectangleVertex a w h ≃
      RectangleDualVertex (annulusHostAnchor N) (4 * N) (4 * N))
    (hIso : K.map f.toEmbedding =
      rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N)) :
    K.edgeSet ≃
      (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N)).edgeSet :=
  (isolatedExtensionEdgeEquiv K f.toEmbedding).trans
    (Set.equivOfEq (congrArg (fun G : SimpleGraph
      (RectangleDualVertex (annulusHostAnchor N) (4 * N) (4 * N)) => G.edgeSet)
      hIso))

/-- The edge labels from the active double dual carrier back to the source
annulus. -/
noncomputable def p5aActiveDoubleDualToSourceEdgeEquiv
    (N : ℕ) {a : LatticeVertex} {w h : ℕ}
    {K : SimpleGraph (RectangleVertex a w h)}
    (hK : K ≤ rectangleGraph a w h)
    (e : positiveActiveVertexSet (rectangleSubgraphDualGraph hK) ≃
      {v : LatticeVertex // v ∈ annulusVertexSet N})
    (hgraph : (positiveActiveGraph (rectangleSubgraphDualGraph hK)).map
        e.toEmbedding = annulusSourceGraph N) :
    (rectangleSubgraphDualGraph hK).edgeSet ≃
      (annulusSourceGraph N).edgeSet :=
  (((positiveActiveEdgeToGraphEquiv (rectangleSubgraphDualGraph hK)).symm).trans
      (isolatedExtensionEdgeEquiv
        (positiveActiveGraph (rectangleSubgraphDualGraph hK)) e.toEmbedding)).trans
    (Set.equivOfEq (congrArg (fun G : SimpleGraph
      {v : LatticeVertex // v ∈ annulusVertexSet N} => G.edgeSet) hgraph))

/-- The direct source-annulus to rectangle-dual edge-label equivalence. -/
noncomputable def p5aSourceToActualDualEdgeEquiv (N : ℕ) :
    (annulusSourceGraph N).edgeSet ≃
      (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N)).edgeSet :=
  (isolatedExtensionEdgeEquiv (annulusSourceGraph N)
      (annulusSourceEmbedding N)).trans
    (rectangleSubgraphDualEdgeEquiv (annulusSourceGraph_map_le_host N))

/-- The candidate and direct maps agree once their pure edge labels agree. -/
theorem p5aAnnulusCompositeDualMap_eq_of_edgeLabelAgreement
    (N : ℕ) {a : LatticeVertex} {w h : ℕ}
    {K : SimpleGraph (RectangleVertex a w h)}
    (hK : K ≤ rectangleGraph a w h)
    (e : positiveActiveVertexSet (rectangleSubgraphDualGraph hK) ≃
      {v : LatticeVertex // v ∈ annulusVertexSet N})
    (hgraph : (positiveActiveGraph (rectangleSubgraphDualGraph hK)).map
        e.toEmbedding = annulusSourceGraph N)
    (f : RectangleVertex a w h ≃
      RectangleDualVertex (annulusHostAnchor N) (4 * N) (4 * N))
    (hIso : K.map f.toEmbedding =
      rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))
    (hlabels : ∀ d : (rectangleSubgraphDualGraph
        (annulusSourceGraph_map_le_host N)).edgeSet,
      p5aActiveDoubleDualToSourceEdgeEquiv N hK e hgraph
          (rectangleSubgraphDualEdgeEmbedding hK
            ((p5aCandidateToActualDualEdgeEquiv N f hIso).symm d)) =
        (p5aSourceToActualDualEdgeEquiv N).symm d) :
    (annulusPrimalToEmbeddedDualConfigurationEquiv N hK e hgraph).trans
        (annulusCandidateToActualDualConfigurationEquiv N f hIso) =
      (isolatedExtensionConfigurationEquiv (annulusSourceGraph N)
        (annulusSourceEmbedding N)).trans
        (rectangleSubgraphDualConfigurationEquiv
          (annulusSourceGraph_map_le_host N)) := by
  apply Equiv.ext
  intro C
  ext d
  let source := annulusSourceGraph N
  let actual := rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N)
  let active := positiveActiveGraph (rectangleSubgraphDualGraph hK)
  let activeMapped := active.map e.toEmbedding
  let sourceToActual := p5aSourceToActualDualEdgeEquiv N
  let candidateToActual := p5aCandidateToActualDualEdgeEquiv N f hIso
  let k := candidateToActual.symm d
  let Cactive := Equiv.cast (congrArg Configuration hgraph.symm) C
  let gCandidate := (positiveActiveEdgeToGraphEquiv
      (rectangleSubgraphDualGraph hK)).symm
        (rectangleSubgraphDualEdgeEmbedding hK k)
  let gmCandidate := isolatedExtensionEdgeEquiv active e.toEmbedding gCandidate
  have hCandidateApply (A : Configuration K) :
      annulusCandidateToActualDualConfigurationEquiv N f hIso A =
        A.map candidateToActual.toEmbedding := by
    have hEdge : (K.map f.toEmbedding).edgeSet = actual.edgeSet :=
      congrArg (fun G : SimpleGraph
        (RectangleDualVertex (annulusHostAnchor N) (4 * N) (4 * N)) => G.edgeSet)
        hIso
    change Equiv.cast
        (congrArg (fun s : Set (Sym2
          (RectangleDualVertex (annulusHostAnchor N) (4 * N) (4 * N))) =>
            Finset s) hEdge)
        (A.map (isolatedExtensionEdgeEquiv K f.toEmbedding).toEmbedding) = _
    rw [configurationCast_setEq_eq_edgeMap (K.map f.toEmbedding).edgeSet
      actual.edgeSet hEdge]
    rw [Finset.map_map]
    congr 1
  have hActiveCast : gmCandidate ∈ Cactive ↔
      (p5aActiveDoubleDualToSourceEdgeEquiv N hK e hgraph
        (rectangleSubgraphDualEdgeEmbedding hK k)) ∈ C := by
    have hEdge : activeMapped.edgeSet = source.edgeSet :=
      congrArg (fun G : SimpleGraph
        {v : LatticeVertex // v ∈ annulusVertexSet N} => G.edgeSet) hgraph
    change gmCandidate ∈ Equiv.cast
        (congrArg (fun G : SimpleGraph
          {v : LatticeVertex // v ∈ annulusVertexSet N} => Configuration G)
          hgraph.symm) C ↔ _
    rw [configurationCast_setEq_eq_edgeMap source.edgeSet activeMapped.edgeSet hEdge.symm]
    rw [Finset.mem_map_equiv]
    rfl
  have hLeft : d ∈
      (annulusPrimalToEmbeddedDualConfigurationEquiv N hK e hgraph).trans
        (annulusCandidateToActualDualConfigurationEquiv N f hIso) C ↔
      (p5aActiveDoubleDualToSourceEdgeEquiv N hK e hgraph
        (rectangleSubgraphDualEdgeEmbedding hK k)) ∉ C := by
    change d ∈ annulusCandidateToActualDualConfigurationEquiv N f hIso
        (annulusPrimalToEmbeddedDualConfigurationEquiv N hK e hgraph C) ↔ _
    rw [hCandidateApply]
    rw [Finset.mem_map_equiv]
    change k ∈ positiveWiredSubgraphDualConfigurationEquiv hK e Cactive ↔ _
    rw [positiveWiredSubgraphDualConfigurationEquiv_edgeState]
    exact not_congr hActiveCast
  have hRight : d ∈
      ((isolatedExtensionConfigurationEquiv source
        (annulusSourceEmbedding N)).trans
          (rectangleSubgraphDualConfigurationEquiv
            (annulusSourceGraph_map_le_host N))) C ↔
      sourceToActual.symm d ∉ C := by
    let gh := (rectangleSubgraphDualEdgeEquiv
      (annulusSourceGraph_map_le_host N)).symm d
    let g := (isolatedExtensionEdgeEquiv source
      (annulusSourceEmbedding N)).symm gh
    have hg : g = sourceToActual.symm d := by
      rfl
    have hdualEdge : rectangleSubgraphDualEdgeEmbedding
        (annulusSourceGraph_map_le_host N) gh = d := by
      change rectangleSubgraphDualEdgeEquiv
        (annulusSourceGraph_map_le_host N) gh = d
      exact Equiv.apply_symm_apply
        (rectangleSubgraphDualEdgeEquiv
          (annulusSourceGraph_map_le_host N)) d
    have hextEdge : isolatedExtensionEdgeEquiv source
        (annulusSourceEmbedding N) g = gh :=
      Equiv.apply_symm_apply
        (isolatedExtensionEdgeEquiv source
          (annulusSourceEmbedding N)) gh
    rw [← hg]
    change d ∈ rectangleSubgraphDualConfigurationEquiv
        (annulusSourceGraph_map_le_host N)
        (isolatedExtensionConfigurationEquiv source
          (annulusSourceEmbedding N) C) ↔ g ∉ C
    rw [← hdualEdge]
    rw [← hextEdge]
    exact embeddedRectangleSubgraphDualConfiguration_edgeState
      (V := {v : LatticeVertex // v ∈ annulusVertexSet N})
      (W := RectangleVertex (annulusHostAnchor N) (4 * N) (4 * N))
      (G := annulusSourceGraph N)
      (a := annulusHostAnchor N) (w := 4 * N) (h := 4 * N)
      (f := annulusSourceEmbedding N)
      (hG := annulusSourceGraph_map_le_host N) C g
  have hlabel' :
      p5aActiveDoubleDualToSourceEdgeEquiv N hK e hgraph
          (rectangleSubgraphDualEdgeEmbedding hK k) = sourceToActual.symm d := by
    simpa only [k, candidateToActual, sourceToActual] using hlabels d
  rw [hlabel'] at hLeft
  exact hLeft.trans hRight.symm

end

end PottsContinuity.DualityExt
