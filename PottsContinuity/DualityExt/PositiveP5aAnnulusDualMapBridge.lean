module

public import PottsContinuity.DualityExt.PositiveP5aAnnulusMergeActualDual
public import PottsContinuity.DualityExt.PositiveP5aAnnulusNoOpenCrossing
public import PottsContinuity.DualityExt.PositiveP5aAnnulusActualDualLaw
public import PottsContinuity.DualityExt.AnnulusFullBoxCrossingTransfer

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open MeasureTheory

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance p5aDualMapBridgeSourceConfigFintype (N : ℕ) :
    Fintype (Configuration (annulusSourceGraph N)) := Fintype.ofFinite _

local instance p5aDualMapBridgeCandidateConfigFintype
    {a : LatticeVertex} {w h : ℕ}
    {K : SimpleGraph (RectangleVertex a w h)} :
    Fintype (Configuration K) := Fintype.ofFinite _

local instance p5aDualMapBridgeActualConfigFintype (N : ℕ) :
    Fintype (Configuration
      (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))) :=
  Fintype.ofFinite _

/-- The exact event interfaces for the P5a annulus merge consumer follow from
identifying its composite configuration map with the direct subgraph-dual map.
The set on the candidate carrier is defined as the image of the two-block
disconnection event, so its pullback identity is exact. -/
theorem p5aAnnulusMergeActualDual_eventInterfaces_of_configurationMapEq
    (N : ℕ) (hN : 2 ≤ N)
    {a : LatticeVertex} {w h : ℕ}
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
    (hmap :
      (annulusPrimalToEmbeddedDualConfigurationEquiv N hK e hgraph).trans
          (annulusCandidateToActualDualConfigurationEquiv N f hIso) =
        (isolatedExtensionConfigurationEquiv (annulusSourceGraph N)
          (annulusSourceEmbedding N)).trans
          (rectangleSubgraphDualConfigurationEquiv
            (annulusSourceGraph_map_le_host N)))
    (u v : {x : LatticeVertex // x ∈ annulusVertexSet N})
    (hu : u ∈ annulusPrimalInnerBoundaryClass N (by omega))
    (hv : v ∈ annulusPrimalOuterBoundaryClass N (by omega)) :
    let d := annulusPrimalToEmbeddedDualConfigurationEquiv N hK e hgraph
    let E := positiveBoundaryDisconnectedEvent
      (G := annulusSourceGraph N)
      (positiveTwoBlockBoundary
        (annulusPrimalInnerBoundaryClass N (by omega))
        (annulusPrimalOuterBoundaryClass N (by omega))
        (annulusPrimalInnerOuter_disjoint N (by omega))) u v
    let S := d '' E
    let T := (annulusCandidateToActualDualConfigurationEquiv N f hIso) ⁻¹'
      p5aAnnulusSourceActualDualJordanEvent N (by omega)
    T ⊆ S ∧ E = d ⁻¹' S := by
  dsimp only
  let d := annulusPrimalToEmbeddedDualConfigurationEquiv N hK e hgraph
  let c := annulusCandidateToActualDualConfigurationEquiv N f hIso
  let direct := (isolatedExtensionConfigurationEquiv (annulusSourceGraph N)
      (annulusSourceEmbedding N)).trans
      (rectangleSubgraphDualConfigurationEquiv
        (annulusSourceGraph_map_le_host N))
  let E := positiveBoundaryDisconnectedEvent
    (G := annulusSourceGraph N)
    (positiveTwoBlockBoundary
      (annulusPrimalInnerBoundaryClass N (by omega))
      (annulusPrimalOuterBoundaryClass N (by omega))
      (annulusPrimalInnerOuter_disjoint N (by omega))) u v
  constructor
  · intro A hA
    have hA' : c A ∈ p5aAnnulusSourceActualDualJordanEvent N (by omega) := hA
    let C := d.symm A
    have hdc : d C = A := Equiv.apply_symm_apply d A
    have hcomp : c (d C) = direct C := by
      have h := congrArg (fun g => g C) hmap
      simpa only [d, c, direct, Equiv.trans_apply] using h
    have hdual : direct C ∈ p5aAnnulusSourceActualDualJordanEvent N (by omega) := by
      rw [← hcomp, hdc]
      exact hA'
    have hactual :
        rectangleSubgraphDualConfigurationEquiv
            (annulusSourceGraph_map_le_host N)
          (isolatedExtensionConfigurationEquiv (annulusSourceGraph N)
            (annulusSourceEmbedding N) C) ∈
          p5aAnnulusSourceActualDualJordanEvent N (by omega) := by
      simpa only [direct, Equiv.trans_apply] using hdual
    have hdisconnected := p5aAnnulusSourceActualDualJordan_twoBlockDisconnected
      N hN C u v hu hv hactual
    exact ⟨C, hdisconnected, hdc⟩
  · change E = d ⁻¹' (d '' E)
    ext C
    constructor
    · intro hC
      exact ⟨C, hC, rfl⟩
    · rintro ⟨C', hC', hEq⟩
      have hCC' : C' = C := d.injective hEq
      simpa [hCC'] using hC'

/-- The candidate Jordan event pulls back to the source annulus Jordan event
when the double-dual map agrees with the direct rectangle map. -/
theorem p5aAnnulusMergeActualDual_sourceEvent_eq_of_configurationMapEq
    (N : ℕ) (hN : 2 ≤ N)
    {a : LatticeVertex} {w h : ℕ}
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
    (hmap :
      (annulusPrimalToEmbeddedDualConfigurationEquiv N hK e hgraph).trans
          (annulusCandidateToActualDualConfigurationEquiv N f hIso) =
        (isolatedExtensionConfigurationEquiv (annulusSourceGraph N)
          (annulusSourceEmbedding N)).trans
          (rectangleSubgraphDualConfigurationEquiv
            (annulusSourceGraph_map_le_host N)))
    (T : Set (Configuration K))
    (hT : T = (annulusCandidateToActualDualConfigurationEquiv N f hIso) ⁻¹'
      p5aAnnulusSourceActualDualJordanEvent N hN) :
    (annulusPrimalToEmbeddedDualConfigurationEquiv N hK e hgraph) ⁻¹' T =
      p5aAnnulusPrimalDualJordanEvent N hN := by
  let d := annulusPrimalToEmbeddedDualConfigurationEquiv N hK e hgraph
  let c := annulusCandidateToActualDualConfigurationEquiv N f hIso
  let direct := (isolatedExtensionConfigurationEquiv (annulusSourceGraph N)
      (annulusSourceEmbedding N)).trans
      (rectangleSubgraphDualConfigurationEquiv
        (annulusSourceGraph_map_le_host N))
  have hpoint (C : Configuration (annulusSourceGraph N)) :
      c (d C) = direct C := by
    have h := congrArg (fun g => g C) hmap
    simpa only [d, c, direct, Equiv.trans_apply] using h
  ext C
  change d C ∈ T ↔ C ∈ p5aAnnulusPrimalDualJordanEvent N hN
  rw [hT]
  simp only [Set.mem_preimage]
  rw [hpoint C]
  simp [p5aAnnulusPrimalDualJordanEvent, p5aAnnulusActiveDualJordanEvent,
    annulusPrimalToActiveDualConfigurationEquiv, direct]

/-- The P5a Jordan event itself transfers to joint wiring, and therefore
retains its full-box non-crossing consequence. -/
theorem annulus_jointWired_p5aJordan_measure_ge_div_of_actualDualMapEq
    (N : ℕ) (hN : 1 ≤ N) (hN4 : 4 ≤ N)
    {a : LatticeVertex} {w h : ℕ}
    {K : SimpleGraph (RectangleVertex a w h)}
    (hK : K ≤ rectangleGraph a w h)
    (e : positiveActiveVertexSet (rectangleSubgraphDualGraph hK) ≃
      {v : LatticeVertex // v ∈ annulusVertexSet N})
    (hgraph : (positiveActiveGraph (rectangleSubgraphDualGraph hK)).map
        e.toEmbedding = annulusSourceGraph N)
    (hpartition : (positiveWiredSubgraphDualBoundary hK e).partition =
      (annulusPrimalSeparatedBoundary N hN).partition)
    (q : Set.Ici (1 : ℝ)) (c : ℝ)
    (u v : {x : LatticeVertex // x ∈ annulusVertexSet N})
    (hu : u ∈ annulusPrimalInnerBoundaryClass N hN)
    (hv : v ∈ annulusPrimalOuterBoundaryClass N hN)
    (f : RectangleVertex a w h ≃
      RectangleDualVertex (annulusHostAnchor N) (4 * N) (4 * N))
    (hIso : K.map f.toEmbedding =
      rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))
    (hmap :
      (annulusPrimalToEmbeddedDualConfigurationEquiv N hK e hgraph).trans
          (annulusCandidateToActualDualConfigurationEquiv N f hIso) =
        (isolatedExtensionConfigurationEquiv (annulusSourceGraph N)
          (annulusSourceEmbedding N)).trans
          (rectangleSubgraphDualConfigurationEquiv
            (annulusSourceGraph_map_le_host N)))
    (hP5a : c ≤ PottsContinuity.Thm3.Easy.p5aAnnulusProbability
      (criticalParameters q) (N - 1)) :
    c / (q : ℝ) ≤
      (measure (annulusSourceGraph N) (criticalParameters q)
        (BoundaryCondition.wired
          (annulusPrimalInnerBoundaryClass N hN ∪
            annulusPrimalOuterBoundaryClass N hN))
        (p5aAnnulusPrimalDualJordanEvent N (by omega))).toReal := by
  let d := annulusPrimalToEmbeddedDualConfigurationEquiv N hK e hgraph
  let T := (annulusCandidateToActualDualConfigurationEquiv N f hIso) ⁻¹'
    p5aAnnulusSourceActualDualJordanEvent N (by omega)
  let E := positiveBoundaryDisconnectedEvent
    (G := annulusSourceGraph N)
    (positiveTwoBlockBoundary
      (annulusPrimalInnerBoundaryClass N hN)
      (annulusPrimalOuterBoundaryClass N hN)
      (annulusPrimalInnerOuter_disjoint N hN)) u v
  let S := d '' E
  have hInt := p5aAnnulusMergeActualDual_eventInterfaces_of_configurationMapEq
    N (by omega) hK e hgraph f hIso hmap u v hu hv
  have hH : c ≤ (measure
      (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))
      (criticalParameters q) (BoundaryCondition.free ∅)
      (p5aAnnulusSourceActualDualJordanEvent N (by omega))).toReal := by
    exact p5a_annulus_probability_le_actualDual_inducedBoundary N (by omega)
      q c (BoundaryCondition.free ∅) le_rfl hP5a
  have hμ : (measure K (criticalParameters q) (BoundaryCondition.free ∅)).map
      (annulusCandidateToActualDualConfigurationEquiv N f hIso) =
      measure (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))
        (criticalParameters q) (BoundaryCondition.free ∅) := by
    change (law K (criticalParameters q) (BoundaryCondition.free ∅)).toMeasure.map
        (annulusCandidateToActualDualConfigurationEquiv N f hIso) =
      (law (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))
        (criticalParameters q) (BoundaryCondition.free ∅)).toMeasure
    calc
      _ = ((law K (criticalParameters q) (BoundaryCondition.free ∅)).map
          (annulusCandidateToActualDualConfigurationEquiv N f hIso)).toMeasure :=
        PMF.toMeasure_map _ _ measurable_from_top
      _ = _ := congrArg PMF.toMeasure
        (annulusCandidate_freeLaw_map_eq_actualDual_freeLaw N f hIso q)
  have hprob := congrArg
    (fun μ : Measure (Configuration
      (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))) =>
        μ (p5aAnnulusSourceActualDualJordanEvent N (by omega))) hμ
  rw [Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top] at hprob
  have hprob' : measure K (criticalParameters q) (BoundaryCondition.free ∅) T =
      measure (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))
        (criticalParameters q) (BoundaryCondition.free ∅)
        (p5aAnnulusSourceActualDualJordanEvent N (by omega)) := by
    change measure K (criticalParameters q) (BoundaryCondition.free ∅)
        ((annulusCandidateToActualDualConfigurationEquiv N f hIso) ⁻¹'
          p5aAnnulusSourceActualDualJordanEvent N (by omega)) = _
    exact hprob
  have hreal := congrArg ENNReal.toReal hprob'
  have hTbound : c ≤ (measure K (criticalParameters q)
      (BoundaryCondition.free ∅) T).toReal := hH.trans_eq hreal.symm
  have hmerged := annulus_jointWired_dualSubevent_measure_ge_div_of_doubleDualGeometry
    N hN hK e hgraph hpartition q c u v hu hv S T hInt.2 hInt.1 hTbound
  have hsource := p5aAnnulusMergeActualDual_sourceEvent_eq_of_configurationMapEq
    N (by omega) hK e hgraph f hIso hmap T rfl
  simpa only [d, T, hsource] using hmerged

/-- The joint-wired P5a Jordan event bound implies the same lower bound for
the complement of every full-box-to-outer-boundary open crossing. -/
theorem annulus_jointWired_p5a_noFullBoxCrossing_ge_div_of_actualDualMapEq
    (N : ℕ) (hN : 1 ≤ N) (hN4 : 4 ≤ N)
    {a : LatticeVertex} {w h : ℕ}
    {K : SimpleGraph (RectangleVertex a w h)}
    (hK : K ≤ rectangleGraph a w h)
    (e : positiveActiveVertexSet (rectangleSubgraphDualGraph hK) ≃
      {v : LatticeVertex // v ∈ annulusVertexSet N})
    (hgraph : (positiveActiveGraph (rectangleSubgraphDualGraph hK)).map
        e.toEmbedding = annulusSourceGraph N)
    (hpartition : (positiveWiredSubgraphDualBoundary hK e).partition =
      (annulusPrimalSeparatedBoundary N hN).partition)
    (q : Set.Ici (1 : ℝ)) (c : ℝ)
    (u v : {x : LatticeVertex // x ∈ annulusVertexSet N})
    (hu : u ∈ annulusPrimalInnerBoundaryClass N hN)
    (hv : v ∈ annulusPrimalOuterBoundaryClass N hN)
    (f : RectangleVertex a w h ≃
      RectangleDualVertex (annulusHostAnchor N) (4 * N) (4 * N))
    (hIso : K.map f.toEmbedding =
      rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))
    (hmap :
      (annulusPrimalToEmbeddedDualConfigurationEquiv N hK e hgraph).trans
          (annulusCandidateToActualDualConfigurationEquiv N f hIso) =
        (isolatedExtensionConfigurationEquiv (annulusSourceGraph N)
          (annulusSourceEmbedding N)).trans
          (rectangleSubgraphDualConfigurationEquiv
            (annulusSourceGraph_map_le_host N)))
    (hP5a : c ≤ PottsContinuity.Thm3.Easy.p5aAnnulusProbability
      (criticalParameters q) (N - 1)) :
    c / (q : ℝ) ≤
      (measure (annulusSourceGraph N) (criticalParameters q)
        (BoundaryCondition.wired
          (annulusPrimalInnerBoundaryClass N hN ∪
            annulusPrimalOuterBoundaryClass N hN))
        (annulusSourceFullBoxCrossingEvent N)ᶜ).toReal := by
  have hJordan := annulus_jointWired_p5aJordan_measure_ge_div_of_actualDualMapEq
    N hN hN4 hK e hgraph hpartition q c u v hu hv f hIso hmap hP5a
  have hsubset : p5aAnnulusPrimalDualJordanEvent N (by omega) ⊆
      (annulusSourceFullBoxCrossingEvent N)ᶜ := by
    intro C hC
    exact p5aAnnulusPrimalDualJordanEvent_subset_noFullBoxCrossing
      N hN4 C hC
  exact le_trans hJordan (ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono hsubset))

end

end PottsContinuity.DualityExt
