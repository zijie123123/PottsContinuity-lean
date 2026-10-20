module

public import PottsContinuity.DualityExt.PositiveP5aAnnulusActualDual
public import PottsContinuity.DualityExt.PositiveP5aSourceAnnulusTransfer

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial
open MeasureTheory

noncomputable section

local instance p5aActualJordanSourceConfigFintype (N : ℕ) :
    Fintype (Configuration (p5aAnnulusSourceFaceGraph N)) := Fintype.ofFinite _

local instance p5aActualJordanTargetConfigFintype (N : ℕ) :
    Fintype (Configuration
      (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))) :=
  Fintype.ofFinite _

/-- The P5a source face carrier embedded into the edge-deleted annulus dual
carrier. -/
def p5aAnnulusSourceFaceBaseEmbeddingActual (N : ℕ) (hN : 2 ≤ N) :
    {v : LatticeVertex // v ∈
      PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1)} ↪
      RectangleDualVertex (annulusHostAnchor N) (4 * N) (4 * N) where
  toFun v := by
    have hv : v.1 ∈ p5aAnnulusVertexSet (N - 1) := by
      rw [← p5aAnnulusVertexSet_eq_source (N - 1)]
      exact v.2
    exact p5aAnnulusFaceBaseEmbeddingActual N hN ⟨v.1, hv⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : RectangleDualVertex
      (annulusHostAnchor N) (4 * N) (4 * N) => z.1) hxy

/-- The P5a source graph embeds into the exact dual graph after the primal
annulus bonds have been removed. -/
theorem p5a_annulus_sourceFaceGraph_map_le_actualDual
    (N : ℕ) (hN : 2 ≤ N) :
    (p5aAnnulusSourceFaceGraph N).map
        (p5aAnnulusSourceFaceBaseEmbeddingActual N hN) ≤
      rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N) := by
  intro u v huv
  rw [SimpleGraph.map_adj] at huv
  rcases huv with ⟨x, y, hxy, hxu, hyv⟩
  let x' : {z : LatticeVertex // z ∈ p5aAnnulusVertexSet (N - 1)} :=
    ⟨x.1, by
      rw [← p5aAnnulusVertexSet_eq_source (N - 1)]
      exact x.2⟩
  let y' : {z : LatticeVertex // z ∈ p5aAnnulusVertexSet (N - 1)} :=
    ⟨y.1, by
      rw [← p5aAnnulusVertexSet_eq_source (N - 1)]
      exact y.2⟩
  have hxy' : (p5aAnnulusFaceGraph N).Adj x' y' := by
    change squareLattice.Adj x.1 y.1
    exact hxy
  have hmap : ((p5aAnnulusFaceGraph N).map
      (p5aAnnulusFaceBaseEmbeddingActual N hN)).Adj
        (p5aAnnulusFaceBaseEmbeddingActual N hN x')
        (p5aAnnulusFaceBaseEmbeddingActual N hN y') := by
    rw [SimpleGraph.map_adj]
    exact ⟨x', y', hxy', rfl, rfl⟩
  have hactual := p5aAnnulusFaceGraphActual_map_le_annulusSourceDualGraph N hN hmap
  have hfx : p5aAnnulusSourceFaceBaseEmbeddingActual N hN x =
      p5aAnnulusFaceBaseEmbeddingActual N hN x' := by
    apply Subtype.ext
    rfl
  have hfy : p5aAnnulusSourceFaceBaseEmbeddingActual N hN y =
      p5aAnnulusFaceBaseEmbeddingActual N hN y' := by
    apply Subtype.ext
    rfl
  rw [← hxu, ← hyv, hfx, hfy]
  exact hactual

/-- The source P5a polygon circuit interpreted in the exact edge-deleted
dual graph. -/
def p5aAnnulusSourceActualDualJordanEvent (N : ℕ) (hN : 2 ≤ N) :
    Set (Configuration
      (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))) :=
  {A | ∃ m : ℕ, ∃ P : PottsContinuity.FKC.LatticePolygon m,
    PottsContinuity.FKC.latticeEmbed ⟨1, by norm_num⟩ (0, 0) ∈
      P.domain ⟨1, by norm_num⟩ ∧
    (∀ i : ZMod (m + 3), P.vertex i ∈ dualFaceAnnulusShell N) ∧
    ∀ i : ZMod (m + 3),
      ∃ hi : P.vertex i ∈
        PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1),
      ∃ hj : P.vertex (i + 1) ∈
        PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1),
        (openGraph
          (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N)) A).Adj
          (p5aAnnulusSourceFaceBaseEmbeddingActual N hN ⟨P.vertex i, hi⟩)
          (p5aAnnulusSourceFaceBaseEmbeddingActual N hN ⟨P.vertex (i + 1), hj⟩)}

/-- Restricting an edge-deleted dual configuration to the P5a face graph
preserves the source polygon circuit. -/
theorem p5a_annulus_sourceJordan_restriction_subset_actualDual
    (N : ℕ) (hN : 2 ≤ N)
    (A : Configuration
      (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))) :
    embeddedConfigurationRestriction (p5aAnnulusSourceFaceGraph N)
        (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))
        (p5aAnnulusSourceFaceBaseEmbeddingActual N hN)
        (p5a_annulus_sourceFaceGraph_map_le_actualDual N hN) A ∈
      p5aAnnulusSourceJordanCircuitEvent N →
    A ∈ p5aAnnulusSourceActualDualJordanEvent N hN := by
  intro hA
  let G := p5aAnnulusSourceFaceGraph N
  let H := rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N)
  let f := p5aAnnulusSourceFaceBaseEmbeddingActual N hN
  let hGH := p5a_annulus_sourceFaceGraph_map_le_actualDual N hN
  let C := embeddedConfigurationRestriction G H f hGH A
  change (PottsContinuity.PD.FK.boolConfigurationEquiv G).symm C ∈
    PottsContinuity.RSW.annulusCircuitEvent
      (PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1))
      (0, 0) (N - 1) at hA
  rcases hA with ⟨m, P, hcenter, hradial, hopen⟩
  have hsource : openGraph G C =
      PottsContinuity.PD.rcOpenGraph
        (PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1))
        ((PottsContinuity.PD.FK.boolConfigurationEquiv G).symm C) := by
    have hcfg : PottsContinuity.PD.FK.boolConfigurationEquiv G
        ((PottsContinuity.PD.FK.boolConfigurationEquiv G).symm C) = C :=
      Equiv.apply_symm_apply _ _
    calc
      openGraph G C = openGraph G
          (PottsContinuity.PD.FK.boolConfigurationEquiv G
            ((PottsContinuity.PD.FK.boolConfigurationEquiv G).symm C)) := by
              rw [hcfg]
      _ = PottsContinuity.PD.rcOpenGraph
          (PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1))
          ((PottsContinuity.PD.FK.boolConfigurationEquiv G).symm C) :=
            PottsContinuity.PD.FK.rcOpenGraph_eq
              (PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1))
              ((PottsContinuity.PD.FK.boolConfigurationEquiv G).symm C)
  let k : openGraph G C →g openGraph H A := by
    refine ⟨f, ?_⟩
    intro u v huv
    rw [openGraph_adj]
    rcases (openGraph_adj _ _ _ _).mp huv with ⟨e, he, hev⟩
    refine ⟨embeddedEdgeEmbedding G H f hGH e,
      (mem_embeddedConfigurationRestriction G H f hGH A e).mp he, ?_⟩
    rw [embeddedEdgeEmbedding_coe, hev]
    rfl
  refine ⟨m, P, hcenter, ?_, ?_⟩
  · intro i
    rcases hopen i with ⟨hi, hj, _⟩
    have hi' : P.vertex i ∈ p5aAnnulusVertexSet (N - 1) := by
      rw [← p5aAnnulusVertexSet_eq_source (N - 1)]
      exact hi
    exact p5a_annulus_faceShell_fit N hN hi'
  · intro i
    rcases hopen i with ⟨hi, hj, hij⟩
    refine ⟨hi, hj, ?_⟩
    apply k.map_adj
    rw [hsource]
    exact hij

/-- The source P5a probability is bounded by the same polygon event on the
exact edge-deleted annulus dual graph, for every target partition above free. -/
theorem p5a_annulus_sourceJordan_measure_le_actualDual_at_selfDualParameter_of_target_partition
    (N : ℕ) (hN : 2 ≤ N) (q : Set.Ici (1 : ℝ))
    (η : BoundaryCondition
      (RectangleDualVertex (annulusHostAnchor N) (4 * N) (4 * N)))
    (hη : (BoundaryCondition.free ∅).partition ≤ η.partition) :
    (measure (p5aAnnulusSourceFaceGraph N) (criticalParameters q)
      (BoundaryCondition.free ∅) (p5aAnnulusSourceJordanCircuitEvent N)).toReal ≤
    (measure (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))
      (criticalParameters q) η (p5aAnnulusSourceActualDualJordanEvent N hN)).toReal := by
  have hcmp := free_embedded_event_measure_le_at_selfDualParameter_of_target_partition
    (p5aAnnulusSourceFaceBaseEmbeddingActual N hN)
    (p5a_annulus_sourceFaceGraph_map_le_actualDual N hN) q η hη
    (p5aAnnulusSourceJordanCircuitEvent N)
    (p5aAnnulusSourceJordanCircuitEvent_upper N)
  have hsubset :
      {A | embeddedConfigurationRestriction (p5aAnnulusSourceFaceGraph N)
        (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))
        (p5aAnnulusSourceFaceBaseEmbeddingActual N hN)
        (p5a_annulus_sourceFaceGraph_map_le_actualDual N hN) A ∈
          p5aAnnulusSourceJordanCircuitEvent N} ⊆
        p5aAnnulusSourceActualDualJordanEvent N hN := by
    intro A hA
    exact p5a_annulus_sourceJordan_restriction_subset_actualDual N hN A hA
  exact le_trans hcmp (ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono hsubset))

/-- The P5a lower bound transfers to the induced dual boundary partition on
the exact edge-deleted annulus graph. -/
theorem p5a_annulus_probability_le_actualDual_inducedBoundary
    (N : ℕ) (hN : 2 ≤ N) (q : Set.Ici (1 : ℝ)) (c : ℝ)
    (η : BoundaryCondition
      (RectangleDualVertex (annulusHostAnchor N) (4 * N) (4 * N)))
    (hη : (BoundaryCondition.free ∅).partition ≤ η.partition)
    (hP5a : c ≤ PottsContinuity.Thm3.Easy.p5aAnnulusProbability
      (criticalParameters q) (N - 1)) :
    c ≤ (measure (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))
      (criticalParameters q) η (p5aAnnulusSourceActualDualJordanEvent N hN)).toReal := by
  have hsource : c ≤
      (measure (p5aAnnulusSourceFaceGraph N) (criticalParameters q)
        (BoundaryCondition.free ∅) (p5aAnnulusSourceJordanCircuitEvent N)).toReal := by
    rw [← p5aAnnulusProbability_eq_sourceFaceMeasure N q]
    exact hP5a
  exact le_trans hsource
    (p5a_annulus_sourceJordan_measure_le_actualDual_at_selfDualParameter_of_target_partition
      N hN q η hη)

end
end PottsContinuity.DualityExt
