module

public import PottsContinuity.DualityExt.PositiveP5aAnnulusDualMapBridge
public import PottsContinuity.PD.Defs.VertexBoundary

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial
open MeasureTheory

noncomputable section

local instance annulusBoundaryIdentificationConfigFintype (N : ℕ) :
    Fintype (Configuration (annulusSourceGraph N)) := Fintype.ofFinite _

private theorem annulusHostRectangle_eq_box (N : ℕ) :
    PottsContinuity.PD.FK.latticeRectangle
      (annulusHostAnchor N) (4 * N) (4 * N) =
      latticeBox (0, 0) (2 * N) := by
  ext z
  rw [mem_latticeRectangle, mem_latticeBox]
  simp only [annulusHostAnchor]
  omega

/-- The full vertex boundary of the annulus consists of the two wired sides
used in the separately wired annulus construction. -/
theorem annulusPrimalBoundaryClasses_union_eq_vertexBoundary
    (N : ℕ) (hN : 1 ≤ N) :
    annulusPrimalInnerBoundaryClass N hN ∪ annulusPrimalOuterBoundaryClass N hN =
      {x | x.1 ∈ PottsContinuity.PD.vertexBoundary
        (annulusVertexSet N)} := by
  ext x
  constructor
  · intro hx
    have hxV := x.2
    rcases hx with hI | hO
    · have hI' : annulusSourceEmbedding N x ∈
          annulusHostPrimalInnerClass N := hI
      change x.1 ∈ latticeBox (0, 0) (N - 1) ∨
        ∃ y, y ∈ latticeBox (0, 0) (N - 1) ∧
          squareLattice.Adj y x.1 at hI'
      rcases hI' with hhole | ⟨y, hy, hyx⟩
      · have hnot : x.1 ∉ latticeBox (0, 0) (N - 1) := by
          intro h
          exact (Finset.mem_sdiff.mp hxV).2 h
        exact False.elim (hnot hhole)
      · refine ⟨hxV, y, ?_, ?_⟩
        · exact hyx.symm
        · intro hyAnn
          exact (Finset.mem_sdiff.mp hyAnn).2 hy
    · have hO' : annulusSourceEmbedding N x ∈
          annulusHostPrimalOuterClass N := hO
      change (annulusSourceEmbedding N x).1 ∈
        PottsContinuity.PD.vertexBoundary
          (PottsContinuity.PD.FK.latticeRectangle
            (annulusHostAnchor N) (4 * N) (4 * N)) at hO'
      change x.1 ∈ PottsContinuity.PD.vertexBoundary
        (PottsContinuity.PD.FK.latticeRectangle
          (annulusHostAnchor N) (4 * N) (4 * N)) at hO'
      have hb : x.1 ∈ PottsContinuity.PD.vertexBoundary
          (latticeBox (0, 0) (2 * N)) := by
        simpa only [annulusHostRectangle_eq_box] using hO'
      rcases hb with ⟨_, y, hxy, hy⟩
      refine ⟨hxV, y, hxy, ?_⟩
      intro hyAnn
      exact hy (Finset.mem_sdiff.mp hyAnn).1
  · rintro ⟨_, y, hxy, hy⟩
    have hxV := x.2
    have hyOutOrHole : y ∉ latticeBox (0, 0) (2 * N) ∨
        y ∈ latticeBox (0, 0) (N - 1) := by
      by_cases h2 : y ∈ latticeBox (0, 0) (2 * N)
      · right
        by_contra hinner
        apply hy
        exact Finset.mem_sdiff.mpr ⟨h2, hinner⟩
      · exact Or.inl h2
    rcases hyOutOrHole with hyOut | hyHole
    · have hb : x.1 ∈ PottsContinuity.PD.vertexBoundary
          (latticeBox (0, 0) (2 * N)) :=
        ⟨(Finset.mem_sdiff.mp hxV).1, y, hxy, hyOut⟩
      have hO' : annulusSourceEmbedding N x ∈
          annulusHostPrimalOuterClass N := by
        change x.1 ∈ PottsContinuity.PD.vertexBoundary
          (PottsContinuity.PD.FK.latticeRectangle
            (annulusHostAnchor N) (4 * N) (4 * N))
        simpa only [annulusHostRectangle_eq_box] using hb
      exact Or.inr hO'
    · have hI' : annulusSourceEmbedding N x ∈
          annulusHostPrimalInnerClass N := by
        change x.1 ∈ latticeBox (0, 0) (N - 1) ∨
          ∃ y, y ∈ latticeBox (0, 0) (N - 1) ∧
            squareLattice.Adj y x.1
        right
        exact ⟨y, hyHole, hxy.symm⟩
      exact Or.inl hI'

/-- The P5a dual Jordan event bounds the full-box non-crossing event under
complete vertex-boundary wiring of the annulus. -/
theorem annulus_jointWired_p5a_noFullBoxCrossing_ge_div_at_fullVertexBoundary_of_actualDualMapEq
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
          {x | x.1 ∈ PottsContinuity.PD.vertexBoundary
            (annulusVertexSet N)})
        (annulusSourceFullBoxCrossingEvent N)ᶜ).toReal := by
  have hbound := annulus_jointWired_p5a_noFullBoxCrossing_ge_div_of_actualDualMapEq
    N hN hN4 hK e hgraph hpartition q c u v hu hv f hIso hmap hP5a
  simpa only [annulusPrimalBoundaryClasses_union_eq_vertexBoundary N hN] using hbound

end

end PottsContinuity.DualityExt
