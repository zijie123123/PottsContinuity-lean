-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripAsymmetricTopLimit.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripHeightBoundaryLimit
public import PottsContinuity.FKC.FiniteFK.HorizontalStripIntervalCylinders
public import PottsContinuity.FKC.FiniteFK.RectangleDualCarrier
public import PottsContinuity.FKC.FiniteFK.HorizontalStripTopExhaustion
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Portmanteau

@[expose] public section

open Filter MeasureTheory Topology

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
open FiniteProbability

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance asymEdgeFintype (N n : ℕ) :
    Fintype (rectangleGraph (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n)).edgeSet :=
  Fintype.ofFinite _

/-- The literal one-sided exhaustion interval `[-N-1,N]` at height `2n`. -/
def horizontalStripAsymmetricRectangle (N n : ℕ) :=
  rectangleGraph (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n)

/-- Extend the actual finite configuration by closing all original lattice
edges outside the asymmetric interval. -/
noncomputable def horizontalStripAsymmetricPlaneExtension (N n : ℕ)
    (A : Configuration (horizontalStripAsymmetricRectangle N n)) : LatticeConfiguration := by
  classical
  exact fun e => decide (e ∈ A.image (rectanglePrimalEdgeToSquareEdge
    (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n)))

 theorem horizontalStripAsymmetric_contains_centered (N n : ℕ) :
    latticeRectangle (-(N : ℤ), 0) (2 * N) (2 * n) ⊆
      latticeRectangle (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n) := by
  intro v hv
  rw [mem_latticeRectangle] at hv ⊢
  rcases hv with ⟨⟨hlo, hhi⟩, hy⟩
  constructor
  · constructor <;> omega
  · exact hy

def horizontalStripAsymmetricInnerEmbedding (N n : ℕ) :
    RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) ↪
      RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n) :=
  rectangleVertexEmbedding (horizontalStripAsymmetric_contains_centered N n)

@[simp] private theorem horizontalStripAsymmetricInnerEmbedding_val (N n : ℕ)
    (v : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)) :
    (horizontalStripAsymmetricInnerEmbedding N n v).val = v.val := rfl

private theorem horizontalStripAsymmetric_inner_map_le (N n : ℕ) :
    (horizontalStripCutRectangle N n).map
      (horizontalStripAsymmetricInnerEmbedding N n) ≤
    rectangleGraph (-(N + 1 : ℤ), 0) (2 * N + 1) (2 * n) := by
  change (rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)).map
      (horizontalStripAsymmetricInnerEmbedding N n) ≤
    rectangleGraph (-(N + 1 : ℤ), 0) (2 * N + 1) (2 * n)
  exact rectangleGraph_map_rectangleVertexEmbedding (horizontalStripAsymmetric_contains_centered N n)

private theorem horizontalStripAsymmetric_top_pullback_partition_eq (N n : ℕ) :
    (isolatedExtensionPullbackBoundary (horizontalStripAsymmetricInnerEmbedding N n)
      (horizontalStripIntervalTopWiredBoundary (-(N + 1 : ℕ)) (2 * N + 1) n)).partition =
    (horizontalStripTopWiredBoundary N n).partition := by
  apply Setoid.ext
  intro u v
  change (horizontalStripIntervalTopWiredBoundary (-(N + 1 : ℕ)) (2 * N + 1) n).partition.r
      (horizontalStripAsymmetricInnerEmbedding N n u)
      (horizontalStripAsymmetricInnerEmbedding N n v) ↔
    (horizontalStripTopWiredBoundary N n).partition.r u v
  change (BoundaryCondition.wired
      (horizontalStripIntervalTopWiredSet (-(N + 1 : ℕ)) (2 * N + 1) n)).partition.r
      (horizontalStripAsymmetricInnerEmbedding N n u)
      (horizontalStripAsymmetricInnerEmbedding N n v) ↔
    (BoundaryCondition.wired (horizontalStripTopWiredSet N n)).partition.r u v
  rw [BoundaryCondition.wired_rel, BoundaryCondition.wired_rel]
  simp only [horizontalStripIntervalTopWiredSet, horizontalStripTopWiredSet,
    Set.mem_ofPred_eq]
  constructor
  · rintro (heq | ⟨hu, hv⟩)
    · exact Or.inl ((horizontalStripAsymmetricInnerEmbedding N n).injective heq)
    · change ((horizontalStripAsymmetricInnerEmbedding N n u).val).2 = _ at hu
      change ((horizontalStripAsymmetricInnerEmbedding N n v).val).2 = _ at hv
      rw [horizontalStripAsymmetricInnerEmbedding_val] at hu
      rw [horizontalStripAsymmetricInnerEmbedding_val] at hv
      exact Or.inr ⟨hu, hv⟩
  · rintro (heq | ⟨hu, hv⟩)
    · exact Or.inl (congrArg (horizontalStripAsymmetricInnerEmbedding N n) heq)
    · change u.val.2 = _ at hu
      change v.val.2 = _ at hv
      have hvalu := horizontalStripAsymmetricInnerEmbedding_val N n u
      have hvalv := horizontalStripAsymmetricInnerEmbedding_val N n v
      exact Or.inr ⟨by simpa only [← hvalu] using hu,
        by simpa only [← hvalv] using hv⟩

private theorem horizontalStripAsymmetric_innerCylinder_upper (N n : ℕ)
    (F : Finset squareLattice.edgeSet) :
    IsUpperSet (horizontalStripRectangleCylinderEvent N n F) := by
  intro A B hAB hA
  exact hA.trans (Finset.image_mono _ hAB)

private theorem rectanglePrimalEdgeToSquareEdge_val_local (a : LatticeVertex) (w h : ℕ)
    (e : (rectangleGraph a w h).edgeSet) :
    (rectanglePrimalEdgeToSquareEdge a w h e).val =
      Sym2.map (fun z : RectangleVertex a w h => z.val) e.val := rfl

private theorem horizontalStripAsymmetric_innerEdge_compatible (N n : ℕ)
    (e : (horizontalStripCutRectangle N n).edgeSet) :
    rectanglePrimalEdgeToSquareEdge (-(N + 1 : ℤ), 0) (2 * N + 1) (2 * n)
        (embeddedEdgeEmbedding (horizontalStripCutRectangle N n)
          (horizontalStripAsymmetricRectangle N n) (horizontalStripAsymmetricInnerEmbedding N n)
          (horizontalStripAsymmetric_inner_map_le N n) e) =
      horizontalStripRectangleOriginalEdge N n e := by
  apply Subtype.ext
  change (rectanglePrimalEdgeToSquareEdge (-(N + 1 : ℤ), 0) (2 * N + 1) (2 * n)
        (embeddedEdgeEmbedding (horizontalStripCutRectangle N n)
          (rectangleGraph (-(N + 1 : ℤ), 0) (2 * N + 1) (2 * n))
          (horizontalStripAsymmetricInnerEmbedding N n)
          (horizontalStripAsymmetric_inner_map_le N n) e)).val =
      (horizontalStripRectangleOriginalEdge N n e).val
  rw [rectanglePrimalEdgeToSquareEdge_val_local, horizontalStripRectangleOriginalEdge_val,
    embeddedEdgeEmbedding_coe]
  change Sym2.map (fun z : RectangleVertex (-(N + 1 : ℤ), 0) (2 * N + 1) (2 * n) => z.val)
      (Sym2.map (horizontalStripAsymmetricInnerEmbedding N n) e.val) =
    Sym2.map (fun z : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) => z.val) e.val
  rw [Sym2.map_map]
  congr 1

private theorem horizontalStripAsymmetric_inner_restrict_cylinder_subset
    (N n : ℕ) (F : Finset squareLattice.edgeSet) :
    {A : Configuration (horizontalStripAsymmetricRectangle N n) |
      embeddedConfigurationRestriction (horizontalStripCutRectangle N n)
        (horizontalStripAsymmetricRectangle N n)
        (horizontalStripAsymmetricInnerEmbedding N n)
        (horizontalStripAsymmetric_inner_map_le N n) A ∈
          horizontalStripRectangleCylinderEvent N n F} ⊆
    horizontalStripIntervalCylinderEvent (-(N + 1 : ℤ)) (2 * N + 1) n F := by
  intro A hA e he
  obtain ⟨e₀, he₀, hEq⟩ := Finset.mem_image.mp (hA he)
  have he₀A : embeddedEdgeEmbedding (horizontalStripCutRectangle N n)
      (horizontalStripAsymmetricRectangle N n) (horizontalStripAsymmetricInnerEmbedding N n)
      (horizontalStripAsymmetric_inner_map_le N n) e₀ ∈ A :=
    (mem_embeddedConfigurationRestriction _ _ _ _ A _).mp he₀
  refine Finset.mem_image.mpr ⟨embeddedEdgeEmbedding
      (horizontalStripCutRectangle N n)
      (horizontalStripAsymmetricRectangle N n) (horizontalStripAsymmetricInnerEmbedding N n)
      (horizontalStripAsymmetric_inner_map_le N n) e₀, he₀A, ?_⟩
  exact (horizontalStripAsymmetric_innerEdge_compatible N n e₀).trans hEq

theorem horizontalStripAsymmetricInterval_allOpen_lower_centered
    (q : ClusterWeight) (N n : ℕ) (F : Finset squareLattice.edgeSet) :
    measure (horizontalStripCutRectangle N n) q (horizontalStripTopWiredBoundary N n)
        (horizontalStripRectangleCylinderEvent N n F) ≤
      measure (horizontalStripAsymmetricRectangle N n) q
        (horizontalStripIntervalTopWiredBoundary (-(N + 1 : ℕ)) (2 * N + 1) n)
        (horizontalStripIntervalCylinderEvent (-(N + 1 : ℤ)) (2 * N + 1) n F) := by
  let G := horizontalStripCutRectangle N n
  let H := horizontalStripAsymmetricRectangle N n
  let f := horizontalStripAsymmetricInnerEmbedding N n
  let hGH := horizontalStripAsymmetric_inner_map_le N n
  have hlaw : law G q (horizontalStripTopWiredBoundary N n) =
      law G q (isolatedExtensionPullbackBoundary f
        (horizontalStripIntervalTopWiredBoundary (-(N + 1 : ℕ)) (2 * N + 1) n)) := by
    apply law_eq_of_boundary_partition_eq q _ _
    exact (horizontalStripAsymmetric_top_pullback_partition_eq N n).symm
  have hcomparison := embedded_boundary_probability_le G H f hGH q
    (horizontalStripIntervalTopWiredBoundary (-(N + 1 : ℕ)) (2 * N + 1) n)
    (horizontalStripRectangleCylinderEvent N n F)
    (horizontalStripAsymmetric_innerCylinder_upper N n F)
  have hsubset :
      measure H q (horizontalStripIntervalTopWiredBoundary (-(N + 1 : ℕ)) (2 * N + 1) n)
        {A | embeddedConfigurationRestriction G H f hGH A ∈
          horizontalStripRectangleCylinderEvent N n F} ≤
      measure H q (horizontalStripIntervalTopWiredBoundary (-(N + 1 : ℕ)) (2 * N + 1) n)
        (horizontalStripIntervalCylinderEvent (-(N + 1 : ℤ)) (2 * N + 1) n F) := by
    exact measure_mono (horizontalStripAsymmetric_inner_restrict_cylinder_subset N n F)
  have hleft :
      measure G q (horizontalStripTopWiredBoundary N n)
        (horizontalStripRectangleCylinderEvent N n F) =
      measure G q (isolatedExtensionPullbackBoundary f
        (horizontalStripIntervalTopWiredBoundary (-(N + 1 : ℕ)) (2 * N + 1) n))
        (horizontalStripRectangleCylinderEvent N n F) := by
    change (law G q (horizontalStripTopWiredBoundary N n)).toMeasure _ =
      (law G q (isolatedExtensionPullbackBoundary f
        (horizontalStripIntervalTopWiredBoundary (-(N + 1 : ℕ)) (2 * N + 1) n))).toMeasure _
    rw [hlaw]
  have hcompReal :
      (measure G q (isolatedExtensionPullbackBoundary f
        (horizontalStripIntervalTopWiredBoundary (-(N + 1 : ℕ)) (2 * N + 1) n))
        (horizontalStripRectangleCylinderEvent N n F)).toReal ≤
      (measure H q (horizontalStripIntervalTopWiredBoundary (-(N + 1 : ℕ)) (2 * N + 1) n)
        {A | embeddedConfigurationRestriction G H f hGH A ∈
          horizontalStripRectangleCylinderEvent N n F}).toReal := hcomparison
  have hsubReal :
      (measure H q (horizontalStripIntervalTopWiredBoundary (-(N + 1 : ℕ)) (2 * N + 1) n)
        {A | embeddedConfigurationRestriction G H f hGH A ∈
          horizontalStripRectangleCylinderEvent N n F}).toReal ≤
      (measure H q (horizontalStripIntervalTopWiredBoundary (-(N + 1 : ℕ)) (2 * N + 1) n)
        (horizontalStripIntervalCylinderEvent (-(N + 1 : ℤ)) (2 * N + 1) n F)).toReal := by
    exact ENNReal.toReal_mono (measure_ne_top _ _) hsubset
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [hleft]
  exact hcompReal.trans hsubReal

end
end PottsContinuity.FKC.Medial
