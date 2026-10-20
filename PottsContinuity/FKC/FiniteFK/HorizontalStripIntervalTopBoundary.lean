-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripIntervalTopBoundary.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripTopBoundary
public import PottsContinuity.FKC.FiniteFK.EmbeddedBoundaryComparison
public import PottsContinuity.FKC.FiniteFK.RectangleEvents
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open scoped BigOperators
open FiniteProbability MeasureTheory
noncomputable section

/-- The top-only wired set on an actual horizontal interval rectangle. -/
def horizontalStripIntervalTopWiredSet (a : ℤ) (w n : ℕ) :
    Set (RectangleVertex (a, 0) w (2 * n)) :=
  {v | v.val.2 = (2 * n : ℤ)}

def horizontalStripIntervalTopWiredBoundary (a : ℤ) (w n : ℕ) :
    BoundaryCondition (RectangleVertex (a, 0) w (2 * n)) :=
  BoundaryCondition.wired (horizontalStripIntervalTopWiredSet a w n)

local instance intervalInnerEdgeFintype (a : ℤ) (w n : ℕ) :
    Fintype (rectangleGraph (a, 0) w (2 * n)).edgeSet := Fintype.ofFinite _
local instance intervalOuterEdgeFintype (N n : ℕ) :
    Fintype (rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)).edgeSet := Fintype.ofFinite _

/-- The actual coordinate inclusion of a horizontal interval into a centered
rectangle when both horizontal endpoints fit. -/
theorem horizontalStripInterval_subset {a : ℤ} {w N n : ℕ}
    (hleft : -(N : ℤ) ≤ a) (hright : a + (w : ℤ) ≤ N) :
    latticeRectangle (a, 0) w (2 * n) ⊆
      latticeRectangle (-(N : ℤ), 0) (2 * N) (2 * n) := by
  intro v hv
  rw [mem_latticeRectangle] at hv ⊢
  rcases hv with ⟨⟨hxlo, hxhi⟩, hy⟩
  constructor
  · constructor
    · omega
    · omega
  · exact hy

def horizontalStripIntervalEmbedding {a : ℤ} {w N n : ℕ}
    (hleft : -(N : ℤ) ≤ a) (hright : a + (w : ℤ) ≤ N) :
    RectangleVertex (a, 0) w (2 * n) ↪
      RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) :=
  rectangleVertexEmbedding (horizontalStripInterval_subset hleft hright)

@[simp] theorem horizontalStripIntervalEmbedding_val {a : ℤ} {w N n : ℕ}
    (hleft : -(N : ℤ) ≤ a) (hright : a + (w : ℤ) ≤ N)
    (v : RectangleVertex (a, 0) w (2 * n)) :
    (horizontalStripIntervalEmbedding hleft hright v).val = v.val := rfl

theorem horizontalStripInterval_map_le {a : ℤ} {w N n : ℕ}
    (hleft : -(N : ℤ) ≤ a) (hright : a + (w : ℤ) ≤ N) :
    (rectangleGraph (a, 0) w (2 * n)).map
        (horizontalStripIntervalEmbedding hleft hright) ≤
      rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n) :=
  rectangleGraph_map_rectangleVertexEmbedding (horizontalStripInterval_subset hleft hright)

/-- Pullback of centered top-only wiring is exactly top-only wiring on the
actual included interval. -/
theorem horizontalStripIntervalTopWired_pullback_partition_eq
    {a : ℤ} {w N n : ℕ} (hleft : -(N : ℤ) ≤ a)
    (hright : a + (w : ℤ) ≤ N) :
    (isolatedExtensionPullbackBoundary (horizontalStripIntervalEmbedding hleft hright)
      (horizontalStripTopWiredBoundary N n)).partition =
      (horizontalStripIntervalTopWiredBoundary a w n).partition := by
  apply Setoid.ext
  intro u v
  change (horizontalStripTopWiredBoundary N n).partition.r
      (horizontalStripIntervalEmbedding hleft hright u)
      (horizontalStripIntervalEmbedding hleft hright v) ↔
    (horizontalStripIntervalTopWiredBoundary a w n).partition.r u v
  change (BoundaryCondition.wired (horizontalStripTopWiredSet N n)).partition.r
      (horizontalStripIntervalEmbedding hleft hright u)
      (horizontalStripIntervalEmbedding hleft hright v) ↔
    (BoundaryCondition.wired (horizontalStripIntervalTopWiredSet a w n)).partition.r u v
  rw [BoundaryCondition.wired_rel, BoundaryCondition.wired_rel]
  simp only [horizontalStripTopWiredSet, horizontalStripIntervalTopWiredSet,
    Set.mem_ofPred_eq]
  constructor
  · rintro (heq | ⟨hu, hv⟩)
    · exact Or.inl ((horizontalStripIntervalEmbedding hleft hright).injective heq)
    · change u.val.2 = (2 * n : ℤ) at hu
      change v.val.2 = (2 * n : ℤ) at hv
      exact Or.inr ⟨hu, hv⟩
  · rintro (heq | ⟨hu, hv⟩)
    · exact Or.inl (congrArg (horizontalStripIntervalEmbedding hleft hright) heq)
    · change u.val.2 = (2 * n : ℤ) at hu
      change v.val.2 = (2 * n : ℤ) at hv
      exact Or.inr ⟨by simpa using hu, by simpa using hv⟩

/-- Increasing-event probability comparison for the actual inner interval law
and its actual restriction from the centered top-wired rectangle. -/
theorem horizontalStripIntervalTopWired_probability_le
    {a : ℤ} {w N n : ℕ} (hleft : -(N : ℤ) ≤ a)
    (hright : a + (w : ℤ) ≤ N) (q : ClusterWeight)
    (E : Set (Configuration (rectangleGraph (a, 0) w (2 * n))))
    (hE : IsUpperSet E) :
    (measure (rectangleGraph (a, 0) w (2 * n)) q
      (horizontalStripIntervalTopWiredBoundary a w n) E).toReal ≤
    (measure (rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)) q
      (horizontalStripTopWiredBoundary N n)
      {A | embeddedConfigurationRestriction
        (rectangleGraph (a, 0) w (2 * n))
        (rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n))
        (horizontalStripIntervalEmbedding hleft hright)
        (horizontalStripInterval_map_le hleft hright) A ∈ E}).toReal := by
  let G := rectangleGraph (a, 0) w (2 * n)
  let H := rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)
  let f : RectangleVertex (a, 0) w (2 * n) ↪
      RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) :=
    horizontalStripIntervalEmbedding (n := n) hleft hright
  have hGH : G.map f ≤ H := horizontalStripInterval_map_le hleft hright
  change (measure G q (horizontalStripIntervalTopWiredBoundary a w n) E).toReal ≤
    (measure H q (horizontalStripTopWiredBoundary N n)
      {A | embeddedConfigurationRestriction G H f hGH A ∈ E}).toReal
  have hboundaryLaw : law G q (horizontalStripIntervalTopWiredBoundary a w n) =
      law G q (isolatedExtensionPullbackBoundary f
        (horizontalStripTopWiredBoundary N n)) := by
    symm
    exact law_eq_of_boundary_partition_eq q _ _ (by
      exact horizontalStripIntervalTopWired_pullback_partition_eq hleft hright)
  have hpart := horizontalStripIntervalTopWired_pullback_partition_eq (n := n) hleft hright
  have hboundary :
      (measure G q (horizontalStripIntervalTopWiredBoundary a w n) E).toReal =
        (measure G q
          (isolatedExtensionPullbackBoundary f (horizontalStripTopWiredBoundary N n)) E).toReal := by
    apply le_antisymm
    · exact measure_boundary_comparison q
        (horizontalStripIntervalTopWiredBoundary a w n)
        (isolatedExtensionPullbackBoundary f (horizontalStripTopWiredBoundary N n))
        (le_of_eq hpart.symm) E hE
    · exact measure_boundary_comparison q
        (isolatedExtensionPullbackBoundary f (horizontalStripTopWiredBoundary N n))
        (horizontalStripIntervalTopWiredBoundary a w n)
        (le_of_eq hpart) E hE
  calc
    (measure G q (horizontalStripIntervalTopWiredBoundary a w n) E).toReal =
      (measure G q
        (isolatedExtensionPullbackBoundary f (horizontalStripTopWiredBoundary N n)) E).toReal := hboundary
    _ ≤ (measure H q (horizontalStripTopWiredBoundary N n)
        {A | embeddedConfigurationRestriction G H f hGH A ∈ E}).toReal :=
      embedded_boundary_probability_le G H f hGH q
        (horizontalStripTopWiredBoundary N n) E hE

end
end PottsContinuity.FKC.FiniteFK
