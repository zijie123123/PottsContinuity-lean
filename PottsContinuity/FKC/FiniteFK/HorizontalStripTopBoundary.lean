-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripTopBoundary.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RectangleEvents
public import PottsContinuity.FKC.FiniteFK.EmbeddedBoundaryComparison
public import PottsContinuity.FKC.FiniteFK.RectangleBottomCollar

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open scoped BigOperators
open FiniteProbability

noncomputable section

local instance horizontalStripInnerEdgeFintype (M n : ℕ) :
    Fintype (rectangleGraph (-(M : ℤ), 0) (2 * M) (2 * n)).edgeSet :=
  Fintype.ofFinite _

local instance horizontalStripOuterEdgeFintype (N n : ℕ) :
    Fintype (rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)).edgeSet :=
  Fintype.ofFinite _

def horizontalStripTopWiredSet (M n : ℕ) :
    Set (RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n)) :=
  {v | v.val.2 = (2 * n : ℤ)}

def horizontalStripTopWiredBoundary (M n : ℕ) :
    BoundaryCondition (RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n)) :=
  BoundaryCondition.wired (horizontalStripTopWiredSet M n)

theorem horizontalStripRectangle_subset {M N n : ℕ} (hMN : M ≤ N) :
    latticeRectangle (-(M : ℤ), 0) (2 * M) (2 * n) ⊆
      latticeRectangle (-(N : ℤ), 0) (2 * N) (2 * n) := by
  intro v hv
  rw [mem_latticeRectangle] at hv ⊢
  constructor
  · constructor <;> omega
  · exact hv.2

def horizontalStripRectangleEmbedding {M N n : ℕ} (hMN : M ≤ N) :
    RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n) ↪
      RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) :=
  rectangleVertexEmbedding (horizontalStripRectangle_subset hMN)

@[simp] theorem horizontalStripRectangleEmbedding_val {M N n : ℕ}
    (hMN : M ≤ N) (v : RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n)) :
    (horizontalStripRectangleEmbedding hMN v).val = v.val := rfl

theorem horizontalStripRectangle_map_le {M N n : ℕ} (hMN : M ≤ N) :
    (rectangleGraph (-(M : ℤ), 0) (2 * M) (2 * n)).map
        (horizontalStripRectangleEmbedding hMN) ≤
      rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n) :=
  rectangleGraph_map_rectangleVertexEmbedding (horizontalStripRectangle_subset hMN)

theorem horizontalStripTopWired_pullback_partition_eq {M N n : ℕ} (hMN : M ≤ N) :
    (isolatedExtensionPullbackBoundary (horizontalStripRectangleEmbedding hMN)
      (horizontalStripTopWiredBoundary N n)).partition =
      (horizontalStripTopWiredBoundary M n).partition := by
  apply Setoid.ext
  intro u v
  change (horizontalStripTopWiredBoundary N n).partition.r
    ((horizontalStripRectangleEmbedding hMN) u)
    ((horizontalStripRectangleEmbedding hMN) v) ↔
    (horizontalStripTopWiredBoundary M n).partition.r u v
  change (BoundaryCondition.wired (horizontalStripTopWiredSet N n)).partition.r
    ((horizontalStripRectangleEmbedding hMN) u)
    ((horizontalStripRectangleEmbedding hMN) v) ↔
    (BoundaryCondition.wired (horizontalStripTopWiredSet M n)).partition.r u v
  rw [BoundaryCondition.wired_rel, BoundaryCondition.wired_rel]
  simp only [horizontalStripTopWiredSet, Set.mem_ofPred_eq]
  constructor
  · rintro (heq | ⟨hu, hv⟩)
    · exact Or.inl ((horizontalStripRectangleEmbedding (n := n) hMN).injective heq)
    · change u.val.2 = (2 * n : ℤ) at hu
      change v.val.2 = (2 * n : ℤ) at hv
      exact Or.inr ⟨hu, hv⟩
  · rintro (heq | ⟨hu, hv⟩)
    · exact Or.inl (congrArg (horizontalStripRectangleEmbedding (n := n) hMN) heq)
    · change u.val.2 = (2 * n : ℤ) at hu
      change v.val.2 = (2 * n : ℤ) at hv
      exact Or.inr ⟨by simpa using hu, by simpa using hv⟩

theorem horizontalStripTopWired_expectation_mono {M N n : ℕ}
    (hMN : M ≤ N) (q : ClusterWeight)
    (F : Configuration (rectangleGraph (-(M : ℤ), 0) (2 * M) (2 * n)) → ℝ)
    (hF0 : ∀ A, 0 ≤ F A) (hF : Monotone F) :
    expectation
        (law (rectangleGraph (-(M : ℤ), 0) (2 * M) (2 * n)) q
          (horizontalStripTopWiredBoundary M n)) F ≤
      expectation
        (law (rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)) q
          (horizontalStripTopWiredBoundary N n))
    (fun A => F (embeddedConfigurationRestriction
          (rectangleGraph (-(M : ℤ), 0) (2 * M) (2 * n))
          (rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n))
          (horizontalStripRectangleEmbedding hMN)
          (horizontalStripRectangle_map_le hMN) A)) := by
  let G := rectangleGraph (-(M : ℤ), 0) (2 * M) (2 * n)
  let H := rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)
  let f : RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n) ↪
      RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) :=
    horizontalStripRectangleEmbedding (n := n) hMN
  have hGH : G.map f ≤ H := horizontalStripRectangle_map_le hMN
  change expectation (law G q (horizontalStripTopWiredBoundary M n)) F ≤
    expectation (law H q (horizontalStripTopWiredBoundary N n))
      (fun A => F (embeddedConfigurationRestriction G H f hGH A))
  have hboundaryLaw :
      law G q (horizontalStripTopWiredBoundary M n) =
      law G q (isolatedExtensionPullbackBoundary f
          (horizontalStripTopWiredBoundary N n)) := by
    symm
    exact law_eq_of_boundary_partition_eq q _ _ (by
      exact horizontalStripTopWired_pullback_partition_eq hMN)
  rw [hboundaryLaw]
  exact embedded_boundary_expectation_le G H f hGH q
    (horizontalStripTopWiredBoundary N n) F hF0 hF

end
end PottsContinuity.FKC.FiniteFK
