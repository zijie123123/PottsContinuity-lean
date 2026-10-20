-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripLocalCutFailure.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutFailure
public import PottsContinuity.FKC.FiniteFK.DisjointPatternAvoidance
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK

noncomputable section

local instance horizontalStripLocalCutFailureEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _
local instance horizontalStripLocalCutFailureEdgeDecidableEq (N n : ℕ) :
    DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _

/-- The i-th candidate closed cut on the left of the central column. -/
def horizontalStripLocalLeftCutBlock (N n M i : ℕ) :
    Finset (horizontalStripCutRectangle N n).edgeSet := by
  classical
  by_cases hMN : M ≤ N
  · by_cases hi : i < M
    · have hMN' : (M : ℤ) ≤ N := by exact_mod_cast hMN
      exact horizontalStripRectangleCutEdges N n (-(M : ℤ) + (i : ℤ)) (by omega) (by omega)
    · exact ∅
  · exact ∅

/-- The i-th candidate closed cut on the right of the central column. -/
def horizontalStripLocalRightCutBlock (N n M i : ℕ) :
    Finset (horizontalStripCutRectangle N n).edgeSet := by
  classical
  by_cases hMN : M ≤ N
  · by_cases hi : i < M
    · have hMN' : (M : ℤ) ≤ N := by exact_mod_cast hMN
      exact horizontalStripRectangleCutEdges N n ((M : ℤ) - 1 - (i : ℤ)) (by omega) (by omega)
    · exact ∅
  · exact ∅

def horizontalStripLocalLeftCutScan (N n M : ℕ)
    (A : Configuration (horizontalStripCutRectangle N n)) :
    Finset (horizontalStripCutRectangle N n).edgeSet × Option ℕ :=
  firstClosedBlockScan (horizontalStripLocalLeftCutBlock N n M) A (List.range M)

def horizontalStripLocalRightCutScan (N n M : ℕ)
    (A : Configuration (horizontalStripCutRectangle N n)) :
    Finset (horizontalStripCutRectangle N n).edgeSet × Option ℕ :=
  firstClosedBlockScan (horizontalStripLocalRightCutBlock N n M) A (List.range M)

/-- Failure to find at least one closed cut on either side among the M central
candidate columns. The event lives on the actual finite radius-N rectangle. -/
def horizontalStripLocalCutFailureEvent (N n M : ℕ) :
    Set (Configuration (horizontalStripCutRectangle N n)) :=
  {A | (horizontalStripLocalLeftCutScan N n M A).2 = none ∨
    (horizontalStripLocalRightCutScan N n M A).2 = none}

private theorem horizontalStripLocalLeftCutBlock_card
    (N n M : ℕ) (hMN : M ≤ N) {i : ℕ} (hi : i < M) :
    (horizontalStripLocalLeftCutBlock N n M i).card = 2 * n + 1 := by
  have hMN' : (M : ℤ) ≤ N := by exact_mod_cast hMN
  have hleft : -(N : ℤ) ≤ -(M : ℤ) + (i : ℤ) := by omega
  have hright : -(M : ℤ) + (i : ℤ) < N := by omega
  simp [horizontalStripLocalLeftCutBlock, hMN, hi,
    horizontalStripRectangleCutEdges_card]

private theorem horizontalStripLocalRightCutBlock_card
    (N n M : ℕ) (hMN : M ≤ N) {i : ℕ} (hi : i < M) :
    (horizontalStripLocalRightCutBlock N n M i).card = 2 * n + 1 := by
  have hMN' : (M : ℤ) ≤ N := by exact_mod_cast hMN
  have hleft : -(N : ℤ) ≤ (M : ℤ) - 1 - (i : ℤ) := by omega
  have hright : (M : ℤ) - 1 - (i : ℤ) < N := by omega
  simp [horizontalStripLocalRightCutBlock, hMN, hi,
    horizontalStripRectangleCutEdges_card]

private theorem horizontalStripLocalLeftCutBlock_disjoint
    (N n M : ℕ) (hMN : M ≤ N) {i j : ℕ}
    (hi : i < M) (hj : j < M) (hij : i ≠ j) :
    Disjoint (horizontalStripLocalLeftCutBlock N n M i)
      (horizontalStripLocalLeftCutBlock N n M j) := by
  have hlefti : -(N : ℤ) ≤ -(M : ℤ) + (i : ℤ) := by omega
  have hrighti : -(M : ℤ) + (i : ℤ) < N := by omega
  have hleftj : -(N : ℤ) ≤ -(M : ℤ) + (j : ℤ) := by omega
  have hrightj : -(M : ℤ) + (j : ℤ) < N := by omega
  have hkl : (-(M : ℤ) + (i : ℤ)) ≠ (-(M : ℤ) + (j : ℤ)) := by
    intro he
    have : (i : ℤ) = (j : ℤ) := by omega
    exact hij (by exact_mod_cast this)
  simpa [horizontalStripLocalLeftCutBlock, hMN, hi, hj] using
    horizontalStripRectangleCutEdges_disjoint_of_ne N n hlefti hrighti hleftj hrightj hkl

private theorem horizontalStripLocalRightCutBlock_disjoint
    (N n M : ℕ) (hMN : M ≤ N) {i j : ℕ}
    (hi : i < M) (hj : j < M) (hij : i ≠ j) :
    Disjoint (horizontalStripLocalRightCutBlock N n M i)
      (horizontalStripLocalRightCutBlock N n M j) := by
  have hlefti : -(N : ℤ) ≤ (M : ℤ) - 1 - (i : ℤ) := by omega
  have hrighti : (M : ℤ) - 1 - (i : ℤ) < N := by omega
  have hleftj : -(N : ℤ) ≤ (M : ℤ) - 1 - (j : ℤ) := by omega
  have hrightj : (M : ℤ) - 1 - (j : ℤ) < N := by omega
  have hkl : ((M : ℤ) - 1 - (i : ℤ)) ≠ ((M : ℤ) - 1 - (j : ℤ)) := by
    intro he
    have : (i : ℤ) = (j : ℤ) := by omega
    exact hij (by exact_mod_cast this)
  simpa [horizontalStripLocalRightCutBlock, hMN, hi, hj] using
    horizontalStripRectangleCutEdges_disjoint_of_ne N n hlefti hrighti hleftj hrightj hkl

private theorem horizontalStripLocalLeftCutBlocks_pairwise
    (N n M : ℕ) (hMN : M ≤ N) :
    ∀ i ∈ (List.range M).toFinset,
      ∀ j ∈ (List.range M).toFinset, i ≠ j →
        Disjoint (horizontalStripLocalLeftCutBlock N n M i)
          (horizontalStripLocalLeftCutBlock N n M j) := by
  intro i hi j hj hij
  exact horizontalStripLocalLeftCutBlock_disjoint N n M hMN
    (List.mem_range.mp (List.mem_toFinset.mp hi))
    (List.mem_range.mp (List.mem_toFinset.mp hj)) hij

private theorem horizontalStripLocalRightCutBlocks_pairwise
    (N n M : ℕ) (hMN : M ≤ N) :
    ∀ i ∈ (List.range M).toFinset,
      ∀ j ∈ (List.range M).toFinset, i ≠ j →
        Disjoint (horizontalStripLocalRightCutBlock N n M i)
          (horizontalStripLocalRightCutBlock N n M j) := by
  intro i hi j hj hij
  exact horizontalStripLocalRightCutBlock_disjoint N n M hMN
    (List.mem_range.mp (List.mem_toFinset.mp hi))
    (List.mem_range.mp (List.mem_toFinset.mp hj)) hij

private theorem horizontalStripLocalLeftCutBlocks_card
    (N n M : ℕ) (hMN : M ≤ N) :
    ∀ i ∈ (List.range M).toFinset,
      (horizontalStripLocalLeftCutBlock N n M i).card = 2 * n + 1 := by
  intro i hi
  exact horizontalStripLocalLeftCutBlock_card N n M hMN
    (List.mem_range.mp (List.mem_toFinset.mp hi))

private theorem horizontalStripLocalRightCutBlocks_card
    (N n M : ℕ) (hMN : M ≤ N) :
    ∀ i ∈ (List.range M).toFinset,
      (horizontalStripLocalRightCutBlock N n M i).card = 2 * n + 1 := by
  intro i hi
  exact horizontalStripLocalRightCutBlock_card N n M hMN
    (List.mem_range.mp (List.mem_toFinset.mp hi))

theorem horizontalStripLocalLeftCutScan_none_probability_le
    (q : ClusterWeight) (N n M : ℕ) (hMN : M ≤ N)
    (ξ : BoundaryCondition (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n))) :
    (measure (horizontalStripCutRectangle N n) q ξ
      {A | (horizontalStripLocalLeftCutScan N n M A).2 = none}).toReal ≤
      (1 - (1 / (1 + loopWeight q)) ^ (2 * n + 1)) ^ M := by
  have h := firstClosedBlockScan_none_probability_le_constant_card
    q ξ (List.range M) (horizontalStripLocalLeftCutBlock N n M)
    (2 * n + 1) (horizontalStripLocalLeftCutBlocks_pairwise N n M hMN)
    (horizontalStripLocalLeftCutBlocks_card N n M hMN)
  have hlen : (List.range M).toFinset.card = M := by
    rw [List.toFinset_card_of_nodup List.nodup_range, List.length_range]
  simpa [horizontalStripLocalLeftCutScan, hlen] using h

theorem horizontalStripLocalRightCutScan_none_probability_le
    (q : ClusterWeight) (N n M : ℕ) (hMN : M ≤ N)
    (ξ : BoundaryCondition (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n))) :
    (measure (horizontalStripCutRectangle N n) q ξ
      {A | (horizontalStripLocalRightCutScan N n M A).2 = none}).toReal ≤
      (1 - (1 / (1 + loopWeight q)) ^ (2 * n + 1)) ^ M := by
  have h := firstClosedBlockScan_none_probability_le_constant_card
    q ξ (List.range M) (horizontalStripLocalRightCutBlock N n M)
    (2 * n + 1) (horizontalStripLocalRightCutBlocks_pairwise N n M hMN)
    (horizontalStripLocalRightCutBlocks_card N n M hMN)
  have hlen : (List.range M).toFinset.card = M := by
    rw [List.toFinset_card_of_nodup List.nodup_range, List.length_range]
  simpa [horizontalStripLocalRightCutScan, hlen] using h

theorem horizontalStripLocalCutFailure_probability_le
    (q : ClusterWeight) (N n M : ℕ) (hMN : M ≤ N)
    (ξ : BoundaryCondition (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n))) :
    (measure (horizontalStripCutRectangle N n) q ξ
      (horizontalStripLocalCutFailureEvent N n M)).toReal ≤
      2 * (1 - (1 / (1 + loopWeight q)) ^ (2 * n + 1)) ^ M := by
  let μ := measure (horizontalStripCutRectangle N n) q ξ
  let L : Set (Configuration (horizontalStripCutRectangle N n)) :=
    {A | (horizontalStripLocalLeftCutScan N n M A).2 = none}
  let R : Set (Configuration (horizontalStripCutRectangle N n)) :=
    {A | (horizontalStripLocalRightCutScan N n M A).2 = none}
  have hUnion := measureReal_union_le (μ := μ) L R
  have hL := horizontalStripLocalLeftCutScan_none_probability_le q N n M hMN ξ
  have hR := horizontalStripLocalRightCutScan_none_probability_le q N n M hMN ξ
  change μ.real (L ∪ R) ≤ _ at hUnion
  change μ.real L ≤ _ at hL
  change μ.real R ≤ _ at hR
  calc
    μ.real (L ∪ R) ≤ μ.real L + μ.real R := hUnion
    _ ≤ (1 - (1 / (1 + loopWeight q)) ^ (2 * n + 1)) ^ M +
        (1 - (1 / (1 + loopWeight q)) ^ (2 * n + 1)) ^ M := add_le_add hL hR
    _ = _ := by ring

end
end PottsContinuity.FKC.Medial
