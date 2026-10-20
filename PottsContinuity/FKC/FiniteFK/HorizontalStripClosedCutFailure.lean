-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripClosedCutFailure.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutExploration
public import PottsContinuity.FKC.FiniteFK.FirstClosedBlockFailureBound
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
noncomputable section

local instance horizontalStripClosedCutFailureEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _
local instance horizontalStripClosedCutFailureEdgeDecidableEq (N n : ℕ) :
    DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _

theorem horizontalStripLeftCutBlock_card
    (N n K : ℕ) (hKN : K ≤ N) {i : ℕ} (hi : i < N - K) :
    (horizontalStripLeftCutBlock N n K i).card = 2 * n + 1 := by
  have hiN : i < N := by omega
  simp [horizontalStripLeftCutBlock, hi,
    horizontalStripRectangleCutEdges_card]

theorem horizontalStripRightCutBlock_card
    (N n K : ℕ) (hKN : K ≤ N) {i : ℕ} (hi : i < N - K) :
    (horizontalStripRightCutBlock N n K i).card = 2 * n + 1 := by
  have hiN : i < N := by omega
  simp [horizontalStripRightCutBlock, hi,
    horizontalStripRectangleCutEdges_card]

theorem horizontalStripLeftCutBlock_disjoint
    (N n K : ℕ) (hKN : K ≤ N) {i j : ℕ}
    (hi : i < N - K) (hj : j < N - K) (hij : i ≠ j) :
    Disjoint (horizontalStripLeftCutBlock N n K i)
      (horizontalStripLeftCutBlock N n K j) := by
  have hiN : i < N := by omega
  have hjN : j < N := by omega
  have hkl : (-(N : ℤ) + (i : ℤ)) ≠ (-(N : ℤ) + (j : ℤ)) := by
    intro heq
    have hcast : (i : ℤ) = (j : ℤ) := by omega
    exact hij (by exact_mod_cast hcast)
  simpa [horizontalStripLeftCutBlock, hi, hj] using
    horizontalStripRectangleCutEdges_disjoint_of_ne N n (by omega) (by omega)
      (by omega) (by omega) hkl

theorem horizontalStripRightCutBlock_disjoint
    (N n K : ℕ) (hKN : K ≤ N) {i j : ℕ}
    (hi : i < N - K) (hj : j < N - K) (hij : i ≠ j) :
    Disjoint (horizontalStripRightCutBlock N n K i)
      (horizontalStripRightCutBlock N n K j) := by
  have hiN : i < N := by omega
  have hjN : j < N := by omega
  have hkl : ((N : ℤ) - 1 - (i : ℤ)) ≠ ((N : ℤ) - 1 - (j : ℤ)) := by
    intro heq
    have hcast : (i : ℤ) = (j : ℤ) := by omega
    exact hij (by exact_mod_cast hcast)
  simpa [horizontalStripRightCutBlock, hi, hj] using
    horizontalStripRectangleCutEdges_disjoint_of_ne N n (by omega) (by omega)
      (by omega) (by omega) hkl

private theorem horizontalStripLeftCutBlocks_pairwise
    (N n K : ℕ) (hKN : K ≤ N) :
    ∀ i ∈ (List.range (N - K)).toFinset,
      ∀ j ∈ (List.range (N - K)).toFinset, i ≠ j →
        Disjoint (horizontalStripLeftCutBlock N n K i)
          (horizontalStripLeftCutBlock N n K j) := by
  intro i hi j hj hij
  have hi' : i < N - K := List.mem_range.mp (List.mem_toFinset.mp hi)
  have hj' : j < N - K := List.mem_range.mp (List.mem_toFinset.mp hj)
  exact horizontalStripLeftCutBlock_disjoint N n K hKN hi' hj' hij

private theorem horizontalStripRightCutBlocks_pairwise
    (N n K : ℕ) (hKN : K ≤ N) :
    ∀ i ∈ (List.range (N - K)).toFinset,
      ∀ j ∈ (List.range (N - K)).toFinset, i ≠ j →
        Disjoint (horizontalStripRightCutBlock N n K i)
          (horizontalStripRightCutBlock N n K j) := by
  intro i hi j hj hij
  have hi' : i < N - K := List.mem_range.mp (List.mem_toFinset.mp hi)
  have hj' : j < N - K := List.mem_range.mp (List.mem_toFinset.mp hj)
  exact horizontalStripRightCutBlock_disjoint N n K hKN hi' hj' hij

private theorem horizontalStripLeftCutBlocks_card
    (N n K : ℕ) (hKN : K ≤ N) :
    ∀ i ∈ (List.range (N - K)).toFinset,
      (horizontalStripLeftCutBlock N n K i).card = 2 * n + 1 := by
  intro i hi
  exact horizontalStripLeftCutBlock_card N n K hKN
    (List.mem_range.mp (List.mem_toFinset.mp hi))

private theorem horizontalStripRightCutBlocks_card
    (N n K : ℕ) (hKN : K ≤ N) :
    ∀ i ∈ (List.range (N - K)).toFinset,
      (horizontalStripRightCutBlock N n K i).card = 2 * n + 1 := by
  intro i hi
  exact horizontalStripRightCutBlock_card N n K hKN
    (List.mem_range.mp (List.mem_toFinset.mp hi))

theorem horizontalStripLeftBlockScan_none_probability_le
    (q : PottsContinuity.FKC.ClusterWeight) (N n K : ℕ) (hKN : K ≤ N)
    (ξ : BoundaryCondition (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n))) :
    (measure (horizontalStripCutRectangle N n) q ξ
      {A | (horizontalStripLeftBlockScan N n K A).2 = none}).toReal ≤
      (1 - (1 / (1 + loopWeight q)) ^ (2 * n + 1)) ^ (N - K) := by
  have h := firstClosedBlockScan_none_probability_le_constant_card
    q ξ (List.range (N - K)) (horizontalStripLeftCutBlock N n K)
    (2 * n + 1) (horizontalStripLeftCutBlocks_pairwise N n K hKN)
    (horizontalStripLeftCutBlocks_card N n K hKN)
  have hlen : (List.range (N - K)).toFinset.card = N - K := by
    rw [List.toFinset_card_of_nodup List.nodup_range, List.length_range]
  simpa [horizontalStripLeftBlockScan, hlen] using h

theorem horizontalStripRightBlockScan_none_probability_le
    (q : PottsContinuity.FKC.ClusterWeight) (N n K : ℕ) (hKN : K ≤ N)
    (ξ : BoundaryCondition (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n))) :
    (measure (horizontalStripCutRectangle N n) q ξ
      {A | (horizontalStripRightBlockScan N n K A).2 = none}).toReal ≤
      (1 - (1 / (1 + loopWeight q)) ^ (2 * n + 1)) ^ (N - K) := by
  have h := firstClosedBlockScan_none_probability_le_constant_card
    q ξ (List.range (N - K)) (horizontalStripRightCutBlock N n K)
    (2 * n + 1) (horizontalStripRightCutBlocks_pairwise N n K hKN)
    (horizontalStripRightCutBlocks_card N n K hKN)
  have hlen : (List.range (N - K)).toFinset.card = N - K := by
    rw [List.toFinset_card_of_nodup List.nodup_range, List.length_range]
  simpa [horizontalStripRightBlockScan, hlen] using h

theorem horizontalStripEitherBlockScan_none_probability_le
    (q : PottsContinuity.FKC.ClusterWeight) (N n K : ℕ) (hKN : K ≤ N)
    (ξ : BoundaryCondition (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n))) :
    (measure (horizontalStripCutRectangle N n) q ξ
      {A | (horizontalStripLeftBlockScan N n K A).2 = none ∨
        (horizontalStripRightBlockScan N n K A).2 = none}).toReal ≤
      2 * (1 - (1 / (1 + loopWeight q)) ^ (2 * n + 1)) ^ (N - K) := by
  let μ := measure (horizontalStripCutRectangle N n) q ξ
  let L : Set (Configuration (horizontalStripCutRectangle N n)) :=
    {A | (horizontalStripLeftBlockScan N n K A).2 = none}
  let R : Set (Configuration (horizontalStripCutRectangle N n)) :=
    {A | (horizontalStripRightBlockScan N n K A).2 = none}
  have hUnion := measureReal_union_le (μ := μ) L R
  have hL := horizontalStripLeftBlockScan_none_probability_le q N n K hKN ξ
  have hR := horizontalStripRightBlockScan_none_probability_le q N n K hKN ξ
  change μ.real (L ∪ R) ≤ _ at hUnion
  change μ.real L ≤ _ at hL
  change μ.real R ≤ _ at hR
  calc
    μ.real (L ∪ R) ≤ μ.real L + μ.real R := hUnion
    _ ≤ (1 - (1 / (1 + loopWeight q)) ^ (2 * n + 1)) ^ (N - K) +
        (1 - (1 / (1 + loopWeight q)) ^ (2 * n + 1)) ^ (N - K) :=
      add_le_add hL hR
    _ = _ := by ring

end
end PottsContinuity.FKC.Medial
