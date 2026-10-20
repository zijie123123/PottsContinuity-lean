-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/FirstClosedBlockFailureBound.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.FirstClosedBlockScan
public import PottsContinuity.FKC.FiniteFK.DisjointPatternAvoidance
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance firstClosedBlockBoundEdgeFintype : Fintype G.edgeSet :=
  Fintype.ofFinite _
local instance firstClosedBlockBoundEdgeDecidableEq : DecidableEq G.edgeSet :=
  Classical.decEq _

omit [Finite V] in
private theorem pattern_false_iff_disjoint
    (F : Finset G.edgeSet) (A : Configuration G) :
    A ∈ finiteConfigurationPatternEvent F (fun _ => false) ↔ Disjoint A F := by
  change (∀ e ∈ F, (e ∈ A ↔ false = true)) ↔ Disjoint A F
  simp only [Bool.false_eq_true, iff_false]
  constructor
  · intro h
    rw [Finset.disjoint_left]
    intro e heA heF
    exact h e heF heA
  · intro h e heF heA
    exact (Finset.disjoint_right.mp h) heF heA

omit [Finite V] in
/-- A scan returns none exactly when every listed closed block is hit by an
open edge; equivalently, the configuration avoids every all-closed block
pattern in the deduplicated list of indices. -/
theorem firstClosedBlockScan_none_iff_avoids_closed_patterns
    {ι : Type*} [DecidableEq ι]
    (D : ι → Finset G.edgeSet) (A : Configuration G) (js : List ι) :
    (firstClosedBlockScan D A js).2 = none ↔
      A ∈ finitePatternAvoidanceEvent js.toFinset D (fun _ _ => false) := by
  rw [firstClosedBlockScan_none_iff]
  simp only [finitePatternAvoidanceEvent, Set.mem_ofPred_eq, List.mem_toFinset]
  simp_rw [pattern_false_iff_disjoint]

/-- The exact first-block scan failure event has the usual disjoint-pattern
avoidance upper bound, using pairwise edge-disjointness and the proved FK
finite-energy estimate, without assuming probabilistic independence. -/
theorem firstClosedBlockScan_none_probability_le
    {ι : Type*} [DecidableEq ι]
    (q : ClusterWeight) (ξ : BoundaryCondition V)
    (js : List ι) (D : ι → Finset G.edgeSet)
    (hdisj : ∀ i ∈ js.toFinset, ∀ j ∈ js.toFinset, i ≠ j →
      Disjoint (D i) (D j)) :
    (measure G q ξ {A : Configuration G |
      (firstClosedBlockScan D A js).2 = none}).toReal ≤
      ∏ i ∈ js.toFinset,
        (1 - (1 / (1 + loopWeight q)) ^ (D i).card) := by
  have hevent :
      {A : Configuration G | (firstClosedBlockScan D A js).2 = none} =
        finitePatternAvoidanceEvent js.toFinset D (fun _ _ => false) := by
    ext A
    exact firstClosedBlockScan_none_iff_avoids_closed_patterns D A js
  rw [hevent]
  exact configurationProbability_disjoint_pattern_avoidance
    q ξ js.toFinset D (fun _ _ => false) hdisj

/-- When all tested blocks have the same size, the scan-failure estimate is
the corresponding single factor raised to the number of distinct indices. -/
theorem firstClosedBlockScan_none_probability_le_constant_card
    {ι : Type*} [DecidableEq ι]
    (q : ClusterWeight) (ξ : BoundaryCondition V)
    (js : List ι) (D : ι → Finset G.edgeSet) (k : ℕ)
    (hdisj : ∀ i ∈ js.toFinset, ∀ j ∈ js.toFinset, i ≠ j →
      Disjoint (D i) (D j))
    (hcard : ∀ i ∈ js.toFinset, (D i).card = k) :
    (measure G q ξ {A : Configuration G |
      (firstClosedBlockScan D A js).2 = none}).toReal ≤
      (1 - (1 / (1 + loopWeight q)) ^ k) ^ js.toFinset.card := by
  calc
    _ ≤ ∏ i ∈ js.toFinset,
        (1 - (1 / (1 + loopWeight q)) ^ (D i).card) :=
      firstClosedBlockScan_none_probability_le q ξ js D hdisj
    _ = _ := by
      calc
        ∏ i ∈ js.toFinset, (1 - (1 / (1 + loopWeight q)) ^ (D i).card) =
            ∏ i ∈ js.toFinset, (1 - (1 / (1 + loopWeight q)) ^ k) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [hcard i hi]
        _ = (1 - (1 / (1 + loopWeight q)) ^ k) ^ js.toFinset.card := by
          simp

end
end PottsContinuity.FKC.FiniteFK
