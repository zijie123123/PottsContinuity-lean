module

public import PottsContinuity.BD12.DRTBoxDifferential
public import PottsContinuity.BD12.BoxCentredOneArmComparison
public import PottsContinuity.BD12.DRTMeanOrder
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Compare the restricted inner-path denominator with full outer centred
one-arm sums under the same original finite FK law. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section
open scoped Classical
local instance boxArmMaxEdges (c : LatticeVertex) (n : ℕ) :
    Fintype (finiteLatticeGraph (latticeBox c n)).edgeSet := Fintype.ofFinite _
local instance boxArmMaxEdgeDecidableEq (c : LatticeVertex) (n : ℕ) :
    DecidableEq (finiteLatticeGraph (latticeBox c n)).edgeSet := Classical.decEq _
local instance boxArmMaxVerticesNonempty (c : LatticeVertex) (n : ℕ) :
    Nonempty (latticeBox c n : Set LatticeVertex) := ⟨radiusBoxCenter c n⟩

/-- Genuine maximum over inner vertices of FULL outer centred one-arm sums. -/
def drtBoxOuterArmMaximum (c : LatticeVertex) (n N : ℕ) (hnN : n ≤ N)
    (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition (latticeBox c N : Set LatticeVertex))
    (J : (finiteLatticeGraph (latticeBox c N)).edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ)) : ℝ :=
  (Finset.univ.image (fun u : (latticeBox c n : Set LatticeVertex) =>
    ∑ j ∈ Finset.range n, drtMean (finiteLatticeGraph (latticeBox c N)) q ξ J β
      (radiusOneArmIndicator (finiteLatticeGraph (latticeBox c N))
        (fun v => latticeRadius u.val v.val) (radiusBoxInclusion c n N hnN u) j))).max'
    (Finset.univ_nonempty.image _)

theorem drtBoxInnerArmMaximum_ge_one (c : LatticeVertex) (n N : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition (latticeBox c N : Set LatticeVertex))
    (J : (finiteLatticeGraph (latticeBox c N)).edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ)) :
    1 ≤ drtBoxInnerArmMaximum c n N hnN q ξ J β := by
  unfold drtBoxInnerArmMaximum
  rw [← partitionCentredOneArmMaximum_eq]
  exact positiveCentredOneArmMaximum_ge_one _ _ _ n hn (radiusBoxCenter c n) (boxCentredRadius_self c n _)

/-- The comparison keeps every mean under the original outer FK law. -/
theorem drtBoxInnerArmMaximum_le_outer (c : LatticeVertex) (n N : ℕ) (hnN : n ≤ N)
    (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition (latticeBox c N : Set LatticeVertex))
    (J : (finiteLatticeGraph (latticeBox c N)).edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ)) :
    drtBoxInnerArmMaximum c n N hnN q ξ J β ≤ drtBoxOuterArmMaximum c n N hnN q ξ J β := by
  unfold drtBoxInnerArmMaximum partitionCentredOneArmMaximum
  apply Finset.max'_le
  intro y hy
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hy
  apply le_trans _ (Finset.le_max' _ _ (Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩))
  apply Finset.sum_le_sum
  intro j _
  change finitePinnedMean (drtPositiveWeight _ q ξ J β) ∅ ∅ _ ≤ _
  rw [drt_pinnedMean_empty_eq]
  apply drtMean_mono
  intro A
  rw [radiusBoxEdgePartition_projection]
  exact box_centred_one_arm_indicator_le_outer c n N hnN u j A

end
end PottsContinuity.BD12
