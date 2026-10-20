module

public import PottsContinuity.BD12.BoxRadiusRestriction
public import PottsContinuity.BD12.BoxEdgeOrder
public import PottsContinuity.BD12.DRTInnerDifferential
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.CategoryTheory.Countable
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! The finite-box DRT differential estimate with all metric, partition,
endpoint and first-hit inputs discharged. The law is the full outer-box law. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory PD.FK PD.RCInfinite
noncomputable section
open scoped Classical
local instance boxDiffEdges (c : LatticeVertex) (n : ℕ) :
    Fintype (finiteLatticeGraph (latticeBox c n)).edgeSet := Fintype.ofFinite _
local instance boxDiffEdgeDecidableEq (c : LatticeVertex) (n : ℕ) :
    DecidableEq (finiteLatticeGraph (latticeBox c n)).edgeSet := Classical.decEq _
local instance boxDiffVerticesNonempty (c : LatticeVertex) (n : ℕ) :
    Nonempty (latticeBox c n : Set LatticeVertex) := ⟨radiusBoxCenter c n⟩

/-- The actual origin-to-radius-n observable under the full outer configuration. -/
abbrev boxOuterOneArmIndicator (c : LatticeVertex) (n N : ℕ) :=
  radiusOneArmIndicator (finiteLatticeGraph (latticeBox c N)) (boxGlobalRadius c N) (radiusBoxCenter c N) n

/-- Genuine maximum over inner vertices of restricted centred one-arm sums,
all evaluated under the original outer finite FK law. -/
def drtBoxInnerArmMaximum (c : LatticeVertex) (n N : ℕ) (hnN : n ≤ N)
    (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition (latticeBox c N : Set LatticeVertex))
    (J : (finiteLatticeGraph (latticeBox c N)).edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ)) : ℝ :=
  partitionCentredOneArmMaximum (finiteLatticeGraph (latticeBox c n))
    (radiusBoxEdgePartition c n N hnN) (drtPositiveWeight _ q ξ J β) (boxCentredRadius c n) n

/-- Actual finite-box differential inequality. No geometric, exploration,
revealment, covariance or derivative bound is assumed. The remaining physical
input is a common nonnegative lower bound on the explicit Russo coefficients. -/
theorem drt_box_one_arm_differential_inequality
    (c : LatticeVertex) (n N : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (ξ : BoundaryCondition (latticeBox c N : Set LatticeVertex))
    (J : (finiteLatticeGraph (latticeBox c N)).edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ))
    (a : ℝ) (ha : 0 ≤ a)
    (hcoeff : ∀ b, a ≤ (J b : ℝ) / (Real.exp ((β : ℝ) * (J b : ℝ)) - 1)) :
    let H := finiteLatticeGraph (latticeBox c N)
    let X := boxOuterOneArmIndicator c n N
    let θ := drtMean H q ξ J β X
    ((a * (n : ℝ)) / (4 * drtBoxInnerArmMaximum c n N hnN q ξ J β)) * (θ * (1 - θ)) ≤
      deriv (fun t : ℝ => (∑ C, drtWeight H q ξ J t C * X C) / ∑ C, drtWeight H q ξ J t C) β := by
  let G := finiteLatticeGraph (latticeBox c n)
  let H := finiteLatticeGraph (latticeBox c N)
  let : MeasurableSpace (Configuration G) := ⊤
  let : MeasurableSpace (Option G.edgeSet) := ⊤
  let e := radiusBoxEdgePartition c n N hnN
  let B := finiteRadiusShell (boxGlobalRadius c n) n
  let X := fun C => finiteConnectionToSetIndicator G (radiusBoxCenter c n) B (finitePartitionProjection e C)
  have hX : X = boxOuterOneArmIndicator c n N := by
    funext C
    change radiusOneArmIndicator G (boxGlobalRadius c n) (radiusBoxCenter c n) n
      (finitePartitionProjection e C) = _
    rw [radiusBoxEdgePartition_projection]
    exact (box_radiusOneArmIndicator_eq_restriction c n N hnN C).symm
  have h := drt_inner_connection_differential_inequality G H e (Fintype.equivFin G.edgeSet)
    (boxGlobalRadius c n) (boxCentredRadius c n) (boxGlobalRadius_step c n) n hn
    (boxGlobalRadius_le c n) B (radiusBoxCenter c n) (boxGlobalRadius_center c n)
    (fun b hb => ((mem_finiteRadiusShell _ _ b).mp hb).ge)
    (boxCentredRadius_self c n) (boxCentredRadius_step c n) (boxRadius_difference_le c n)
    (radiusBoxEdgeFirst c n) (radiusBoxEdgeSecond c n) (radiusBoxEdge_endpoints c n)
    q hq ξ J β (fun _ => 0) a ha hcoeff
  change ((a * (n : ℝ)) / (4 * drtBoxInnerArmMaximum c n N hnN q ξ J β)) *
      (drtMean H q ξ J β X * (1 - drtMean H q ξ J β X)) ≤
    deriv (fun t : ℝ => (∑ C, drtWeight H q ξ J t C * X C) / ∑ C, drtWeight H q ξ J t C) β at h
  rw [hX] at h
  exact h

end
end PottsContinuity.BD12
