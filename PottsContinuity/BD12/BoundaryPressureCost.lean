module

public import PottsContinuity.BD12.BoundaryComponentCost
public import PottsContinuity.BD12.DRTFiniteLaw
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Uniform surface bounds for actual finite FK partition functions. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK
open scoped BigOperators Classical
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance boundaryPressureEdges : Fintype G.edgeSet := Fintype.ofFinite _

/-- A supported boundary partition costs at most q to the boundary size in
unnormalized weight, uniformly in the positive bond couplings and temperature. -/
theorem drtWeight_boundary_comparison (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (ξ : BoundaryCondition V) (J : G.edgeSet → Set.Ioi (0 : ℝ))
    (β : Set.Ioi (0 : ℝ)) (A : Configuration G) :
    drtWeight G q ξ J β A ≤ drtWeight G q (BoundaryCondition.free ξ.boundary) J β A ∧
    drtWeight G q (BoundaryCondition.free ξ.boundary) J β A ≤
      (q : ℝ) ^ Nat.card ξ.boundary * drtWeight G q ξ J β A := by
  have hp : 0 ≤ ∏ e ∈ A, (Real.exp ((β : ℝ) * (J e : ℝ)) - 1) := by
    apply Finset.prod_nonneg
    intro e _
    exact (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos β.property (J e).property))).le
  constructor
  · exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hq (componentCount_boundary_le_free G ξ A)) hp
  · have h := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hq (componentCount_free_le_boundary_add G ξ A)) hp
    simpa only [drtWeight, pow_add, mul_assoc, mul_left_comm, mul_comm] using h

/-- The same comparison for the genuine partition functions. -/
theorem drtPartition_boundary_comparison (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (ξ : BoundaryCondition V) (J : G.edgeSet → Set.Ioi (0 : ℝ))
    (β : Set.Ioi (0 : ℝ)) :
    (∑ A, drtWeight G q ξ J β A) ≤
      ∑ A, drtWeight G q (BoundaryCondition.free ξ.boundary) J β A ∧
    (∑ A, drtWeight G q (BoundaryCondition.free ξ.boundary) J β A) ≤
      (q : ℝ) ^ Nat.card ξ.boundary * ∑ A, drtWeight G q ξ J β A := by
  constructor
  · exact Finset.sum_le_sum (fun A _ => (drtWeight_boundary_comparison G q hq ξ J β A).1)
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun A _ => (drtWeight_boundary_comparison G q hq ξ J β A).2)

/-- The free-minus-wired log partition error lies between zero and the
boundary size times log q. This is a finite-volume statement without a limit premise. -/
theorem drtLogPartition_boundary_cost (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (ξ : BoundaryCondition V) (J : G.edgeSet → Set.Ioi (0 : ℝ))
    (β : Set.Ioi (0 : ℝ)) :
    0 ≤ Real.log (∑ A, drtWeight G q (BoundaryCondition.free ξ.boundary) J β A) -
      Real.log (∑ A, drtWeight G q ξ J β A) ∧
    Real.log (∑ A, drtWeight G q (BoundaryCondition.free ξ.boundary) J β A) -
      Real.log (∑ A, drtWeight G q ξ J β A) ≤
        (Nat.card ξ.boundary : ℝ) * Real.log q := by
  obtain ⟨hl,hu⟩ := drtPartition_boundary_comparison G q hq ξ J β
  have hw := drtPartition_pos G q ξ J β
  have hf := drtPartition_pos G q (BoundaryCondition.free ξ.boundary) J β
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log hw hl)
  · have h := Real.log_le_log hf hu
    rw [Real.log_mul (pow_pos q.property _).ne' hw.ne', Real.log_pow] at h
    linarith only [h]

end
end PottsContinuity.BD12
