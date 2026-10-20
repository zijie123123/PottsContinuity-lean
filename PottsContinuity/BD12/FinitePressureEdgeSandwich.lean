module

public import PottsContinuity.BD12.BoundaryPressureCost
public import PottsContinuity.BD12.DRTLogActivity
public import PottsContinuity.BD12.PressureDerivativeSandwich
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! A cross-parameter edge-count comparison with the actual FK surface error. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)

/-- At separated log activities, the free expected edge count dominates every
supported boundary law up to the explicit surface error. -/
theorem drtActivityEdgeSum_boundary_le_free_larger_activity
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (ξ : BoundaryCondition V)
    (s t : ℝ) (hst : s < t) :
    drtActivityEdgeSum G q ξ s ≤
      drtActivityEdgeSum G q (BoundaryCondition.free ξ.boundary) t +
        (Nat.card ξ.boundary : ℝ) * Real.log q / (t-s) := by
  apply pressure_derivative_sandwich
    (drtActivityLogPartition G q ξ)
    (drtActivityLogPartition G q (BoundaryCondition.free ξ.boundary))
    (drtActivityEdgeSum G q ξ)
    (drtActivityEdgeSum G q (BoundaryCondition.free ξ.boundary))
    ((Nat.card ξ.boundary : ℝ) * Real.log q)
    (drtActivityLogPartition_hasDerivAt G q ξ)
    (drtActivityLogPartition_hasDerivAt G q (BoundaryCondition.free ξ.boundary))
    (drtActivityEdgeSum_monotone G q hq ξ)
    (drtActivityEdgeSum_monotone G q hq (BoundaryCondition.free ξ.boundary))
    _ s t hst
  intro x
  exact drtLogPartition_boundary_cost G q hq ξ
    (fun _ => ⟨(1 : ℝ), (show (0 : ℝ) < 1 from one_pos)⟩)
    (drtLogActivityTemperature x)

end
end PottsContinuity.BD12
