module

public import PottsContinuity.BD12.DRTBoxOuterDifferential
public import PottsContinuity.BD12.DRTHomogeneousParameters
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Homogeneous finite-box differential inequality with a positive coefficient
uniform on a bounded inverse-temperature interval. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section
open scoped Classical
local instance boxHomoEdges (c : LatticeVertex) (n : ℕ) :
    Fintype (finiteLatticeGraph (latticeBox c n)).edgeSet := Fintype.ofFinite _
local instance boxHomoEdgeDecidableEq (c : LatticeVertex) (n : ℕ) :
    DecidableEq (finiteLatticeGraph (latticeBox c n)).edgeSet := Classical.decEq _

/-- The lower Russo coefficient for unit coupling is uniform up to beta_0. -/
theorem drt_homogeneous_coefficient_lower_bound (β β₀ : Set.Ioi (0 : ℝ))
    (hβ : (β : ℝ) ≤ β₀) :
    1 / (Real.exp (β₀ : ℝ) - 1) ≤ 1 / (Real.exp (β : ℝ) - 1) :=
  div_le_div_of_nonneg_left zero_le_one
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr β.property))
    (sub_le_sub_right (Real.exp_le_exp.mpr hβ) 1)

/-- The full outer-box homogeneous one-arm estimate. All finite graph and
exploration premises and the physical coefficient comparison are proved. -/
theorem drt_box_homogeneous_one_arm_differential_inequality
    (c : LatticeVertex) (n N : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (ξ : BoundaryCondition (latticeBox c N : Set LatticeVertex))
    (β β₀ : Set.Ioi (0 : ℝ)) (hβ : (β : ℝ) ≤ β₀) :
    let H := finiteLatticeGraph (latticeBox c N)
    let J : H.edgeSet → Set.Ioi (0 : ℝ) := fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩
    let X := boxOuterOneArmIndicator c n N
    let θ := drtMean H q ξ J β X
    (((1 / (Real.exp (β₀ : ℝ) - 1)) * (n : ℝ)) /
        (4 * drtBoxOuterArmMaximum c n N hnN q ξ J β)) * (θ * (1 - θ)) ≤
      deriv (fun t : ℝ => (∑ C, drtWeight H q ξ J t C * X C) / ∑ C, drtWeight H q ξ J t C) β := by
  apply drt_box_one_arm_outer_differential_inequality c n N hn hnN q hq ξ _ β
    (1 / (Real.exp (β₀ : ℝ) - 1))
    (div_nonneg zero_le_one (sub_pos.mpr (Real.one_lt_exp_iff.mpr β₀.property)).le)
  intro b
  simpa only [mul_one] using drt_homogeneous_coefficient_lower_bound β β₀ hβ

end
end PottsContinuity.BD12
