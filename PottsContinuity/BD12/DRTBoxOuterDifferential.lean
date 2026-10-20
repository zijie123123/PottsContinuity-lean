module

public import PottsContinuity.BD12.DRTBoxArmMaximum
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Finite-box differential inequality with the full outer centred one-arm
maximum, as required before comparison with translated wired domains. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section
open scoped Classical
local instance boxOuterDiffEdges (c : LatticeVertex) (n : ℕ) :
    Fintype (finiteLatticeGraph (latticeBox c n)).edgeSet := Fintype.ofFinite _
local instance boxOuterDiffEdgeDecidableEq (c : LatticeVertex) (n : ℕ) :
    DecidableEq (finiteLatticeGraph (latticeBox c n)).edgeSet := Classical.decEq _

/-- The outer centred one-arm maximum also contains a probability-one term. -/
theorem drtBoxOuterArmMaximum_ge_one (c : LatticeVertex) (n N : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition (latticeBox c N : Set LatticeVertex))
    (J : (finiteLatticeGraph (latticeBox c N)).edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ)) :
    1 ≤ drtBoxOuterArmMaximum c n N hnN q ξ J β :=
  (drtBoxInnerArmMaximum_ge_one c n N hn hnN q ξ J β).trans
    (drtBoxInnerArmMaximum_le_outer c n N hnN q ξ J β)

/-- The original finite-box one-arm observable takes values in the unit interval. -/
theorem drt_box_one_arm_mean_mem_Icc (c : LatticeVertex) (n N : ℕ)
    (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition (latticeBox c N : Set LatticeVertex))
    (J : (finiteLatticeGraph (latticeBox c N)).edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ)) :
    drtMean (finiteLatticeGraph (latticeBox c N)) q ξ J β (boxOuterOneArmIndicator c n N) ∈
      Set.Icc (0 : ℝ) 1 := by
  let H := finiteLatticeGraph (latticeBox c N)
  have h01 := finiteConnectionToSetIndicator_mem_Icc H (radiusBoxCenter c N)
    (finiteRadiusShell (boxGlobalRadius c N) n)
  have hone : drtMean H q ξ J β (fun _ => 1) = 1 := by
    simp only [drtMean, mul_one]
    exact div_self (drtPartition_pos H q ξ J β).ne'
  exact ⟨drtMean_nonneg H q ξ J β _ (fun A => (h01 A).1),
    (drtMean_mono H q ξ J β _ _ (fun A => (h01 A).2)).trans_eq hone⟩

/-- Actual outer-box differential estimate with its full centred one-arm sums. -/
theorem drt_box_one_arm_outer_differential_inequality
    (c : LatticeVertex) (n N : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (ξ : BoundaryCondition (latticeBox c N : Set LatticeVertex))
    (J : (finiteLatticeGraph (latticeBox c N)).edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ))
    (a : ℝ) (ha : 0 ≤ a)
    (hcoeff : ∀ b, a ≤ (J b : ℝ) / (Real.exp ((β : ℝ) * (J b : ℝ)) - 1)) :
    let H := finiteLatticeGraph (latticeBox c N)
    let X := boxOuterOneArmIndicator c n N
    let θ := drtMean H q ξ J β X
    ((a * (n : ℝ)) / (4 * drtBoxOuterArmMaximum c n N hnN q ξ J β)) * (θ * (1 - θ)) ≤
      deriv (fun t : ℝ => (∑ C, drtWeight H q ξ J t C * X C) / ∑ C, drtWeight H q ξ J t C) β := by
  have h := drt_box_one_arm_differential_inequality c n N hn hnN q hq ξ J β a ha hcoeff
  have hMi := drtBoxInnerArmMaximum_ge_one c n N hn hnN q ξ J β
  have hMo := drtBoxInnerArmMaximum_le_outer c n N hnN q ξ J β
  have hcoef : (a * (n : ℝ)) / (4 * drtBoxOuterArmMaximum c n N hnN q ξ J β) ≤
      (a * (n : ℝ)) / (4 * drtBoxInnerArmMaximum c n N hnN q ξ J β) :=
    div_le_div_of_nonneg_left (mul_nonneg ha (Nat.cast_nonneg n)) (by linarith only [hMi])
      (mul_le_mul_of_nonneg_left hMo (by norm_num))
  have hθ := drt_box_one_arm_mean_mem_Icc c n N q ξ J β
  exact (mul_le_mul_of_nonneg_right hcoef (mul_nonneg hθ.1 (sub_nonneg.mpr hθ.2))).trans h

end
end PottsContinuity.BD12
