module

public import PottsContinuity.BD12.DRTSourceDenominator
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! DRT's finite wired source differential inequality with its actual partial
sum denominator. All exploration and domain-comparison steps are discharged. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section
open scoped Classical
local instance wiredSourceDiffEdges (n : ℕ) : Fintype (boxGraph (0,0) (2*n)).edgeSet := Fintype.ofFinite _

/-- Actual source one-arm differential inequality for every real q>=1, with
coefficient uniform for 0<beta<=beta_0 and the proved denominator 8*S_n. -/
theorem drt_wired_one_arm_source_differential_inequality
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (β β₀ : Set.Ioi (0 : ℝ))
    (hβ : (β : ℝ) ≤ β₀) (n : ℕ) (hn : 1 ≤ n) :
    let H := boxGraph (0,0) (2*n)
    let J : H.edgeSet → Set.Ioi (0 : ℝ) := fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩
    let ξ := BoundaryCondition.wired (boxVertexBoundary (0,0) (2*n))
    let X := boxOuterOneArmIndicator (0,0) n (2*n)
    let θ := drtWiredOneArmMean q β n
    (((1 / (Real.exp (β₀ : ℝ) - 1)) * (n : ℝ)) / (8 * drtWiredOneArmSum q β n)) * (θ * (1 - θ)) ≤
      deriv (fun t : ℝ => (∑ C, drtWeight H q ξ J t C * X C) / ∑ C, drtWeight H q ξ J t C) β := by
  let ξ := BoundaryCondition.wired (boxVertexBoundary (0,0) (2*n))
  let H := boxGraph (0,0) (2*n)
  let J : H.edgeSet → Set.Ioi (0 : ℝ) := fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩
  let M := drtBoxOuterArmMaximum (0,0) n (2*n) (by omega) q ξ J β
  let a := 1 / (Real.exp (β₀ : ℝ) - 1)
  have ha : 0 ≤ a := div_nonneg zero_le_one (sub_pos.mpr (Real.one_lt_exp_iff.mpr β₀.property)).le
  have hdiff := drt_box_homogeneous_one_arm_differential_inequality (0,0) n (2*n) hn (by omega) q hq ξ β β₀ hβ
  have hM1 : 1 ≤ M := drtBoxOuterArmMaximum_ge_one (0,0) n (2*n) hn (by omega) q ξ J β
  have hM : M ≤ 2 * drtWiredOneArmSum q β n := drtBoxOuterArmMaximum_le_twice_source q hq β (0,0) n
  have hcoef : (a * (n : ℝ)) / (8 * drtWiredOneArmSum q β n) ≤ (a * (n : ℝ)) / (4 * M) :=
    div_le_div_of_nonneg_left (mul_nonneg ha (Nat.cast_nonneg n)) (by linarith only [hM1])
      (by linarith only [hM])
  have hθ := drtWiredOneArmMean_mem_Icc q β n
  exact (mul_le_mul_of_nonneg_right hcoef (mul_nonneg hθ.1 (sub_nonneg.mpr hθ.2))).trans hdiff

end
end PottsContinuity.BD12
