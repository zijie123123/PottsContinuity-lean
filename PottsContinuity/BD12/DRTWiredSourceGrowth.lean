module

public import PottsContinuity.BD12.DRTWiredOneArmUpper
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! DRT's actual finite wired growth inequality, with a strictly positive
coefficient uniform below a fixed positive inverse temperature. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section
open scoped Classical
local instance sourceGrowthEdges (n : ℕ) : Fintype (boxGraph (0,0) (2*n)).edgeSet := Fintype.ofFinite _

/-- The homogeneous coefficient in the source growth estimate. -/
def drtWiredGrowthCoefficient (q : Set.Ioi (0 : ℝ)) (β₀ : Set.Ioi (0 : ℝ)) : ℝ :=
  (1 - drtWiredOneArmMean q β₀ 1) / (8 * (Real.exp (β₀ : ℝ) - 1))

theorem drtWiredGrowthCoefficient_pos (q : Set.Ioi (0 : ℝ)) (β₀ : Set.Ioi (0 : ℝ)) :
    0 < drtWiredGrowthCoefficient q β₀ :=
  div_pos (sub_pos.mpr (drtWiredOneArmMean_lt_one q β₀ 1 le_rfl))
    (mul_pos (by norm_num) (sub_pos.mpr (Real.one_lt_exp_iff.mpr β₀.property)))

/-- Source equation mlem3 for the actual wired one-arm sequence. All finite
probabilistic, domain, and strict-upper-bound steps have been discharged. -/
theorem drt_wired_one_arm_source_growth (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β β₀ : Set.Ioi (0 : ℝ)) (hβ : (β : ℝ) ≤ β₀) (n : ℕ) (hn : 1 ≤ n) :
    let H := boxGraph (0,0) (2*n)
    let J : H.edgeSet → Set.Ioi (0 : ℝ) := fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩
    let ξ := BoundaryCondition.wired (boxVertexBoundary (0,0) (2*n))
    let X := boxOuterOneArmIndicator (0,0) n (2*n)
    (drtWiredGrowthCoefficient q β₀ * (n : ℝ) / drtWiredOneArmSum q β n) * drtWiredOneArmMean q β n ≤
      deriv (fun t : ℝ => (∑ C, drtWeight H q ξ J t C * X C) / ∑ C, drtWeight H q ξ J t C) β := by
  have hdiff := drt_wired_one_arm_source_differential_inequality q hq β β₀ hβ n hn
  have hθ := drtWiredOneArmMean_mem_Icc q β n
  have hu := drtWiredOneArmMean_le_one_scale_upper q hq β β₀ hβ n hn
  have hS : 0 < drtWiredOneArmSum q β n := lt_of_lt_of_le zero_lt_one (drtWiredOneArmSum_ge_one q β n hn)
  have he : 0 < Real.exp (β₀ : ℝ) - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr β₀.property)
  have hp : 0 ≤ ((1 / (Real.exp (β₀ : ℝ) - 1)) * (n : ℝ)) / (8 * drtWiredOneArmSum q β n) :=
    div_nonneg (mul_nonneg (div_nonneg zero_le_one he.le) (Nat.cast_nonneg n)) (by positivity)
  have hprod : drtWiredOneArmMean q β n * (1 - drtWiredOneArmMean q β₀ 1) ≤
      drtWiredOneArmMean q β n * (1 - drtWiredOneArmMean q β n) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left hu 1) hθ.1
  have halg : (drtWiredGrowthCoefficient q β₀ * (n : ℝ) / drtWiredOneArmSum q β n) * drtWiredOneArmMean q β n =
      (((1 / (Real.exp (β₀ : ℝ) - 1)) * (n : ℝ)) / (8 * drtWiredOneArmSum q β n)) *
        (drtWiredOneArmMean q β n * (1 - drtWiredOneArmMean q β₀ 1)) := by
    unfold drtWiredGrowthCoefficient
    field_simp
  rw [halg]
  exact (mul_le_mul_of_nonneg_left hprod hp).trans hdiff

end
end PottsContinuity.BD12
