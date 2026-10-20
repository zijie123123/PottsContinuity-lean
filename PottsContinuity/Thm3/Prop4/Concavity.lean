module

public import Mathlib.Tactic
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Quantitative subadditivity defect for the Proposition 4 weights

DCST (15 May 2015), TeX line 1783, the concavity inequality in the proof of
Proposition 4. The explicit positive coefficient
1-β is sufficient. This is a real inequality with no probabilistic input.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

private theorem rpow_add_defect_of_le {β x y : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hx : 0 < x) (hxy : x ≤ y) :
    (x + y)^β + (1 - β)*x^β ≤ x^β + y^β := by
  have hy : 0 < y := hx.trans_le hxy
  have hber := rpow_one_add_le_one_add_mul_self
    (show -1 ≤ x / y from le_trans (by norm_num) (div_nonneg hx.le hy.le)) hβ.le hβ1.le
  have hsum : (x + y)^β ≤ y^β + β * (y^(β - 1) * x) := by
    have hid : x + y = y * (1 + x / y) := by field_simp; ring
    calc
      (x + y)^β = y^β * (1 + x / y)^β := by
        rw [hid, Real.mul_rpow hy.le (by positivity)]
      _ ≤ y^β * (1 + β * (x / y)) :=
        mul_le_mul_of_nonneg_left hber (Real.rpow_nonneg hy.le _)
      _ = y^β + β * (y^(β - 1) * x) := by
        rw [Real.rpow_sub hy, Real.rpow_one]
        ring
  have hp : y^(β - 1) * x ≤ x^β := by
    calc
      y^(β - 1) * x ≤ x^(β - 1) * x :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos hx hxy (by linarith only [hβ1])) hx.le
      _ = x^β := by
        rw [← Real.rpow_add_one hx.ne']
        congr 1
        ring
  have := mul_le_mul_of_nonneg_left hp hβ.le
  linarith only [hsum, this]

/-- Quantitative subadditivity: the defect controls a fixed power of the
smaller argument, with coefficient depending only on β. -/
theorem rpow_add_defect {β x y : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hx : 0 < x) (hy : 0 < y) :
    (x + y)^β + (1 - β)*(min x y)^β ≤ x^β + y^β := by
  rcases le_total x y with hxy | hyx
  · simpa only [min_eq_left hxy] using rpow_add_defect_of_le hβ hβ1 hx hxy
  · simpa only [min_eq_right hyx, add_comm] using rpow_add_defect_of_le hβ hβ1 hy hyx

/-- Exact real-inequality graph leaf, with explicit c=1-β. All n≥1 and all
real k,l≥n^ε are retained; the coefficient is independent of ε,n,k,l. -/
theorem concavity_inequality {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (ε n k l : ℝ) (hn : 1 ≤ n) (hk : n^ε ≤ k) (hl : n^ε ≤ l) :
    Real.exp (-(k^β + l^β)) ≤
      Real.exp (-(k+l)^β) * Real.exp (-(1-β)*n^(ε*β)) := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hkpos : 0 < k := (Real.rpow_pos_of_pos hnpos ε).trans_le hk
  have hlpos : 0 < l := (Real.rpow_pos_of_pos hnpos ε).trans_le hl
  have hmin : n^(ε*β) ≤ (min k l)^β := by
    rw [Real.rpow_mul hnpos.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hnpos.le ε) (le_min hk hl) hβ.le
  have hdef := rpow_add_defect hβ hβ1 hkpos hlpos
  have hgain := mul_le_mul_of_nonneg_left hmin (sub_nonneg.mpr hβ1.le)
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith only [hdef, hgain])

end PottsContinuity.Thm3.Prop4
