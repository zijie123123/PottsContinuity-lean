module

public import PottsContinuity.BD12.OriginalPinBlockTower
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Exact decomposition of an original uniform block into consecutive prefix
and suffix blocks. This is the prefix conditioning used for revealments. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section

/-- Resampling adjacent original-input blocks once is the law of resampling
their concatenation once. Coordinates outside the concatenation are retained. -/
theorem finiteOriginalPinBlock_bind_add (c k l : ℕ) (U : ℕ → ℝ) :
    (finiteOriginalPinBlock c k U).bind (finiteOriginalPinBlock (c + k) l) =
      finiteOriginalPinBlock c (k + l) U := by
  induction k generalizing c U with
  | zero =>
    simp only [finiteOriginalPinBlock, Nat.add_zero, Nat.zero_add]
    exact Measure.dirac_bind (finiteOriginalPinBlock_measurable c l) U
  | succ k ih =>
    have hK : Measurable (fun u : ℝ => finiteOriginalPinBlock (c + 1) k (Function.update U c u)) :=
      (finiteOriginalPinBlock_measurable (c + 1) k).comp (measurable_original_stream_update U c)
    rw [finiteOriginalPinBlock, Measure.bind_bind hK.aemeasurable
      (finiteOriginalPinBlock_measurable (c + (k + 1)) l).aemeasurable]
    have hindex : c + (k + 1) = (c + 1) + k := by omega
    simp_rw [hindex, ih]
    rw [show k + 1 + l = (k + l) + 1 by omega]
    rfl

/-- Integrate a bounded observable by averaging the original prefix and then
the independent remaining original inputs. -/
theorem finiteOriginalPinBlock_integral_split (c k l : ℕ) (U : ℕ → ℝ)
    (g : (ℕ → ℝ) → ℝ) (hg : Measurable g) (hg01 : ∀ W, g W ∈ Set.Icc (0 : ℝ) 1) :
    (∫ W, ∫ Z, g Z ∂finiteOriginalPinBlock (c + k) l W ∂finiteOriginalPinBlock c k U) =
      ∫ Z, g Z ∂finiteOriginalPinBlock c (k + l) U := by
  rw [probabilityKernel_unit_integral_bind _ _ (finiteOriginalPinBlock_measurable (c + k) l) g hg hg01,
    finiteOriginalPinBlock_bind_add]

end
end PottsContinuity.BD12
