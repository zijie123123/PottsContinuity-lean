module

public import PottsContinuity.BD12.OriginalPinBlock
public import PottsContinuity.BD12.ProbabilityKernelIntegral

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section

/-- Average the current original input first, then the remaining block, for
an actual bounded measurable observable of the original stream. -/
theorem finiteOriginalPinBlock_integral_succ (c k : ℕ) (U : ℕ → ℝ)
    (g : (ℕ → ℝ) → ℝ) (hg : Measurable g) (hg01 : ∀ W, g W ∈ Set.Icc (0 : ℝ) 1) :
    (∫ W, g W ∂finiteOriginalPinBlock c (k + 1) U) =
      ∫ u, ∫ W, g W ∂finiteOriginalPinBlock (c + 1) k (Function.update U c u)
        ∂finiteUnitUniform := by
  have hK : Measurable (fun u : ℝ => finiteOriginalPinBlock (c + 1) k (Function.update U c u)) :=
    (finiteOriginalPinBlock_measurable (c + 1) k).comp (measurable_original_stream_update U c)
  rw [finiteOriginalPinBlock]
  exact (probabilityKernel_unit_integral_bind _ _ hK g hg hg01).symm

end
end PottsContinuity.BD12
