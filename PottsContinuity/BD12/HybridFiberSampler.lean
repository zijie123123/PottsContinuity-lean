module

public import PottsContinuity.BD12.StoppingDetermination
public import PottsContinuity.BD12.AugmentedUniformTree

/-! The stopped-hybrid fiber algorithm from DRT, conditional on a prescribed
initial segment of the original U inputs. Its output law is proved pointwise
in the fixed segment; identification on one joint (U,V) space is separate. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
open scoped Classical
noncomputable section

/-- Before the cutoff the original input is fixed; afterwards its unused
partner is a fresh independent uniform, whichever input drives the hybrid. -/
def finiteHybridAuxLaw (cutoff : ℕ) (fixedU : ℕ → ℝ) (i : ℕ) : Measure ℝ :=
  if i < cutoff then Measure.dirac (fixedU i) else finiteUnitUniform

instance finiteHybridAuxLaw_isProbabilityMeasure (cutoff : ℕ) (fixedU : ℕ → ℝ) (i : ℕ) :
    IsProbabilityMeasure (finiteHybridAuxLaw cutoff fixedU i) := by
  unfold finiteHybridAuxLaw
  split_ifs <;> infer_instance

variable {E : Type*} [Fintype E] [DecidableEq E]

end
end PottsContinuity.BD12
