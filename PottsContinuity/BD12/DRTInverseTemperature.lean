module

public import PottsContinuity.BD12.DRTHomogeneousParameters
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

/-! Explicit inverse of the homogeneous physical probability map on every
interior FK parameter record. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK
noncomputable section

/-- The unique positive inverse temperature corresponding to the stored edge probability. -/
def drtInverseTemperature (θ : Parameters) : Set.Ioi (0 : ℝ) :=
  ⟨-Real.log (1 - edgeParameter θ), neg_pos.mpr
    (Real.log_neg (one_sub_edgeParameter_pos θ) (sub_lt_self _ (edgeParameter_pos θ)))⟩

/-- The physical map of the inverse temperature is the original edge probability. -/
theorem drtInverseTemperature_physical (θ : Parameters) :
    1 - Real.exp (-(drtInverseTemperature θ : ℝ)) = edgeParameter θ := by
  change 1 - Real.exp (-(-Real.log (1 - edgeParameter θ))) = edgeParameter θ
  rw [neg_neg,Real.exp_log (one_sub_edgeParameter_pos θ)]
  ring

/-- The entire parameter record is recovered, including its cluster weight. -/
theorem drtHomogeneousParameters_inverse (θ : Parameters) :
    drtHomogeneousParameters ⟨θ.val,clusterWeight_pos θ⟩ θ.property (drtInverseTemperature θ) = θ := by
  have hp := drtInverseTemperature_physical θ
  cases θ with
  | mk v hv p =>
    change Parameters.mk v hv _ = Parameters.mk v hv p
    congr 1
    apply Subtype.ext
    exact hp

end
end PottsContinuity.BD12
