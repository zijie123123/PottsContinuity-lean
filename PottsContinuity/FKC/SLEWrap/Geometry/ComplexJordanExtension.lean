-- Taken from the SLE development in https://github.com/openai/math (commit
-- fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, file `lean/OAI/Probability/SLE/Geometry/ComplexJordanExtension.lean`):
-- module relocated and ported to the module system; the declarations kept are unchanged
-- (the declarations `complexPlaneCoordinates_isArcBetween` and `complex_jordan_extension`, not used
-- here, are omitted).
module

public import Schoenflies.JordanSchoenflies

@[expose] public section

namespace OAI

/-! Complex-coordinate application of the relative Schönflies theorem.
The prescribed boundary homeomorphism is retained pointwise. -/
noncomputable section
open Set

namespace SLEExactGauge

def complexPlaneCoordinates : ℂ ≃ₜ Schoenflies.Plane where
  toFun z := !₂[z.re,z.im]
  invFun v := ⟨v 0,v 1⟩
  left_inv _ := rfl
  right_inv v := by
    ext i
    fin_cases i <;> rfl
  continuous_toFun := by
    apply (PiLp.continuous_toLp _ _).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact Complex.continuous_re
    · exact Complex.continuous_im
  continuous_invFun := by
    have hc : Continuous (fun v : Schoenflies.Plane =>
        (v 0 : ℂ)+(v 1 : ℂ)*Complex.I) := by fun_prop
    convert hc using 1
    funext v
    apply Complex.ext <;> simp

end SLEExactGauge

end

end OAI
