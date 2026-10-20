module

public import PottsContinuity.PD.Duality.Parameters
public import Mathlib.Tactic

/-! Order reversal of physical dual parameters, independent of threshold claims. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.Duality

/-- Planar FK parameter duality strictly reverses order on the interior interval. -/
theorem dualParameter_lt_of_lt (q p r : ℝ) (hq : 0 < q)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hpr : p < r) :
    dualParameter q r < dualParameter q p := by
  rw [dualParameter, dualParameter, div_lt_div_iff₀
    (dualParameter_den_pos hq hr.1 hr.2) (dualParameter_den_pos hq hp.1 hp.2)]
  have hpos : 0 < q * (r-p) := mul_pos hq (sub_pos.mpr hpr)
  have hid : q*(1-p)*(r+q*(1-r)) - q*(1-r)*(p+q*(1-p)) = q*(r-p) := by ring
  linarith only [hpos,hid]

/-- A parameter strictly below the explicit self-dual point has dual strictly above it. -/
theorem selfDual_lt_dualParameter_of_lt (q : Set.Ici (1 : ℝ)) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hps : p < PD.rcCriticalParameter q) :
    (PD.rcCriticalParameter q : ℝ) < dualParameter q p := by
  have h := dualParameter_lt_of_lt q p (PD.rcCriticalParameter q)
    (lt_of_lt_of_le one_pos q.property) hp (rcCriticalParameter_mem_Ioo q) hps
  rwa [dualParameter_rcCriticalParameter] at h

end PottsContinuity.BD12
