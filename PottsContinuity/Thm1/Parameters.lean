module

public import PottsContinuity.PD.FK.Parameters
public import Mathlib.Tactic

/-! Finite Edwards--Sokal parameter conversion for positive inverse temperature. -/

@[expose] public section

namespace PottsContinuity.Thm1

open PottsContinuity.PD.FK

/-- The FK parameters corresponding to a Potts model with `q ≥ 1` and `β > 0`. -/
noncomputable def pottsESParameters (q : ℕ) (β : ℝ) (hq : 1 ≤ q) (hβ : 0 < β) : Parameters :=
  { val := (q : ℝ)
    property := by exact_mod_cast hq
    edgeProbability := ⟨1 - Real.exp (-β), by
      constructor
      · apply sub_pos.mpr
        rw [Real.exp_lt_one_iff]
        linarith
      · have hpos : 0 < Real.exp (-β) := Real.exp_pos _
        linarith⟩ }

@[simp] theorem pottsESParameters_edgeParameter (q : ℕ) (β : ℝ)
    (hq : 1 ≤ q) (hβ : 0 < β) :
    edgeParameter (pottsESParameters q β hq hβ) = 1 - Real.exp (-β) := rfl

end PottsContinuity.Thm1
