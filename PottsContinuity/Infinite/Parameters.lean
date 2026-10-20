module

public import PottsContinuity.PD.FK.FrozenBridge
public import Mathlib.Tactic

/-! Source-parameter adapter for the reusable finite and infinite FK library. -/

@[expose] public section

namespace PottsContinuity.Infinite

/-- The common interior-parameter random-cluster model used by the PD library. -/
noncomputable def pdParameters (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ)) :
    PottsContinuity.PD.FK.Parameters :=
  { val := q
    property := hq
    edgeProbability := ⟨p, hp0, hp1⟩ }

theorem pdParameters_toP (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ)) :
    (pdParameters p q hp0 hp1 hq).toP = p := by
  apply Subtype.ext
  rfl

theorem pdParameters_toQ (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ)) :
    (pdParameters p q hp0 hp1 hq).toQ = q := by
  apply Subtype.ext
  rfl

end PottsContinuity.Infinite
