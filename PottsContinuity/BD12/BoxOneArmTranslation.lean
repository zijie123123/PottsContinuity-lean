module

public import PottsContinuity.BD12.OneArmIsomorphism
public import PottsContinuity.BD12.DRTWiredBoxTranslation
public import PottsContinuity.BD12.DRTBoxDifferential
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Translation of the actual centred one-arm observable and its homogeneous
wired finite-box probability. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section

/-- Integer sup-radii are unchanged by simultaneous translation. -/
theorem latticeRadius_translate (a c v : LatticeVertex) :
    latticeRadius (latticeTranslate a c) (latticeTranslate a v) = latticeRadius c v := by
  simp [latticeRadius, latticeTranslate]

/-- Exact pointwise transport on the original finite configuration carrier. -/
theorem boxOuterOneArmIndicator_configurationIso (a c : LatticeVertex) (n N : ℕ)
    (A : Configuration (boxGraph c N)) :
    boxOuterOneArmIndicator (latticeTranslate a c) n N
        (configurationIso (boxVertexTranslationIso a c N) A) = boxOuterOneArmIndicator c n N A := by
  exact radiusOneArmIndicator_configurationIso (boxVertexTranslationIso a c N)
    (boxGlobalRadius c N) (boxGlobalRadius (latticeTranslate a c) N)
    (fun v => latticeRadius_translate a c v.val) (radiusBoxCenter c N) n A

/-- The actual homogeneous wired one-arm mean is independent of the box centre. -/
theorem drtMean_wired_box_one_arm_translation (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β : Set.Ioi (0 : ℝ)) (a c : LatticeVertex) (n N : ℕ) :
    drtMean (boxGraph (latticeTranslate a c) N) q
        (BoundaryCondition.wired (boxVertexBoundary (latticeTranslate a c) N))
        (fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩) β
        (boxOuterOneArmIndicator (latticeTranslate a c) n N) =
      drtMean (boxGraph c N) q (BoundaryCondition.wired (boxVertexBoundary c N))
        (fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩) β (boxOuterOneArmIndicator c n N) := by
  have h := drtMean_wired_box_translation q hq β a c N
    (boxOuterOneArmIndicator (latticeTranslate a c) n N)
  have hf : (fun A => boxOuterOneArmIndicator (latticeTranslate a c) n N
      (configurationIso (boxVertexTranslationIso a c N) A)) = boxOuterOneArmIndicator c n N :=
    funext (boxOuterOneArmIndicator_configurationIso a c n N)
  rw [hf] at h
  exact h

end
end PottsContinuity.BD12
