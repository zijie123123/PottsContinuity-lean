module

public import PottsContinuity.Thm3.Push.StripRSWSymmetryBridge
public import PottsContinuity.Thm3.Push.StripTopArmEvent
public import PottsContinuity.Thm3.Push.StripSideArmEvent
public import PottsContinuity.Thm3.RSW.StripCanonicalBandSeed

@[expose] public section

namespace PottsContinuity.Push
open PD.FK MeasureTheory
noncomputable section

/-- The literal source top cylinder is the physical rectangle arm `RSW.stripRectangleArm`. -/
theorem strip_source_top_arm_eq_rectangleArm (n s : ℕ) (hscale : 9*s ≤ 2*n) :
    stripSourceSquareEvent n 0 (sourceSquareTopArmEvent (2*n)
      (4*(s:ℤ)) (5*(s:ℤ)) 0 (9*(s:ℤ))) =
    RSW.stripRectangleArm n 0 (9*s) (2*n) (4*s) (5*s) {v | v.val.2=2*n} := by
  rw [stripSourceTopArmEvent_eq_confined n 0 (4*(s:ℤ)) (5*(s:ℤ)) 0 (9*(s:ℤ))
    (by omega) (by omega)]
  simp only [zero_add,RSW.stripRectangleArm]
  have hA : {w : RSW.stripVertices n | w.val ∈ Set.Icc (4*(s:ℤ)) (5*(s:ℤ)) ×ˢ ({0}:Set ℤ)} =
      {w : RSW.stripVertices n | 4*(s:ℤ) ≤ w.val.1 ∧ w.val.1 ≤ 5*(s:ℤ) ∧ w.val.2=0} := by
    ext w
    simp only [Set.mem_ofPred_eq,Set.mem_prod,Set.mem_Icc,Set.mem_singleton_iff]
    tauto
  rw [hA]

/-- The literal source left cylinder is the physical rectangle arm `RSW.stripRectangleArm`. -/
theorem strip_source_left_arm_eq_rectangleArm (n s : ℕ) (hscale : 9*s ≤ 2*n) :
    stripSourceSquareEvent n 0 (sourceSquareSideArmEvent (2*n)
      (4*(s:ℤ)) (5*(s:ℤ)) 0 (9*(s:ℤ)) 0) =
    RSW.stripRectangleArm n 0 (9*s) (2*n) (4*s) (5*s) {v | v.val.1=0} := by
  rw [stripSourceSideArmEvent_eq_confined n 0 (4*(s:ℤ)) (5*(s:ℤ)) 0 (9*(s:ℤ)) 0
    (by omega) (by omega)]
  simp only [zero_add,RSW.stripRectangleArm]
  have hA : {w : RSW.stripVertices n | w.val ∈ Set.Icc (4*(s:ℤ)) (5*(s:ℤ)) ×ˢ ({0}:Set ℤ)} =
      {w : RSW.stripVertices n | 4*(s:ℤ) ≤ w.val.1 ∧ w.val.1 ≤ 5*(s:ℤ) ∧ w.val.2=0} := by
    ext w
    simp only [Set.mem_ofPred_eq,Set.mem_prod,Set.mem_Icc,Set.mem_singleton_iff]
    tauto
  rw [hA]

/-- The physical source top/left case dichotomy from the reflected-dual
branch's primal vertical bound, with both whole-law symmetries discharged. -/
theorem selfDual_strip_physical_case_split_of_verticalLower
    (q : Set.Ici (1:ℝ)) (k n s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) (hns : n ≤ 9*s)
    (hvertical : (1/2:ℝ) ≤ (RSW.selfDualStripMeasure q n).real
      (RSW.stripVerticalCrossing n (-(k:ℤ)*n) ((k:ℤ)*n) (2*n))) :
    (1/(36*(k:ℝ)))/3 ≤ (RSW.selfDualStripMeasure q n).real
      (RSW.stripRectangleArm n 0 (9*s) (2*n) (4*s) (5*s) {v | v.val.2=2*n}) ∨
    (1/(36*(k:ℝ)))/3 ≤ (RSW.selfDualStripMeasure q n).real
      (RSW.stripRectangleArm n 0 (9*s) (2*n) (4*s) (5*s) {v | v.val.1=0}) := by
  exact RSW.selfDual_strip_source_case_split_of_stripSymmetries_and_verticalLower q k n s hk hs hns
    (fun c => strip_limit_map_RSW_translation (RSW.selfDualParameters q) n _
      (RSW.selfDualStripMeasure_isLimit q n) c)
    (strip_limit_map_RSW_reflection (RSW.selfDualParameters q) n _
      (RSW.selfDualStripMeasure_isLimit q n) (9*s)) hvertical

/-- The source dichotomy is expressed on the exact original source cylinders
used by both proved Case 1 and Case 2 marginal estimates. -/
theorem selfDual_strip_source_case_split_of_verticalLower
    (q : Set.Ici (1:ℝ)) (k n s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s)
    (hns : n ≤ 9*s) (hscale : 9*s ≤ 2*n)
    (hvertical : (1/2:ℝ) ≤ (RSW.selfDualStripMeasure q n).real
      (RSW.stripVerticalCrossing n (-(k:ℤ)*n) ((k:ℤ)*n) (2*n))) :
    (1/(36*(k:ℝ)))/3 ≤ (RSW.selfDualStripMeasure q n).real (stripSourceSquareEvent n 0
      (sourceSquareTopArmEvent (2*n) (4*(s:ℤ)) (5*(s:ℤ)) 0 (9*(s:ℤ)))) ∨
    (1/(36*(k:ℝ)))/3 ≤ (RSW.selfDualStripMeasure q n).real (stripSourceSquareEvent n 0
      (sourceSquareSideArmEvent (2*n) (4*(s:ℤ)) (5*(s:ℤ)) 0 (9*(s:ℤ)) 0)) := by
  rw [strip_source_top_arm_eq_rectangleArm n s hscale,strip_source_left_arm_eq_rectangleArm n s hscale]
  exact selfDual_strip_physical_case_split_of_verticalLower q k n s hk hs hns hvertical

end
end PottsContinuity.Push
