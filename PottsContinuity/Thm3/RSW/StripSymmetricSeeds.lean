module

public import PottsContinuity.Thm3.RSW.StripTranslationInvariant
public import PottsContinuity.Thm3.RSW.StripReflectionInvariant
public import PottsContinuity.Thm3.RSW.StripCanonicalBandSeed
public import PottsContinuity.Thm3.RSW.StripReflectionArm
public import PottsContinuity.Thm3.RSW.ThreeSideWalkExit
public import PottsContinuity.Thm3.RSW.StripBandArm
public import PottsContinuity.Thm3.RSW.StripTranslationArm
public import PottsContinuity.Thm3.RSW.StripEventLimit
public import PottsContinuity.Thm3.RSW.EmbeddedPath
public import PottsContinuity.BD12.TwoBlockConnectivity
public import PottsContinuity.Thm3.RSW.EmbeddedConfinedWalkLift
public import PottsContinuity.Thm3.RSW.StripHorizontalTranslation

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory

theorem selfDual_strip_source_case_split_of_verticalLower
    (q : Set.Ici (1:ℝ)) (k n s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) (hns : n ≤ 9*s)
    (hvertical : (1/2:ℝ) ≤ (selfDualStripMeasure q n).real
      (stripVerticalCrossing n (-(k:ℤ)*n) ((k:ℤ)*n) (2*n))) :
    (1/(36*(k:ℝ)))/3 ≤ (selfDualStripMeasure q n).real
      (stripRectangleArm n 0 (9*s) (2*n) (4*s) (5*s) {v | v.val.2 = 2*n}) ∨
    (1/(36*(k:ℝ)))/3 ≤ (selfDualStripMeasure q n).real
      (stripRectangleArm n 0 (9*s) (2*n) (4*s) (5*s) {v | v.val.1 = 0}) :=
  selfDual_strip_source_case_split_of_stripSymmetries_and_verticalLower q k n s hk hs hns
    (selfDualStripMeasure_horizontalTranslation_invariant q n)
    (selfDualStripMeasure_horizontalReflection_invariant q n (9*s)) hvertical

end PottsContinuity.RSW
