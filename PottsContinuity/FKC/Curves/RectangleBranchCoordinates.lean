-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/RectangleBranchCoordinates.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RectangleOpenWalkInterpolation
public import PottsContinuity.FKC.Curves.UpperCrosscutWinding
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverBranchRootComparison
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial PottsContinuity.FKC.Curves

noncomputable section

theorem parafermionicCoverBranchRoot_dualFaceCenter_eq
    (n : ℕ) (hn : 1 ≤ n) :
    dualFaceCenter rectangleInterpolationUnitMesh
      (parafermionicCoverBranchRootVertex n hn).val = upperCrosscutBranchCenter := by
  apply Complex.ext
  · norm_num [dualFaceCenter, latticeEmbed, rectangleInterpolationUnitMesh,
      parafermionicCoverBranchRootVertex, upperCrosscutBranchCenter,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  · norm_num [dualFaceCenter, latticeEmbed, rectangleInterpolationUnitMesh,
      parafermionicCoverBranchRootVertex, upperCrosscutBranchCenter,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]

theorem rectangleDualBottomCollarInnerThreeSides_faceCenter_exterior
    (n : ℕ) (z : rectangleDualBottomCollarInnerVertex n)
    (hz : z ∈ rectangleDualBottomCollarInnerThreeSides n) :
    (dualFaceCenter rectangleInterpolationUnitMesh z.val).re < -(n : ℝ) ∨
    (n : ℝ) < (dualFaceCenter rectangleInterpolationUnitMesh z.val).re ∨
    (n : ℝ) < (dualFaceCenter rectangleInterpolationUnitMesh z.val).im := by
  simp only [rectangleDualBottomCollarInnerThreeSides, Set.mem_ofPred_eq] at hz
  norm_num [dualFaceCenter, latticeEmbed, rectangleInterpolationUnitMesh,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  rcases hz with hleft | hright | htop
  · left
    have hreal : (z.val.1 : ℝ) = -(n : ℝ) - 1 := by exact_mod_cast hleft
    rw [hreal]
    linarith
  · right
    left
    have hreal : (z.val.1 : ℝ) = (n : ℝ) := by exact_mod_cast hright
    rw [hreal]
    linarith
  · right
    right
    have hreal : (z.val.2 : ℝ) = (n : ℝ) := by exact_mod_cast htop
    rw [hreal]
    linarith

end
end PottsContinuity.FKC.FiniteFK
