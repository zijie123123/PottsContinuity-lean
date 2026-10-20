-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/RectangleBranchPathIntersection.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Curves.RectangleBranchCoordinates
public import PottsContinuity.FKC.Curves.UpperCrosscutSeparation
public import PottsContinuity.FKC.Curves.ClosedDualWalk
public import PottsContinuity.FKC.FiniteFK.RectangleOpenExtension
public import PottsContinuity.FKC.FiniteFK.RectangleOpenWalkInterpolation
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverBranchRootComparison
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Curves PottsContinuity.FKC.Medial
open Set
open unitInterval
noncomputable section

theorem rectangleBranch_primal_dual_walk_intersect
    (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (rectangleGraph (-(n : ℤ), 0) (2 * n) n))
    {u v : RectangleVertex (-(n : ℤ), 0) (2 * n) n}
    (p : (openGraph (rectangleGraph (-(n : ℤ), 0) (2 * n) n) A).Walk u v)
    (huBottom : u.val.2 = 0) (hvBottom : v.val.2 = 0)
    (huLeft : u.val.1 ≤ 0) (hvRight : 1 ≤ v.val.1)
    {z : rectangleDualBottomCollarInnerVertex n}
    (hz : z ∈ rectangleDualBottomCollarInnerThreeSides n)
    (q : (openGraph (rectangleDualBottomCollarInnerGraph n)
      (rectangleDualConfiguration (-(n : ℤ), 0) (2 * n) n A)).Walk
        (parafermionicCoverBranchRootVertex n hn) z) :
    ∃ w, w ∈ Set.range (closedDualWalkPath rectangleInterpolationUnitMesh
        (rectangleOpenOutsideExtension (-(n : ℤ), 0) (2 * n) n A)
        (q.map (rectangleOpenOutsideDualGraphHom (-(n : ℤ), 0) (2 * n) n A))) ∧
      w ∈ Set.range (upperCrosscutClosure
        (latticeWalkPath rectangleInterpolationUnitMesh
          (rectangleOpenOutsideWalkToLatticeWalk A p))) := by
  let primalTop : Path (latticeEmbed rectangleInterpolationUnitMesh u.val)
      (latticeEmbed rectangleInterpolationUnitMesh v.val) :=
    latticeWalkPath rectangleInterpolationUnitMesh
      (rectangleOpenOutsideWalkToLatticeWalk A p)
  let ω := rectangleOpenOutsideExtension (-(n : ℤ), 0) (2 * n) n A
  let qWhole := q.map (rectangleOpenOutsideDualGraphHom (-(n : ℤ), 0) (2 * n) n A)
  have hroot : dualFaceCenter rectangleInterpolationUnitMesh
      (parafermionicCoverBranchRootVertex n hn).val = upperCrosscutBranchCenter :=
    parafermionicCoverBranchRoot_dualFaceCenter_eq n hn
  let rawDualPath := closedDualWalkPath rectangleInterpolationUnitMesh ω qWhole
  let hdualPath : Path upperCrosscutBranchCenter
      (dualFaceCenter rectangleInterpolationUnitMesh z.val) := by
    refine ⟨rawDualPath.toContinuousMap, ?_, ?_⟩
    · have hsrc := rawDualPath.source
      change rawDualPath.toFun 0 = _ at hsrc
      calc
        rawDualPath.toFun 0 = dualFaceCenter rectangleInterpolationUnitMesh
            ((rectangleOpenOutsideDualGraphHom (-(n : ℤ), 0) (2 * n) n A)
              (parafermionicCoverBranchRootVertex n hn)) := hsrc
        _ = dualFaceCenter rectangleInterpolationUnitMesh
            (parafermionicCoverBranchRootVertex n hn).val := rfl
        _ = upperCrosscutBranchCenter := hroot
    · have htgt := rawDualPath.target
      change rawDualPath.toFun 1 = dualFaceCenter rectangleInterpolationUnitMesh z.val at htgt
      exact htgt
  have hdual_eval (t : I) : hdualPath t =
      closedDualWalkPath rectangleInterpolationUnitMesh ω qWhole t := rfl
  have hstart_re : (latticeEmbed rectangleInterpolationUnitMesh u.val).re ≤ 0 := by
    have huR : (u.val.1 : ℝ) ≤ 0 := by exact_mod_cast huLeft
    simpa [latticeEmbed_re, rectangleInterpolationUnitMesh] using huR
  have hend_re : 1 ≤ (latticeEmbed rectangleInterpolationUnitMesh v.val).re := by
    have hvR : (1 : ℝ) ≤ (v.val.1 : ℝ) := by exact_mod_cast hvRight
    simpa [latticeEmbed_re, rectangleInterpolationUnitMesh] using hvR
  have hstart_im : (latticeEmbed rectangleInterpolationUnitMesh u.val).im = 0 := by
    simp [latticeEmbed_im, rectangleInterpolationUnitMesh, huBottom]
  have hend_im : (latticeEmbed rectangleInterpolationUnitMesh v.val).im = 0 := by
    simp [latticeEmbed_im, rectangleInterpolationUnitMesh, hvBottom]
  have htop (t : I) :
      -(n : ℝ) ≤ (primalTop t).re ∧ (primalTop t).re ≤ n ∧
        0 ≤ (primalTop t).im ∧ (primalTop t).im ≤ n := by
    simpa [primalTop] using centeredRectangleOpenOutsideWalkPath_coordinate_bounds n A p t
  have hex := rectangleDualBottomCollarInnerThreeSides_faceCenter_exterior n z hz
  rcases hex with hleft | hright | habove
  · obtain ⟨w, ⟨t, rfl⟩, hcross⟩ :=
      upperCrosscut_path_meets_of_re_lt_left primalTop (n : ℝ)
        (by positivity) hstart_im hend_im hstart_re hend_re htop hdualPath hleft
    refine ⟨hdualPath t, ⟨t, ?_⟩, ?_⟩
    · exact (hdual_eval t).symm
    · simpa [primalTop] using hcross
  · obtain ⟨w, ⟨t, rfl⟩, hcross⟩ :=
      upperCrosscut_path_meets_of_re_gt_right primalTop (n : ℝ)
        (by positivity) hstart_im hend_im hstart_re hend_re htop hdualPath hright
    refine ⟨hdualPath t, ⟨t, ?_⟩, ?_⟩
    · exact (hdual_eval t).symm
    · simpa [primalTop] using hcross
  · obtain ⟨w, ⟨t, rfl⟩, hcross⟩ :=
      upperCrosscut_path_meets_of_im_gt primalTop (n : ℝ)
        (by positivity) hstart_im hend_im hstart_re hend_re htop hdualPath habove
    refine ⟨hdualPath t, ⟨t, ?_⟩, ?_⟩
    · exact (hdual_eval t).symm
    · simpa [primalTop] using hcross


end
end PottsContinuity.FKC.FiniteFK
