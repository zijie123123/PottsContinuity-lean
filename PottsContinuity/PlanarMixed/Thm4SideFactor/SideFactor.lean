module

public import PottsContinuity.PlanarMixed.Thm4SideFactor.RightProbabilityFinal
public import PottsContinuity.PlanarMixed.Thm4SideFactor.SideReflectionLaw

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open Thm4Plane FKC.FiniteFK

/-- The source's two side factors, obtained by direct fixed-half-domain conditioning. -/
theorem slitScreen_sideFactor
    (q : ℝ) (hq : q ∈ Set.Icc (1 : ℝ) 4) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ m : ℕ, 1 ≤ m →
      c₂ ^ 2 * (slitScreenFiniteMeasure ⟨q,hq⟩ m).real (slitScreenEvent m) ≤
        (slitScreenFiniteMeasure ⟨q,hq⟩ m).real
          (slitScreenEvent m ∩
            (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m)) :=
  slitScreenSideFactor_of_uniform_right_residual_bound q hq
    (rightResidual_crossing_uniform_pos ⟨q,hq⟩)

end PottsContinuity.PlanarMixed.Thm4SideFactor
