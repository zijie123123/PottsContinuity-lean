module

public import PottsContinuity.DualityExt.PositiveP5aAnnulusFit
public import PottsContinuity.Thm3.Easy.P5FourFrameConditional
public import PottsContinuity.Thm3.RSW.FiniteBoundary

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open MeasureTheory

noncomputable section

local instance p5aJordanSourceConfigFintype (N : ℕ) :
    Fintype (Configuration (p5aAnnulusFaceGraph N)) := Fintype.ofFinite _

local instance p5aJordanHostConfigFintype (N : ℕ) :
    Fintype (Configuration
      (rectangleDualGraph (p5aAnnulusHostAnchor N) (4 * N) (4 * N))) :=
  Fintype.ofFinite _

/-- The source and face-base definitions of the P5a annulus use the same
finite vertex set. -/
theorem p5aAnnulusVertexSet_eq_source (n : ℕ) :
    PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet n =
      p5aAnnulusVertexSet n := by
  ext v
  simp [PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet,
    p5aAnnulusVertexSet, PottsContinuity.PD.FK.latticeBox,
    PottsContinuity.box]

end
end PottsContinuity.DualityExt
