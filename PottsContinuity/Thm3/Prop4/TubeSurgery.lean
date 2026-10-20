module

public import PottsContinuity.Thm3.Prop4.TubeCut
public import PottsContinuity.Thm3.Prop4.ClosingImage

/-!
# The actual tube cut and its finite-energy surgery cost

All configurations and boundary conditions live on the original finite box.
The event may be arbitrary: closing the cut is treated by its image, not by
assuming that the original connection event survives edge closing.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

noncomputable section

local instance tubeSurgeryEdgeFintype (n : ℕ) :
    Fintype (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet := Fintype.ofFinite _

local instance tubeSurgeryEdgeDecidableEq (n : ℕ) :
    DecidableEq (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet := Classical.decEq _

/-- Uniform positive cost coefficient, depending only on the FK parameters. -/
def tubeClosingCoefficient (θ : PD.FK.Parameters) : ℝ :=
  -9*Real.log (1-PD.FK.edgeParameter θ)

theorem tubeClosingCoefficient_pos (θ : PD.FK.Parameters) :
    0 < tubeClosingCoefficient θ := by
  have hlog := Real.log_neg (PD.FK.one_sub_edgeParameter_pos θ)
    (show 1-PD.FK.edgeParameter θ < 1 by linarith only [PD.FK.edgeParameter_pos θ])
  unfold tubeClosingCoefficient
  linarith only [hlog]

end

end PottsContinuity.Thm3.Prop4
