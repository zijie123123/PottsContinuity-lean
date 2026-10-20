module

public import PottsContinuity.PlanarMixed.FiniteSlit.CrosscutBand
public import PottsContinuity.PlanarMixed.EmbeddedActiveLaw

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK BD12 MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

namespace CrosscutData
variable {M : ℕ} {x y : ℤ} (D : CrosscutData M x y) (hM : 2 ≤ M) (hy : 0 < y)
local notation "r" => D.rank hM hy
local notation "GΩ" => rankedBandGraph (graph M x y) r

/-- The original bottom start is a vertex of the first marked band arc. -/
def firstStartBand : rankedBandVertices r :=
  ⟨D.firstStart,by
    have hh := (D.rank_first_iff hM hy D.firstStart).mpr D.first.start_mem_support
    change 1 ≤ r D.firstStart ∧ r D.firstStart ≤ 3
    omega⟩

/-- The later bottom start is a vertex of the second marked band arc. -/
def secondStartBand : rankedBandVertices r :=
  ⟨D.secondStart,by
    have hh := (D.rank_second_iff hM hy D.secondStart).mpr D.second.start_mem_support
    change 1 ≤ r D.secondStart ∧ r D.secondStart ≤ 3
    omega⟩

/-- Both wired arcs are nonempty, witnessed by their actual bottom roots. -/
theorem arcs_nonempty : (rankedBandFirstArc r).Nonempty ∧ (rankedBandSecondArc r).Nonempty := by
  constructor
  · exact ⟨D.firstStartBand hM hy,
      (D.rank_first_iff hM hy D.firstStart).mpr D.first.start_mem_support⟩
  · exact ⟨D.secondStartBand hM hy,
      (D.rank_second_iff hM hy D.secondStart).mpr D.second.start_mem_support⟩

end CrosscutData
end
end PottsContinuity.PlanarMixed.FiniteSlit
