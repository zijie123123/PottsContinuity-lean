module

public import PottsContinuity.Thm4Plane.ScreenFactorAssembly
public import PottsContinuity.Thm3.RSW.StoppingAverage
public import PottsContinuity.PlanarMixed.OmegaConditional
public import PottsContinuity.PD.FK.RemainingComparison
public import Mathlib.Tactic
public import PottsContinuity.PlanarMixed.SourceActiveCrosscutComparison
public import PottsContinuity.PlanarMixed.SourceCrosscutShapes
public import PottsContinuity.PlanarMixed.Square.Consumers

@[expose] public section

namespace PottsContinuity.Thm4Plane

open MeasureTheory
open PottsContinuity.PD.FK
open PottsContinuity.BD12
open PottsContinuity.Exploration
open PottsContinuity.RSW
open PottsContinuity.PlanarMixed

noncomputable section

attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

local instance screenMixedEdgeDecidableEq (m : ℕ) :
    DecidableEq (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m)).edgeSet :=
  Classical.decEq _

local instance screenMixedConfigurationMeasurableSpace (m : ℕ) :
    MeasurableSpace (Configuration
      (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))) :=
  PottsContinuity.PD.FK.configurationMeasurableSpace _

def slitScreenRStarBase (m : ℕ) : LatticeVertex :=
  (-(5 * (m : ℤ)), -(12 * (m : ℤ)))

def slitScreenRStarSide (m : ℕ) : ℕ := 10 * m - 1

end
end PottsContinuity.Thm4Plane
