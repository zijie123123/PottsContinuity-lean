module

public import PottsContinuity.DualityExt.PositiveP5aAnnulusActualDualJordan
public import PottsContinuity.DualityExt.PositiveAnnulusDualShell
public import PottsContinuity.DualityExt.PositiveConnectedBoundaryPartition
public import PottsContinuity.DualityExt.PositiveEndpointDualSubgraphLaw
public import PottsContinuity.PD.RCInfinite.OpeningPaths
public import PottsContinuity.DualityExt.PositivePDLawBridge

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open MeasureTheory

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance p5aDualLawSourceConfigFintype (N : ℕ) :
    Fintype (Configuration (annulusSourceGraph N)) := Fintype.ofFinite _

local instance p5aDualLawHostConfigFintype (N : ℕ) :
    Fintype (Configuration
      (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))) :=
  Fintype.ofFinite _

local instance p5aDualLawActiveConfigFintype (N : ℕ) :
    Fintype (Configuration (positiveActiveGraph
      (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N)))) :=
  Fintype.ofFinite _

/-- The P5a polygon event on active endpoints of the annulus dual graph. -/
def p5aAnnulusActiveDualJordanEvent (N : ℕ) (hN : 2 ≤ N) :
    Set (Configuration (positiveActiveGraph
      (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N)))) :=
  {A | positiveActiveConfigurationEquiv
      (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N)) A ∈
        p5aAnnulusSourceActualDualJordanEvent N hN}

/-- The exact configuration map from the primal annulus law to active
endpoints of its induced dual graph. -/
noncomputable def annulusPrimalToActiveDualConfigurationEquiv (N : ℕ) :
    Configuration (annulusSourceGraph N) ≃
      Configuration (positiveActiveGraph
        (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))) :=
  (isolatedExtensionConfigurationEquiv (annulusSourceGraph N)
    (annulusSourceEmbedding N)).trans
    ((rectangleSubgraphDualConfigurationEquiv
      (annulusSourceGraph_map_le_host N)).trans
      (positiveActiveConfigurationEquiv
        (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))).symm)

/-- The dual pullback of the P5a event on the primal annulus carrier. -/
def p5aAnnulusPrimalDualJordanEvent (N : ℕ) (hN : 2 ≤ N) :
    Set (Configuration (annulusSourceGraph N)) :=
  (annulusPrimalToActiveDualConfigurationEquiv N) ⁻¹'
    p5aAnnulusActiveDualJordanEvent N hN

end
end PottsContinuity.DualityExt
