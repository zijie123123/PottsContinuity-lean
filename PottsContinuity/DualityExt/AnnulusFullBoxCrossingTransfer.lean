module

public import PottsContinuity.DualityExt.PositiveP5aAnnulusActualDualLaw
public import PottsContinuity.DualityExt.PositiveP5aAnnulusNoOpenCrossing

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open MeasureTheory

noncomputable section

local instance annulusFullBoxTransferConfigFintype (N : ℕ) :
    Fintype (Configuration (annulusSourceGraph N)) := Fintype.ofFinite _

/-- An actual open connection on the finite annulus carrier from the full
inner box to its outer boundary. -/
def annulusSourceFullBoxCrossingEvent (N : ℕ) :
    Set (Configuration (annulusSourceGraph N)) :=
  {C | ∃ u v : {x : LatticeVertex // x ∈ annulusVertexSet N},
      u.1 ∈ latticeBox (0, 0) N ∧
      v.1 ∈ annulusOuterBoundary (2 * N) ∧
      ActualConnected (annulusSourceGraph N) C u v}

/-- The source P5a dual Jordan event excludes every actual connection from
the full inner box of the finite annulus to its outer perimeter. -/
theorem p5aAnnulusPrimalDualJordanEvent_subset_noFullBoxCrossing
    (N : ℕ) (hN : 4 ≤ N)
    (C : Configuration (annulusSourceGraph N)) :
    C ∈ p5aAnnulusPrimalDualJordanEvent N (by omega) →
      C ∈ (annulusSourceFullBoxCrossingEvent N)ᶜ := by
  intro hJordan hCross
  rcases hCross with ⟨u, v, hu, hv, hconnected⟩
  obtain ⟨p⟩ := (actualConnected_iff_walk _ _ _ _).mp hconnected
  have hA : rectangleSubgraphDualConfigurationEquiv
      (annulusSourceGraph_map_le_host N)
      (isolatedExtensionConfigurationEquiv (annulusSourceGraph N)
        (annulusSourceEmbedding N) C) ∈
      p5aAnnulusSourceActualDualJordanEvent N (by omega) := by
    simpa [p5aAnnulusPrimalDualJordanEvent,
      annulusPrimalToActiveDualConfigurationEquiv,
      p5aAnnulusActiveDualJordanEvent] using hJordan
  exact p5aAnnulusSourceActualDualJordan_no_openCrossing
    N (by omega) C u v hu hv p hA

end

end PottsContinuity.DualityExt
