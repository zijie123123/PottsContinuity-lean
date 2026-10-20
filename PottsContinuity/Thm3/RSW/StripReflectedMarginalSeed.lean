module

public import PottsContinuity.Thm3.RSW.StripReflectedCentralLawConditional
public import PottsContinuity.Thm3.RSW.StripReflectedPortTransport

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The original primal vertical estimate from the literal reflected finite
marginal alone. All actual port-walk confinement and row clipping are proved. -/
theorem selfDual_stripCentral_vertical_lower_of_reflectedMarginal
    (q : Set.Ici (1:ℝ)) (k n : ℕ) (hn : 1 ≤ n)
    (hlaw : Measure.map (stripCentralDualConfiguration n k) (selfDualStripMeasure q n) =
      Measure.map (stripReflectedCentralDualConfiguration n k hn) (selfDualStripMeasure q n))
    (hsmall : selfDualStripHorizontalProbability q k n < 1/2) :
    (1/2:ℝ) ≤ (selfDualStripMeasure q n).real
      (stripVerticalCrossing n (-(k:ℤ)*n) ((k:ℤ)*n) (2*n)) :=
  selfDual_stripCentral_vertical_lower_of_reflectedDualLaw_and_crossingTransport
    q k n hn hlaw (strip_reflected_dual_port_crossing_subset_shifted_all n k hn) hsmall

end
end PottsContinuity.RSW
