module

public import PottsContinuity.Thm4Records.SourceConnectorSurgery

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Thm4Plane MeasureTheory
noncomputable section

/-- The source connector factor at the explicit self-dual parameter, from
the actual stopping records and their full original source-screen traces. -/
theorem slitScreenConnectorFactor
    (q : Set.Icc (1:ℝ) 4) (m : ℕ) (hm : 1 ≤ m) :
    (1/(1+(q:ℝ)^2)) * (slitScreenFiniteMeasure q m).real
      (slitScreenEvent m ∩ (FKC.FiniteFK.slitScreenLeftCrossingEvent m ∩
        FKC.FiniteFK.slitScreenRightCrossingEvent m)) ≤
      (slitScreenFiniteMeasure q m).real
        ((slitScreenEvent m ∩ (FKC.FiniteFK.slitScreenLeftCrossingEvent m ∩
          FKC.FiniteFK.slitScreenRightCrossingEvent m)) ∩ slitScreenConnectorEvent m) :=
  slitScreenConnectorFactor_of_sourceSurgery q m hm (sourceConnectorSurgery m hm)

end
end PottsContinuity.Thm4Records
