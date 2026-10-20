module

public import PottsContinuity.Thm4Records.SideRectangleRead
public import PottsContinuity.Thm4Records.ActualResidualConsumer

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Exploration Push RSW Thm4Plane MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance actualSourceRecordsEdgeEq (m : ℕ) :
    DecidableEq (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet := Classical.decEq _

/-- The original E and both F events are read by the concrete common reveal. -/
theorem connectorSourceEvent_readFrom_connectorReveal (m : ℕ) (hm : 1 ≤ m) :
    ReadFromReveal (connectorReveal m hm) (connectorSourceEvent m) :=
  connectorSourceEvent_readFrom_connectorReveal_of_primalDualAlternatives m hm
    (sidePrimalDualAlternative m hm false) (sidePrimalDualAlternative m hm true)

/-- The sole remaining obligation is original-bond geometry on the common
record fibre. It contains no law, partition or probability hypothesis. -/
def SourceConnectorSurgery (m : ℕ) (hm : 1 ≤ m) : Prop :=
  ∀ X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)), X ∈ connectorSourceEvent m →
    ∀ Y ∈ revealRecordEvent (connectorReveal m hm) X,
      (configurationSplitEquiv _ (connectorReveal m hm X) Y).1 ∈
        connectorRemainingNoncrossing m hm X → Y ∈ slitScreenConnectorEvent m

/-- The corrected consumer now has only its explicit full-trace surgery premise.
All records, laws, selections and quantitative bounds are already constructed. -/
theorem slitScreenConnectorFactor_of_sourceSurgery
    (q : Set.Icc (1:ℝ) 4) (m : ℕ) (hm : 1 ≤ m)
    (hsurgery : SourceConnectorSurgery m hm) :
    (1/(1+(q:ℝ)^2)) * (slitScreenFiniteMeasure q m).real
      (slitScreenEvent m ∩ (FKC.FiniteFK.slitScreenLeftCrossingEvent m ∩
        FKC.FiniteFK.slitScreenRightCrossingEvent m)) ≤
      (slitScreenFiniteMeasure q m).real
        ((slitScreenEvent m ∩ (FKC.FiniteFK.slitScreenLeftCrossingEvent m ∩
          FKC.FiniteFK.slitScreenRightCrossingEvent m)) ∩ slitScreenConnectorEvent m) :=
  slitScreenConnectorFactor_of_residual_geometry q m hm
    ⟨sidePrimalDualAlternative m hm false,sidePrimalDualAlternative m hm true,hsurgery⟩

end
end PottsContinuity.Thm4Records
