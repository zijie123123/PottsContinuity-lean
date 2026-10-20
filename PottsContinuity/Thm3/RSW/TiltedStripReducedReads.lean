module

public import PottsContinuity.Thm3.RSW.TiltedStripReducedCarrier

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial Thm3.Prop4 MeasureTheory
noncomputable section

/-- Read the states of precisely the retained original strip bonds. -/
def tiltedStripReducedRestriction (N : ℕ) (t : ℝ)
    (ω : TiltedConfiguration N t) : tiltedStripReducedCarrier N t → Bool :=
  fun b => ω (tiltedBondEdge N t b.val)

/-- Actual complementary dual transport on the reduced original bond labels. -/
def tiltedStripReducedDualTransport (N : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (ω : tiltedStripReducedCarrier N t → Bool) : tiltedStripReducedCarrier N t → Bool :=
  fun b => !(ω (tiltedStripReducedBondEquiv N t ht b))

theorem tiltedStripReducedRestriction_continuous (N : ℕ) (t : ℝ) :
    Continuous (tiltedStripReducedRestriction N t) :=
  continuous_pi fun b => continuous_apply (tiltedBondEdge N t b.val)

theorem tiltedStripReducedDualTransport_continuous (N : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    Continuous (tiltedStripReducedDualTransport N t ht) :=
  continuous_pi fun b => (continuous_of_discreteTopology : Continuous Bool.not).comp
    (continuous_apply (tiltedStripReducedBondEquiv N t ht b))

end
end PottsContinuity.RSW
