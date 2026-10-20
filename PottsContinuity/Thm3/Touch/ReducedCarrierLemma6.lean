module

public import PottsContinuity.Thm3.Touch.InfiniteStripLemma6
public import PottsContinuity.PlanarMixed.TiltedHalfHeight.TopErasure
public import PottsContinuity.PlanarMixed.TiltedHalfHeightConsumers.ProbabilityConsumer
public import PottsContinuity.Thm3.RSW.TiltedStripReducedCarrier

@[expose] public section

namespace PottsContinuity.Thm3.Touch

open MeasureTheory
open PottsContinuity.PD.FK
open PottsContinuity.RSW
open PottsContinuity.Thm3.Prop4
open PottsContinuity.PlanarMixed.TiltedHalfHeight
open PottsContinuity.PlanarMixed.TiltedHalfHeightConsumers

noncomputable section

attribute [local instance] PottsContinuity.PD.FK.configurationMeasurableSpace

abbrev TiltedReducedCarrierConfiguration (N : ℕ) (t : ℝ) :=
  tiltedStripReducedCarrier N t → Bool

/-- Restrict an original strip sample to the carrier with the wired top
class contracted. -/
def tiltedReducedCarrierRead (N : ℕ) (t : ℝ)
    (ω : TiltedConfiguration N t) : TiltedReducedCarrierConfiguration N t :=
  fun b => ω (tiltedBondEdge N t b.val)

/-- The inputs needed at one slope to use the dual symmetry on the
contracted top carrier. The event factorization records that deleting
top-top bonds leaves the actual lowest-height observable unchanged. -/
structure TiltedReducedCarrierHalfHeightData
    (q : Set.Ici (1 : ℝ)) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) where
  reflected : TiltedReducedCarrierConfiguration (2*n) t →
    TiltedReducedCarrierConfiguration (2*n) t
  reflectedMeasurable : Measurable reflected
  event : Set (TiltedReducedCarrierConfiguration (2*n) t)
  eventMeasurable : MeasurableSet event
  sourceFactor : ∀ ω : TiltedConfiguration (2*n) t,
    (lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n) ↔
      tiltedReducedCarrierRead (2*n) t ω ∈ event
  cover : ∀ᵐ ω ∂(selfDualTiltedStripMeasure q (2*n) t),
    tiltedReducedCarrierRead (2*n) t ω ∈ event ∨
      reflected (tiltedReducedCarrierRead (2*n) t ω) ∈ event
  invariantLaw :
    ((selfDualTiltedStripMeasure q (2*n) t).map
      (tiltedReducedCarrierRead (2*n) t)).map reflected =
      (selfDualTiltedStripMeasure q (2*n) t).map
        (tiltedReducedCarrierRead (2*n) t)

end

end PottsContinuity.Thm3.Touch
