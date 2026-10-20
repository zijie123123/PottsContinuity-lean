module

public import PottsContinuity.Thm3.Touch.ReducedCarrierLemma6
public import PottsContinuity.Thm3.Prop4.TiltedConnectionEvents
public import PottsContinuity.Thm3.RSW.TiltedStripReducedReads
public import PottsContinuity.PlanarMixed.TiltedHalfHeight.TopErasure
public import PottsContinuity.PlanarMixed.TiltedHalfHeight.HalfHeight

@[expose] public section

namespace PottsContinuity.Thm3.Touch
open PottsContinuity.RSW
open PottsContinuity.Thm3.Prop4
open PottsContinuity.PlanarMixed.TiltedHalfHeight
open MeasureTheory
noncomputable section

/-- The reduced-carrier half-height theorem
`PlanarMixed.TiltedHalfHeight.selfDualTiltedHalfHeight_ge_half` composes with the counting
chain of Lemma 6, leaving only the matching reduced marginal identity as input. -/
theorem selfDual_tilted_touch_all_slopes_corrected_of_reducedMarginal
    (q : Set.Ici (1 : ℝ)) (n m : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hmarginal : ∀ (s : ℝ) (hs : s ∈ Set.Icc (-1 : ℝ) 1),
      Measure.map (tiltedStripReducedDualTransport (2*n) s hs)
        (Measure.map (tiltedStripReducedRestriction (2*n) s)
          (selfDualTiltedStripMeasure q (2*n) s)) =
        Measure.map (tiltedStripReducedRestriction (2*n) s)
          (selfDualTiltedStripMeasure q (2*n) s)) :
    ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(n : ℝ)^2*(m : ℝ)^2) ≤
        tiltedTouchProbability (selfDualParameters q) n m t := by
  apply selfDual_tilted_touch_all_slopes_corrected_of_infiniteHalfHeight q n m hn hnm
  intro d a hd hdm hs
  exact PottsContinuity.PlanarMixed.TiltedHalfHeight.selfDualTiltedHalfHeight_ge_half
    q n hn hmarginal ((a : ℝ)/(d : ℝ)) hs

end
end PottsContinuity.Thm3.Touch
