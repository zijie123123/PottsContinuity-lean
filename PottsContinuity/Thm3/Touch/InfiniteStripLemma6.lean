module

public import PottsContinuity.Thm3.Prop4.TouchHalfConsumer
public import PottsContinuity.Thm3.Touch.InfiniteTopEventCylinders
public import PottsContinuity.Thm3.Prop4.TiltedBoundaryLimits
public import Mathlib.MeasureTheory.Measure.Continuity
public import PottsContinuity.Thm3.RSW.TiltedStripWindowReads
public import PottsContinuity.Thm3.RSW.TiltedStripMarginalFiniteWindow
public import PottsContinuity.PlanarMixed.TiltedHalfHeightConsumers.AlmostSureConsumer

@[expose] public section

namespace PottsContinuity.Thm3.Touch

open MeasureTheory
open PD.FK Filter Topology
open PottsContinuity.RSW
open PottsContinuity.Thm3.Prop4
open PottsContinuity.PlanarMixed.TiltedHalfHeightConsumers

noncomputable section

/-- The finite-window law and event-cover inputs needed to turn one bounded
central read into the half-height event of Lemma 6. -/
structure TiltedCentralWindowHalfHeightData (q : Set.Ici (1 : ℝ))
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) where
  k : ℕ
  E : Set (tiltedStripCentralRetainedBond (2*n) t k → Bool)
  ξ : ∀ M : ℕ, BoundaryCondition (tiltedWindow (2*n) M t : Set (ℤ × ℤ))
  topLe : ∀ M, (tiltedWindowBoundary (2*n) M t 0).partition ≤ (ξ M).partition
  lateralBoundary : ∀ M, (ξ M).boundary ⊆ tiltedWindowWiredVertices (2*n) M t 1
  finiteDuality : ∀ᶠ M : ℕ in atTop,
    ∀ F : Set (tiltedStripCentralRetainedBond (2*n) t k → Bool),
      (measure (squareLattice.induce (tiltedWindow (2*n) M t : Set (ℤ × ℤ)))
        (selfDualParameters q) (tiltedWindowBoundary (2*n) M t 0)
        {C | tiltedStripFiniteCentralDualRead (2*n) t k M C ∈ F}).toReal =
      (measure (squareLattice.induce (tiltedWindow (2*n) M t : Set (ℤ × ℤ)))
        (selfDualParameters q) (ξ M)
        {C | tiltedStripFiniteReflectedCentralDualRead (2*n) t k M C ∈ F}).toReal
  cover : ∀ᵐ ω ∂(selfDualTiltedStripMeasure q (2*n) t),
    tiltedStripCentralDualConfiguration (2*n) t k ω ∈ E ∨
      tiltedStripReflectedCentralDualConfiguration (2*n) t k ω ∈ E
  sourceRead_le_halfHeight : ∀ ω : TiltedConfiguration (2*n) t,
    tiltedStripCentralDualConfiguration (2*n) t k ω ∈ E →
      lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n

/-- The counting and isolation comparison of `Thm3.Prop4` turn the infinite-strip
half-height input into the corrected all-slope touching bound. -/
theorem selfDual_tilted_touch_all_slopes_corrected_of_infiniteHalfHeight
    (q : Set.Ici (1 : ℝ)) (n m : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hhalf : ∀ (d : ℕ) (a : ℤ), 1 ≤ d → d ≤ 2*m →
      (a : ℝ)/(d : ℝ) ∈ Set.Icc (-1 : ℝ) 1 →
      (1/2 : ℝ) ≤ (selfDualTiltedStripMeasure q (2*n) ((a : ℝ)/(d : ℝ))).real
        {ω | lowestTopConnectedHeight (2*n) (by omega) ((a : ℝ)/(d : ℝ)) ω 0 ≤ n}) :
    ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(n : ℝ)^2*(m : ℝ)^2) ≤
        tiltedTouchProbability (selfDualParameters q) n m t := by
  exact selfDual_tilted_touch_all_slopes_corrected_of_dualityHalf q n m hn hnm hhalf

end

end PottsContinuity.Thm3.Touch
