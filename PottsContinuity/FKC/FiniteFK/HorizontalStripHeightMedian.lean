-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripHeightMedian.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripFiniteHeightProbabilityAlternative
public import PottsContinuity.FKC.FiniteFK.HorizontalStripCoreSeedBoundaryComparison
public import PottsContinuity.FKC.FiniteFK.HorizontalStripFiniteHeightEventTransport
public import PottsContinuity.FKC.FiniteFK.HorizontalStripAsymmetricBoundaryProbabilityBound
public import PottsContinuity.FKC.FiniteFK.HorizontalStripHeightLimitEstimates
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.FKC.Medial
open PottsContinuity.FKC.FiniteFK
noncomputable section

/-- The unchanged original whole-strip height event has probability at least
one half under the canonical fixed-height top-wired limit. -/
theorem horizontalStripCanonicalHeight_probability_ge_half
    (q : PottsContinuity.FKC.ClusterWeight) (n : ℕ) :
    (((Classical.choose
      (horizontalStripTopWiredProbabilityMeasures_existsUnique_limit q n) :
        ProbabilityMeasure LatticeConfiguration) : Measure LatticeConfiguration)
      {ω | horizontalStripHeight n ω 0 ≤ n}).toReal ≥ (1 / 2 : ℝ) := by
  let μ : ProbabilityMeasure LatticeConfiguration :=
    Classical.choose (horizontalStripTopWiredProbabilityMeasures_existsUnique_limit q n)
  let H : Set LatticeConfiguration := {ω | horizontalStripHeight n ω 0 ≤ n}
  let F : ℕ → Set LatticeConfiguration := fun M =>
    (horizontalStripLocalClosedCutSuccess M n)ᶜ
  let hμ : ℝ := ((μ : Measure LatticeConfiguration) H).toReal
  have hweak : Tendsto (horizontalStripTopWiredProbabilityMeasures q n) atTop (𝓝 μ) := by
    simpa [μ] using (Classical.choose_spec
      (horizontalStripTopWiredProbabilityMeasures_existsUnique_limit q n)).1
  have hfailZero : Tendsto (fun M : ℕ => ((μ : Measure LatticeConfiguration) (F M)).toReal)
      atTop (𝓝 0) := by
    simpa [μ, F] using
      _root_.PottsContinuity.FKC.Medial.horizontalStripHeightLimit_failure_mass_tendsto_zero q n
  have hfixed (M : ℕ) : 1 ≤ 2 * hμ + ((μ : Measure LatticeConfiguration) (F M)).toReal := by
    let seq : ℕ → ℝ := fun N =>
      ((horizontalStripTopWiredProbabilityMeasures q n N : Measure LatticeConfiguration) H).toReal +
      ((horizontalStripAsymmetricTopSidesProbabilityMeasures q n N : Measure LatticeConfiguration) H).toReal +
      ((horizontalStripAsymmetricTopSidesProbabilityMeasures q n N : Measure LatticeConfiguration) (F M)).toReal
    have hseq : Tendsto seq atTop (𝓝 (2 * hμ + ((μ : Measure LatticeConfiguration) (F M)).toReal)) := by
      simpa only [seq, hμ, μ, H, F] using
        horizontalStripHeightLimit_three_mass_estimate q n M
    have heventually : ∀ᶠ N : ℕ in atTop, 1 ≤ seq N := by
      filter_upwards [Filter.eventually_atTop.2 ⟨M, fun N hMN => hMN⟩] with N hMN
      let a : LatticeVertex := (-(N : ℤ), 0)
      let G : SimpleGraph (RectangleVertex a (2 * N) (2 * n)) :=
        rectangleGraph a (2 * N) (2 * n)
      let S : Set (generalRectangleDualBottomCoreVertex a (2 * N) (2 * n)) :=
        horizontalStripDualLowerCenterSeeds N n
      let dualEvent : Set (Configuration (rectangleGraph (-(N : ℤ) - 1, 0)
          (2 * N + 1) (2 * n))) :=
        generalRectangleDualBottomCoreAmbientSeedBoundaryEvent a (2 * N) (2 * n) S
      let asymEvent : Set (Configuration (horizontalStripAsymmetricRectangle N n)) :=
        horizontalStripAsymmetricCenterThreeSidesEvent N n
      have halt := horizontalStripFiniteHeight_probability_alternative q N n
      have hcore := horizontalStripCoreLowerCenterSeedBoundary_measure_le_asymmetric q N n
      have hcoreReal :
          (measure (rectangleGraph (-(N : ℤ) - 1, 0) (2 * N + 1) (2 * n)) q
            (BoundaryCondition.wired
              (generalRectangleDualBottomCoreAmbientBoundary (-(N : ℤ), 0) (2 * N) (2 * n)))
            dualEvent).toReal ≤
          (measure (horizontalStripAsymmetricRectangle N n) q
            (horizontalStripAsymmetricTopSidesBoundary N n) asymEvent).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) hcore
      have hasym := horizontalStripAsymmetricCenterThreeSides_probability_le_height_add_cutFailure
        q N M n hMN
      have hasymReal :
          (measure (horizontalStripAsymmetricRectangle N n) q
            (horizontalStripAsymmetricTopSidesBoundary N n) asymEvent).toReal ≤
          ((horizontalStripAsymmetricTopSidesProbabilityMeasure q N n : Measure LatticeConfiguration) H).toReal +
            ((horizontalStripAsymmetricTopSidesProbabilityMeasure q N n : Measure LatticeConfiguration) (F M)).toReal := by
        have hsumTop :
            ((horizontalStripAsymmetricTopSidesProbabilityMeasure q N n : Measure LatticeConfiguration) H) +
              ((horizontalStripAsymmetricTopSidesProbabilityMeasure q N n : Measure LatticeConfiguration) (F M)) ≠ ⊤ :=
          ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩
        calc
          _ ≤ (((horizontalStripAsymmetricTopSidesProbabilityMeasure q N n : Measure LatticeConfiguration) H) +
                ((horizontalStripAsymmetricTopSidesProbabilityMeasure q N n : Measure LatticeConfiguration) (F M))).toReal :=
            ENNReal.toReal_mono hsumTop hasym
          _ ≤ _ := ENNReal.toReal_add_le
      have htop := rectangleCenterTopConnectionEvent_probability_le_heightLE q N n
      have hsum :
          1 ≤
            ((horizontalStripTopWiredProbabilityMeasures q n N : Measure LatticeConfiguration) H).toReal +
              ((horizontalStripAsymmetricTopSidesProbabilityMeasures q n N : Measure LatticeConfiguration) H).toReal +
              ((horizontalStripAsymmetricTopSidesProbabilityMeasures q n N : Measure LatticeConfiguration) (F M)).toReal := by
        have hmid :
            1 ≤
              ((horizontalStripTopWiredProbabilityMeasures q n N : Measure LatticeConfiguration) H).toReal +
                ((horizontalStripAsymmetricTopSidesProbabilityMeasures q n N : Measure LatticeConfiguration) H).toReal +
                ((horizontalStripAsymmetricTopSidesProbabilityMeasures q n N : Measure LatticeConfiguration) (F M)).toReal := by
          have hAlt :
              1 ≤
                (measure G q (horizontalStripTopWiredBoundary N n)
                  (rectangleCenterTopConnectionEvent N n)).toReal +
                (measure (rectangleGraph (-(N : ℤ) - 1, 0) (2 * N + 1) (2 * n)) q
                  (BoundaryCondition.wired
                    (generalRectangleDualBottomCoreAmbientBoundary a (2 * N) (2 * n)))
                  dualEvent).toReal := by
            simpa only [G, a, S, dualEvent] using halt
          have hCoreMon := hcoreReal
          have hAsymMon := hasymReal
          have hTop :
              (measure G q (horizontalStripTopWiredBoundary N n)
                (rectangleCenterTopConnectionEvent N n)).toReal ≤
              ((horizontalStripTopWiredProbabilityMeasures q n N :
                Measure LatticeConfiguration) H).toReal := by
            change (measure (horizontalStripCutRectangle N n) q
                (horizontalStripTopWiredBoundary N n)
                (rectangleCenterTopConnectionEvent N n)).toReal ≤
              ((horizontalStripRectangleProbabilityMeasure q N n
                (horizontalStripTopWiredBoundary N n) : Measure LatticeConfiguration) H).toReal
            exact htop
          have htarget :
              1 ≤
                ((horizontalStripTopWiredProbabilityMeasures q n N :
                  Measure LatticeConfiguration) H).toReal +
                ((horizontalStripAsymmetricTopSidesProbabilityMeasures q n N :
                  Measure LatticeConfiguration) H).toReal +
                ((horizontalStripAsymmetricTopSidesProbabilityMeasures q n N :
                  Measure LatticeConfiguration) (F M)).toReal := by
            have h1 := hAlt
            have h2 := hCoreMon
            have h3 := hAsymMon
            have h4 := hTop
            dsimp [horizontalStripAsymmetricTopSidesProbabilityMeasures,
              horizontalStripTopWiredProbabilityMeasures] at h3 h4 ⊢
            linarith
          exact htarget
        simpa only [seq, H, F, asymEvent] using hmid
      exact hsum
    have hlimit := le_of_tendsto_of_tendsto tendsto_const_nhds hseq heventually
    exact hlimit
  have hsumLimit : Tendsto (fun M : ℕ => 2 * hμ + ((μ : Measure LatticeConfiguration) (F M)).toReal)
      atTop (𝓝 (2 * hμ)) := by
    simpa using (tendsto_const_nhds.add hfailZero)
  have hone : 1 ≤ 2 * hμ :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hsumLimit hfixed
  change hμ ≥ (1 / 2 : ℝ)
  nlinarith

end
end PottsContinuity.FKC.Medial
