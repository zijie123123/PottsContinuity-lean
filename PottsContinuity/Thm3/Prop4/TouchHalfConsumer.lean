module

public import PottsContinuity.Thm3.Prop4.TiltedIsolationComparison
public import PottsContinuity.Thm3.Prop4.AllSlopeTouch

/-!
# Touch consumers after discharging the infinite strip comparison

The explored-strip comparison is discharged by
`selfDual_tilted_isolation_probability_le_touch`. The mixed-dual half-height bound is
the hypothesis `hhalf`; it is supplied by
`PlanarMixed.TiltedHalfHeight.selfDualTiltedHalfHeight_ge_half` in
`Thm3.Touch.ReducedMarginalComposition`, through
`Thm3.Touch.selfDual_tilted_touch_all_slopes_corrected_of_infiniteHalfHeight`.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- Every real slope follows from the half-height bound only at the finite denominator representatives. -/
theorem selfDual_tilted_touch_all_slopes_corrected_of_dualityHalf
    (q : Set.Ici (1 : ℝ)) (n m : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hhalf : ∀ (d : ℕ) (a : ℤ), 1 ≤ d → d ≤ 2*m →
      (a : ℝ)/(d : ℝ) ∈ Set.Icc (-1 : ℝ) 1 →
      (1/2 : ℝ) ≤ (selfDualTiltedStripMeasure q (2*n) ((a : ℝ)/(d : ℝ))).real
        {ω | lowestTopConnectedHeight (2*n) (by omega) ((a : ℝ)/(d : ℝ)) ω 0 ≤ n}) :
    ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(n : ℝ)^2*(m : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) n m t := by
  apply selfDual_tilted_touch_all_slopes_corrected_of_dualityHalf_and_stripComparison q n m hn hnm hhalf
  intro d a _ _ hs z hz
  exact selfDual_tilted_isolation_probability_le_touch q n m _ hs z
    ((mem_tiltedCandidates n (n*d*m) _ z).mp hz).2

end PottsContinuity.Thm3.Prop4
