module

public import PottsContinuity.Thm3.Push.StripSourceArmLimit
public import PottsContinuity.Thm3.Push.StripWindowCaseOne
public import PottsContinuity.Thm3.Push.TwoArmWindowLimit

@[expose] public section

namespace PottsContinuity.Push
open PD.FK RSW MeasureTheory Filter Topology
noncomputable section

/-- The first original Case 1 interval-to-top arm, read on the strip. -/
abbrev stripCaseOneFirstArm (n s : ℕ) (x : ℤ) :=
  stripSourceSquareEvent n x (intervalArmEvent (2*n) (4*(s:ℤ)) (5*(s:ℤ)))

/-- The second original Case 1 interval-to-top arm in the same square. -/
abbrev stripCaseOneSecondArm (n s : ℕ) (x : ℤ) :=
  stripSourceSquareEvent n x (intervalArmEvent (2*n) (6*(s:ℤ)) (7*(s:ℤ)))

/-- Unconditional Case 1 strip product estimate at every real q>=1. Finite
exploration, every original boundary, host mixing, FKG and both actual arm
limits have all been proved; no selector or convergence premise remains. -/
theorem strip_intervalArm_product_lower_bound
    (q : Set.Ici (1:ℝ)) (n s : ℕ) (hs : 1 ≤ s) (hscale : 7*s < 2*n) (x : ℤ) :
    ((selfDualStripMeasure q n).real (stripCaseOneFirstArm n s x) *
      (selfDualStripMeasure q n).real (stripCaseOneSecondArm n s x))/(1+(q:ℝ)^2) ≤
      (selfDualStripMeasure q n).real (stripLocalConnection n s x) := by
  apply strip_local_product_lower_of_window_arm_limits q n s x
    (fun m => stripWindowEventProbability (selfDualParameters q) n m (stripCaseOneFirstArm n s x))
    (fun m => stripWindowEventProbability (selfDualParameters q) n m (stripCaseOneSecondArm n s x))
  · exact stripSourceSquareEvent_window_probability_tendsto (selfDualParameters q) n x
      (selfDualStripMeasure q n) (selfDualStripMeasure_isLimit q n) _
  · exact stripSourceSquareEvent_window_probability_tendsto (selfDualParameters q) n x
      (selfDualStripMeasure q n) (selfDualStripMeasure_isLimit q n) _
  · filter_upwards [eventually_stripWindow_contains_sourceSquare n x] with m hm
    change stripWindowEventProbability (selfDualParameters q) n m
        (stripSourceSquareEvent n x (intervalArmEvent (2*n) (4*(s:ℤ)) (5*(s:ℤ)))) *
        stripWindowEventProbability (selfDualParameters q) n m
        (stripSourceSquareEvent n x (intervalArmEvent (2*n) (6*(s:ℤ)) (7*(s:ℤ)))) / (1+(q:ℝ)^2) ≤ _
    rw [stripSourceSquareEvent_window_probability_eq (selfDualParameters q) n m x hm.1 hm.2,
      stripSourceSquareEvent_window_probability_eq (selfDualParameters q) n m x hm.1 hm.2]
    exact stripWindow_intervalArm_connection_probability_ge_product q n m s hs hscale x hm.1 hm.2

/-- The printed Case 1 strip constant from the two ACTUAL limiting arm
bounds. No identical non-strict finite-window bound is presumed. -/
theorem strip_intervalArm_case_one_lower_bound
    (q : Set.Ici (1:ℝ)) (n s : ℕ) (hs : 1 ≤ s) (hscale : 7*s < 2*n) (x : ℤ)
    (c₁ : ℝ) (hc₁ : 0 ≤ c₁)
    (hfirst : c₁/3 ≤ (selfDualStripMeasure q n).real (stripCaseOneFirstArm n s x))
    (hsecond : c₁/3 ≤ (selfDualStripMeasure q n).real (stripCaseOneSecondArm n s x)) :
    c₁^2/(9*(1+(q:ℝ)^2)) ≤ (selfDualStripMeasure q n).real (stripLocalConnection n s x) := by
  have hmul := mul_le_mul hfirst hsecond (by positivity : (0:ℝ) ≤ c₁/3) ENNReal.toReal_nonneg
  have heq : c₁^2/(9*(1+(q:ℝ)^2)) = (c₁/3)*(c₁/3)/(1+(q:ℝ)^2) := by
    field_simp [ne_of_gt (by positivity : (0:ℝ) < 1+(q:ℝ)^2)]; ring
  rw [heq]
  exact (div_le_div_of_nonneg_right hmul (by positivity)).trans
    (strip_intervalArm_product_lower_bound q n s hs hscale x)

end
end PottsContinuity.Push
