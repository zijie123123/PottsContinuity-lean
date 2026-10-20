module

public import PottsContinuity.Thm3.Push.CompleteSourceEmbedded
public import PottsContinuity.Thm3.Push.IntervalArmStripWindowConnection
public import PottsContinuity.Thm3.Push.StripSourceArmLimit
public import PottsContinuity.Thm3.Push.TwoArmWindowLimit

@[expose] public section

namespace PottsContinuity.Push
open RSW PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit Exploration MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance completeSourceStripLimitEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

section
variable
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n) (q : Set.Ici (1:ℝ))
    (selectPrefix : CaseTwoTipEndpointRecord n s →
      Configuration (rectangleGraph (0,0) (2*n) (2*n)) →
      Option (List (RectangleVertex (0,0) (2*n) (2*n))))
    (hprefix : ∀ C D b trace,
      caseTwoTipEndpointSelector n s hfit C = some b → 0 < b.2.val.2 →
      selectPrefix b C = some trace →
      D ∩ caseTwoStoppedPrefixReveal n s hfit b trace =
        C ∩ caseTwoStoppedPrefixReveal n s hfit b trace → selectPrefix b D = some trace)
    (hsearch : ∀ C b,
      caseTwoConfinedPrefixConfiguration n s hfit b C ∈
        arcsConnectionEvent (caseTwoConfinedPrefixGraph n s hfit b)
          (intervalArmBottomArc (2*n) (4*(s:ℤ)) (5*(s:ℤ)))
          {z | z.val.1 = 4*(s:ℤ)-1 ∧ b.2.val.2 ≤ z.val.2} → (selectPrefix b C).isSome)
    (hpaths : ∀ C b trace,
      caseTwoTipEndpointSelector n s hfit C = some b →
      selectPrefix b C = some trace → Nonempty (CaseTwoDirectPrefixSourcePaths n s hfit C b trace))

include hs hfit selectPrefix hprefix hsearch hpaths

/-- The complete augmented source comparison on an actual finite strip
window, with both original host arm marginals. -/
theorem stripWindow_caseTwoCompleteSource_product_of_prefixLocality_and_sourcePaths
    (m : ℕ) (x : ℤ) (hlo : -(m:ℤ) ≤ x) (hhi : x+2*(n:ℤ) ≤ (m:ℤ)) :
    ((measure (PottsContinuity.squareLattice.induce (stripWindow n m : Set LatticeVertex))
      (criticalParameters q) (stripWindowBoundary n m 0)
      {C | embeddedConfigurationRestriction _ _ (intervalArmStripWindowEmbedding n m x hlo hhi)
        (intervalArmStripWindow_map_le n m x hlo hhi) C ∈ sourceCaseTwoFirstArm n s}).toReal *
      (measure (PottsContinuity.squareLattice.induce (stripWindow n m : Set LatticeVertex))
        (criticalParameters q) (stripWindowBoundary n m 0)
        {C | embeddedConfigurationRestriction _ _ (intervalArmStripWindowEmbedding n m x hlo hhi)
          (intervalArmStripWindow_map_le n m x hlo hhi) C ∈ sourceCaseTwoSecondArm n s}).toReal) /
      (1+(q:ℝ)^2) ≤ stripWindowEventProbability (selfDualParameters q) n m (stripLocalConnection n s x) := by
  have h := embedded_caseTwoCompleteSource_product_of_prefixLocality_and_sourcePaths
    n s hs hfit q selectPrefix hprefix hsearch hpaths _
    (intervalArmStripWindowEmbedding n m x hlo hhi)
    (intervalArmStripWindow_map_le n m x hlo hhi) (stripWindowBoundary n m 0)
  exact h.trans (intervalArmStripWindow_connection_probability_le_local (criticalParameters q) n m s x hlo hhi)

/-- The complete Case 2 product under the actual constructed infinite
strip law. Both finite marginals and their limits are discharged. -/
theorem strip_caseTwoCompleteSource_product_of_prefixLocality_and_sourcePaths
    (x : ℤ) :
    ((selfDualStripMeasure q n).real (stripCaseTwoFirstArm n s x) *
      (selfDualStripMeasure q n).real (stripCaseTwoSecondArm n s x))/(1+(q:ℝ)^2) ≤
      (selfDualStripMeasure q n).real (stripLocalConnection n s x) := by
  apply strip_local_product_lower_of_window_arm_limits q n s x
    (fun m => stripWindowEventProbability (selfDualParameters q) n m (stripCaseTwoFirstArm n s x))
    (fun m => stripWindowEventProbability (selfDualParameters q) n m (stripCaseTwoSecondArm n s x))
  · exact stripSourceSquareEvent_window_probability_tendsto (selfDualParameters q) n x
      (selfDualStripMeasure q n) (selfDualStripMeasure_isLimit q n) (sourceCaseTwoFirstArm n s)
  · exact stripSourceSquareEvent_window_probability_tendsto (selfDualParameters q) n x
      (selfDualStripMeasure q n) (selfDualStripMeasure_isLimit q n) (sourceCaseTwoSecondArm n s)
  · filter_upwards [eventually_stripWindow_contains_sourceSquare n x] with m hm
    change stripWindowEventProbability (selfDualParameters q) n m
        (stripSourceSquareEvent n x (sourceCaseTwoFirstArm n s)) *
        stripWindowEventProbability (selfDualParameters q) n m
        (stripSourceSquareEvent n x (sourceCaseTwoSecondArm n s)) / (1+(q:ℝ)^2) ≤ _
    rw [stripSourceSquareEvent_window_probability_eq (selfDualParameters q) n m x hm.1 hm.2,
      stripSourceSquareEvent_window_probability_eq (selfDualParameters q) n m x hm.1 hm.2]
    exact stripWindow_caseTwoCompleteSource_product_of_prefixLocality_and_sourcePaths
      n s hs hfit q selectPrefix hprefix hsearch hpaths m x hm.1 hm.2

/-- The printed Case 2 strip constant from actual limiting arm bounds,
using the complete augmented direct-prefix exploration interfaces. -/
theorem strip_caseTwoCompleteSource_lower_of_prefixLocality_and_sourcePaths
    (x : ℤ)
    (c₁ : ℝ) (hc₁ : 0 ≤ c₁)
    (hfirstProb : c₁/3 ≤ (selfDualStripMeasure q n).real (stripCaseTwoFirstArm n s x))
    (hsecondProb : c₁/6 ≤ (selfDualStripMeasure q n).real (stripCaseTwoSecondArm n s x)) :
    c₁^2/(18*(1+(q:ℝ)^2)) ≤ (selfDualStripMeasure q n).real (stripLocalConnection n s x) := by
  have hprod := strip_caseTwoCompleteSource_product_of_prefixLocality_and_sourcePaths
    n s hs hfit q selectPrefix hprefix hsearch hpaths x
  have hmul := mul_le_mul hfirstProb hsecondProb (by positivity : (0:ℝ) ≤ c₁/6)
    ENNReal.toReal_nonneg
  have heq : c₁^2/(18*(1+(q:ℝ)^2)) = (c₁/3)*(c₁/6)/(1+(q:ℝ)^2) := by
    field_simp [ne_of_gt (by positivity : (0:ℝ) < 1+(q:ℝ)^2)]; ring
  rw [heq]
  exact (div_le_div_of_nonneg_right hmul (by positivity)).trans hprod


end
end
end PottsContinuity.Push
