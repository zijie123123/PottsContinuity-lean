module

public import PottsContinuity.Thm3.Push.CompleteSourceIntervalBound
public import PottsContinuity.Thm3.Push.SourceRecordAverage

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit Exploration MeasureTheory RSW
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance completeSourceLinearEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

section
variable
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n) (q : Set.Ici (1:ℝ))
    (ξ : BoundaryCondition (RectangleVertex (0,0) (2*n) (2*n)))
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

/-- The full source-arm joint event is bounded by physical interval
connection. No observability of discarded far-boundary completion is needed. -/
theorem caseTwoCompleteSource_linear_of_prefixLocality_and_sourcePaths :
    (1/(1+(q:ℝ)^2)) *
      (measure (rectangleGraph (0,0) (2*n) (2*n)) (criticalParameters q) ξ
        (sourceCaseTwoFirstArm n s ∩ sourceCaseTwoSecondArm n s)).toReal ≤
      (measure (rectangleGraph (0,0) (2*n) (2*n)) (criticalParameters q) ξ
        (caseTwoSourceIntervalConnection n s)).toReal := by
  let reveal := caseTwoCompleteSourceRevealMap n s hfit selectPrefix
  let hstable := caseTwoCompleteSourceRevealMap_stable_of_prefixLocality n s hs hfit selectPrefix hprefix
  apply stopped_event_lower_of_bounds_on_event _ (criticalParameters q) ξ reveal hstable
    (caseTwoSourceIntervalConnection n s) (sourceCaseTwoFirstArm n s ∩ sourceCaseTwoSecondArm n s)
    (1/(1+(q:ℝ)^2)) (by positivity)
  intro C hC
  have htip := (caseTwoTipEndpointSelector_isSome_iff n s hfit C).mpr hC.2
  obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp htip
  have hrec := caseTwoCompletePrefixSelector_isSome_of_source_arm n s hs hfit selectPrefix hsearch C b hb hC.1
  obtain ⟨rec,hr⟩ := Option.isSome_iff_exists.mp hrec
  apply caseTwoCompleteSource_interval_lower_bound_of_prefixLocality_and_sourcePaths
    n s hs hfit q ξ selectPrefix hprefix C b rec hb hr
  intro trace htrace
  have hr' : caseTwoCompletePrefixSelector n s hfit selectPrefix b C = some (.inl trace) := by
    simpa only [htrace] using hr
  have hpref := ((caseTwoCompletePrefixSelector_eq_inl_iff n s hfit selectPrefix b C trace).mp hr').2
  exact hpaths C b trace hb hpref

end
end
end PottsContinuity.Push
