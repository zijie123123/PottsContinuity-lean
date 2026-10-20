module

public import PottsContinuity.Thm3.Prop4.TiltedLimit
public import PottsContinuity.Thm3.Prop4.TouchUnion
public import PottsContinuity.Thm3.RSW.SelfDualSetup

/-!
# The constructed tilted law and explicit self-dual specialization

A law is selected only from proved UNIQUE existence. The touching estimate for
the self-dual law at every slope in [-1,1] is proved as
`Thm3.Touch.selfDual_tilted_touch_all_slopes_corrected_of_reducedMarginal` in
`Thm3.Touch.ReducedMarginalComposition`; its reduced marginal hypothesis is
`RSW.selfDual_tiltedStrip_reflected_marginal`.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

/-- The uniquely constructed intrinsic-top cylinder law. -/
noncomputable def tiltedStripMeasure (θ : PD.FK.Parameters) (n : ℕ) (t : ℝ) :
    Measure (TiltedConfiguration n t) :=
  (isTiltedStripLimit_top_existsUnique θ n t).choose

/-- The chosen measure satisfies the actual cylinder-limit predicate. -/
theorem tiltedStripMeasure_isLimit (θ : PD.FK.Parameters) (n : ℕ) (t : ℝ) :
    IsTiltedStripLimit θ n t 0 (tiltedStripMeasure θ n t) :=
  (isTiltedStripLimit_top_existsUnique θ n t).choose_spec.1

instance tiltedStripMeasure_isProbabilityMeasure (θ : PD.FK.Parameters) (n : ℕ) (t : ℝ) :
    IsProbabilityMeasure (tiltedStripMeasure θ n t) :=
  (tiltedStripMeasure_isLimit θ n t).1

/-- The actual tilted law at sqrt(q)/(1+sqrt(q)), for every real q≥1.
No assertion identifying this value with a threshold is part of the definition. -/
noncomputable def selfDualTiltedStripMeasure (q : Set.Ici (1 : ℝ)) (n : ℕ) (t : ℝ) :
    Measure (TiltedConfiguration n t) :=
  tiltedStripMeasure (RSW.selfDualParameters q) n t

/-- The self-dual specialization is a genuine top-only cylinder limit. -/
theorem selfDualTiltedStripMeasure_isLimit (q : Set.Ici (1 : ℝ)) (n : ℕ) (t : ℝ) :
    IsTiltedStripLimit (RSW.selfDualParameters q) n t 0 (selfDualTiltedStripMeasure q n t) :=
  tiltedStripMeasure_isLimit (RSW.selfDualParameters q) n t

instance selfDualTiltedStripMeasure_isProbabilityMeasure (q : Set.Ici (1 : ℝ))
    (n : ℕ) (t : ℝ) : IsProbabilityMeasure (selfDualTiltedStripMeasure q n t) :=
  (selfDualTiltedStripMeasure_isLimit q n t).1

end PottsContinuity.Thm3.Prop4
