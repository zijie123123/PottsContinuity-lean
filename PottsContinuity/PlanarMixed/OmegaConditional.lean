module

public import PottsContinuity.PlanarMixed.OmegaInterfaces
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Conditional mixed-square transfer to the extremal-path domain Omega

DCST TeX L1229-L1235. The geometric inputs `ExtremalBoundaryComparison` and
`SquareCrossingRestrictsToArcs`, and in the conditional form the fiber law
`ExtremalConditionalLaw`, are hypotheses of these lemmas. The geometric inputs
are proved for the crosscut domains in `PlanarMixed.VerticalCrosscutGeometry` and
`PlanarMixed.SourceActiveCrosscutComparison`, and for the interval-arm domains in
`Thm3.Push.IntervalArmOmegaLowerBound`. These lemmas are conditional steps, not
Lemma 2 itself or the general BD12 symmetric-domain theorem. The numerical bound
comes from the proved actual wired-arc square theorem, not from an assumed
Omega probability estimate. All parameters are explicit self-dual parameters.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12 MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The square law transfers to any actual embedded Omega graph whose
exterior-induced partitions are bounded by eta and whose exact restriction
preserves the required actual connection. The premises are the two explicit
geometric interfaces, not a crossing-probability estimate. -/
theorem omega_wiredArc_lower_bound_of_extremalBoundaryComparison
    {V : Type*} [Finite V]
    (q : Set.Ici (1 : ℝ)) (a : LatticeVertex) (N : ℕ) (hN : 1 ≤ N)
    (Ω : SimpleGraph V) (f : V ↪ RectangleVertex a N N)
    (hΩ : Ω.map f ≤ rectangleGraph a N N)
    (A C : Set V) (η : BoundaryCondition V)
    (hboundary : ExtremalBoundaryComparison a N hN Ω f η)
    (hpaths : SquareCrossingRestrictsToArcs a N Ω f hΩ A C) :
    1 / (1 + (q : ℝ)^2) ≤
      (measure Ω (criticalParameters q) η (arcsConnectionEvent Ω A C)).toReal := by
  have hsubset : arcsConnectionEvent (rectangleGraph a N N)
      (Square.squareLeftArc a N) (Square.squareRightArc a N) ⊆
      {ω | embeddedConfigurationRestriction Ω (rectangleGraph a N N) f hΩ ω ∈
        arcsConnectionEvent Ω A C} := hpaths
  calc
    _ ≤ (measure (rectangleGraph a N N) (criticalParameters q)
        (squareSeparateLeftRightBoundary a N hN)
        (arcsConnectionEvent (rectangleGraph a N N)
          (Square.squareLeftArc a N) (Square.squareRightArc a N))).toReal :=
      Square.square_wiredLeftRight_lower_bound q a N hN
    _ ≤ (measure (rectangleGraph a N N) (criticalParameters q)
        (squareSeparateLeftRightBoundary a N hN)
        {ω | embeddedConfigurationRestriction Ω (rectangleGraph a N N) f hΩ ω ∈
          arcsConnectionEvent Ω A C}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)
    _ ≤ _ := embeddedConfigurationRestriction_preimage_measure_le_of_frozen_partition
      Ω (rectangleGraph a N N) f hΩ (criticalParameters q)
      (squareSeparateLeftRightBoundary a N hN) η
      (arcsConnectionEvent Ω A C) (arcsConnectionEvent_isUpperSet A C) hboundary

/-- On one realized source exploration fiber, the actual Omega connection has
the source constant once the exact fiber law and the two geometry interfaces
are supplied. The original conditioning law and its positive support witness
are explicit; no source selector or boundary identification is claimed here. -/
theorem omega_conditional_wiredArc_lower_bound_of_extremalInterfaces
    {U V : Type*} [Finite U] [Finite V]
    (q : Set.Ici (1 : ℝ)) (a : LatticeVertex) (N : ℕ) (hN : 1 ≤ N)
    (Ω : SimpleGraph V) (f : V ↪ RectangleVertex a N N)
    (hΩ : Ω.map f ≤ rectangleGraph a N N)
    (A C : Set V) (η : BoundaryCondition V)
    (hboundary : ExtremalBoundaryComparison a N hN Ω f η)
    (hpaths : SquareCrossingRestrictsToArcs a N Ω f hΩ A C)
    (H : SimpleGraph U) (ξ : BoundaryCondition U)
    (F : Set (Configuration H))
    (hF : ∃ ω ∈ F, ω ∈ (law H (criticalParameters q) ξ).support)
    (r : Configuration H → Configuration Ω)
    (hlaw : ExtremalConditionalLaw q H Ω ξ η F hF r) :
    1 / (1 + (q : ℝ)^2) ≤
      (((law H (criticalParameters q) ξ).filter F hF).toMeasure
        (r ⁻¹' arcsConnectionEvent Ω A C)).toReal := by
  have hm := congrArg PMF.toMeasure hlaw
  rw [← PMF.toMeasure_map _ _ measurable_from_top] at hm
  have heval := congrArg
    (fun μ : Measure (Configuration Ω) => μ (arcsConnectionEvent Ω A C)) hm
  rw [Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top] at heval
  rw [heval]
  exact omega_wiredArc_lower_bound_of_extremalBoundaryComparison
    q a N hN Ω f hΩ A C η hboundary hpaths

end
end PottsContinuity.PlanarMixed
