-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripFiniteHeightLawTransport.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripFiniteHeightEventTransport
public import PottsContinuity.FKC.FiniteFK.RectangleVerticalReflection
public import PottsContinuity.FKC.FiniteFK.GeneralRectangleBottomWiredDuality
public import PottsContinuity.FKC.FiniteFK.GeneralRectangleDualBottomCoreConnectivityLaw
public import Mathlib.MeasureTheory.Measure.Portmanteau

@[expose] public section

open MeasureTheory

namespace PottsContinuity.FKC.Medial
open PottsContinuity.FKC.FiniteFK
noncomputable section

local instance finiteHeightLawRectangleEdgeFintype (N n : ℕ) :
    Fintype (rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)).edgeSet := Fintype.ofFinite _
local instance finiteHeightLawRectangleConfigFintype (N n : ℕ) :
    Fintype (Configuration (rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n))) := Fintype.ofFinite _
local instance finiteHeightLawDualConfigFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (Configuration (rectangleDualGraph a w h)) := Fintype.ofFinite _
local instance finiteHeightLawAmbientConfigFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (Configuration (rectangleGraph (a.1 - 1, a.2) (w + 1) h)) := Fintype.ofFinite _

/-- Bottom wiring transported by the genuine horizontal-midline reflection
is the centered top-wired law. -/
theorem rectangleBottomWired_reflection_preimage_centerTop_probability_eq
    (q : ClusterWeight) (N n : ℕ) :
    (measure (rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)) q
      (BoundaryCondition.wired
        (rectangleArbitraryBottomCollarBottom (-(N : ℤ), 0) (2 * N) (2 * n)))
      {A | configurationIso (rectangleGraphVerticalReflectionIso
        (-(N : ℤ), 0) (2 * N) (2 * n)) A ∈ rectangleCenterTopConnectionEvent N n}).toReal =
    (measure (rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)) q
      (horizontalStripTopWiredBoundary N n)
      (rectangleCenterTopConnectionEvent N n)).toReal := by
  let a : LatticeVertex := (-(N : ℤ), 0)
  let G := rectangleGraph a (2 * N) (2 * n)
  let e := rectangleGraphVerticalReflectionIso a (2 * N) (2 * n)
  have hset : rectangleVerticalReflectionTopSet a (2 * N) (2 * n) =
      horizontalStripTopWiredSet N n := by
    ext v
    change v.val.2 = 0 + (2 * n : ℤ) ↔ v.val.2 = (2 * n : ℤ)
    omega
  have hlaw : (law G q
      (BoundaryCondition.wired (rectangleArbitraryBottomCollarBottom a (2 * N) (2 * n)))).map
        (configurationIso e) =
      law G q (horizontalStripTopWiredBoundary N n) := by
    rw [law_rectangleVerticalReflection_bottom_map]
    rw [hset]
    rfl
  have hm := congrArg (fun p : PMF (Configuration G) =>
      p.toMeasure (rectangleCenterTopConnectionEvent N n)) hlaw
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    (MeasurableSet.of_discrete (s := rectangleCenterTopConnectionEvent N n))] at hm
  simpa [G, a, FiniteFK.measure, Set.preimage] using congrArg ENNReal.toReal hm

/-- The actual bottom-wired primal configuration law, mapped by the literal
complementary-edge duality, assigns the same event mass as the actual expanded
three-side-wired dual law. -/
theorem generalRectangleBottomWired_dualEvent_preimage_probability_eq
    (a : LatticeVertex) (w h : ℕ) (q : ClusterWeight)
    (S : Set (generalRectangleDualBottomCoreVertex a w h)) :
    (measure (rectangleArbitraryBottomCollarInnerGraph a w h) q
      (BoundaryCondition.wired (rectangleArbitraryBottomCollarBottom a w h))
      {A | rectanglePrimalDualConfigurationEquiv a w h A ∈
        generalRectangleDualBottomCoreTrueDualSeedBoundaryEvent a w h S}).toReal =
    (measure (rectangleDualGraph a w h) q
      (BoundaryCondition.wired (generalRectangleDualBottomCollarInnerThreeSides a w h))
      (generalRectangleDualBottomCoreTrueDualSeedBoundaryEvent a w h S)).toReal := by
  let P := rectangleArbitraryBottomCollarInnerGraph a w h
  let D := rectangleDualGraph a w h
  let d := rectanglePrimalDualConfigurationEquiv a w h
  have hlaw := generalRectangleBottomWiredDuality_law_map a w h q
  have hm := congrArg (fun p : PMF (Configuration D) =>
      p.toMeasure (generalRectangleDualBottomCoreTrueDualSeedBoundaryEvent a w h S)) hlaw
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    (MeasurableSet.of_discrete
      (s := generalRectangleDualBottomCoreTrueDualSeedBoundaryEvent a w h S))] at hm
  simpa [P, D, d, FiniteFK.measure, Set.preimage] using congrArg ENNReal.toReal hm

/-- Combining exact finite FK duality with the actual ambient/core connectivity
law comparison transports any retained-seed three-side event probability. -/
theorem generalRectangleBottomWired_dualEvent_ambient_probability_eq
    (a : LatticeVertex) (w h : ℕ) (q : ClusterWeight)
    (S : Set (generalRectangleDualBottomCoreVertex a w h)) :
    (measure (rectangleArbitraryBottomCollarInnerGraph a w h) q
      (BoundaryCondition.wired (rectangleArbitraryBottomCollarBottom a w h))
      {A | rectanglePrimalDualConfigurationEquiv a w h A ∈
        generalRectangleDualBottomCoreTrueDualSeedBoundaryEvent a w h S}).toReal =
    (measure (rectangleGraph (a.1 - 1, a.2) (w + 1) h) q
      (BoundaryCondition.wired (generalRectangleDualBottomCoreAmbientBoundary a w h))
      (generalRectangleDualBottomCoreAmbientSeedBoundaryEvent a w h S)).toReal := by
  rw [generalRectangleBottomWired_dualEvent_preimage_probability_eq]
  exact (generalRectangleDualBottomCore_threeSideConnectivity_probability_eq a w h q S).symm

end
end PottsContinuity.FKC.Medial
