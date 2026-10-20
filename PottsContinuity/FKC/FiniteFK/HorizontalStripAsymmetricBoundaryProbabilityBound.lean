-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripAsymmetricBoundaryProbabilityBound.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripAsymmetricBoundaryLocalization
public import PottsContinuity.FKC.FiniteFK.HorizontalStripAsymmetricBoundaryLimit
public import PottsContinuity.FKC.FiniteFK.HorizontalStripHeightFiniteExhaustion
public import PottsContinuity.FKC.FiniteFK.HorizontalStripLocalCutClopen
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
open FiniteProbability

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance asymBoundEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripAsymmetricRectangle N n).edgeSet := Fintype.ofFinite _
local instance asymBoundConfigFintype (N n : ℕ) :
    Fintype (Configuration (horizontalStripAsymmetricRectangle N n)) := Fintype.ofFinite _
local instance asymBoundVertexDecidableEq (N n : ℕ) :
    DecidableEq (RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n)) := Classical.decEq _

/-- Actual finite-rectangle connectivity from the central lower half to any
of the literal left, right, or top sides. -/
def horizontalStripAsymmetricCenterThreeSidesEvent (N n : ℕ) :
    Set (Configuration (horizontalStripAsymmetricRectangle N n)) :=
  {A | ∃ u : RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n),
    u.val.1 = 0 ∧ 0 ≤ u.val.2 ∧ u.val.2 ≤ (n : ℤ) ∧
    ∃ z : RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n),
      z ∈ horizontalStripAsymmetricFullThreeSides N n ∧
      ActualConnected (horizontalStripAsymmetricRectangle N n) A u z}

private theorem horizontalStripAsymmetricCenterEvent_preimage_subset
    (N M n : ℕ) (hMN : M ≤ N) :
    {A : Configuration (horizontalStripAsymmetricRectangle N n) |
      A ∈ horizontalStripAsymmetricCenterThreeSidesEvent N n} ⊆
    {A | horizontalStripAsymmetricPlaneExtension N n A ∈
      {ω | horizontalStripHeight n ω 0 ≤ n} ∪
        (horizontalStripLocalClosedCutSuccess M n)ᶜ} := by
  rintro A ⟨u, huX, huYlo, huYhi, z, hz, hconn⟩
  have hloc := horizontalStripAsymmetric_center_to_boundary_localizes
    N M n hMN A huX ⟨huYlo, huYhi⟩ hz hconn
  rcases hloc with hheight | hfail
  · change horizontalStripAsymmetricPlaneExtension N n A ∈
      {ω | horizontalStripHeight n ω 0 ≤ n} ∪ _
    exact Or.inl hheight
  · change horizontalStripAsymmetricPlaneExtension N n A ∈
      {ω | horizontalStripHeight n ω 0 ≤ n} ∪ _
    exact Or.inr hfail

/-- For every actual finite asymmetric FK sample, a central-to-three-sides
connection is covered by the original infinite-strip height event or by the
fixed-radius two-closed-cut failure event. -/
theorem horizontalStripAsymmetricCenterThreeSides_probability_le_height_add_cutFailure
    (q : ClusterWeight) (N M n : ℕ) (hMN : M ≤ N) :
    measure (horizontalStripAsymmetricRectangle N n) q
      (horizontalStripAsymmetricTopSidesBoundary N n)
      (horizontalStripAsymmetricCenterThreeSidesEvent N n) ≤
    ((horizontalStripAsymmetricTopSidesProbabilityMeasure q N n :
      Measure LatticeConfiguration)
      {ω | horizontalStripHeight n ω 0 ≤ n}) +
    ((horizontalStripAsymmetricTopSidesProbabilityMeasure q N n :
      Measure LatticeConfiguration)
      (horizontalStripLocalClosedCutSuccess M n)ᶜ) := by
  let μ := horizontalStripAsymmetricTopSidesProbabilityMeasure q N n
  let H : Set LatticeConfiguration := {ω | horizontalStripHeight n ω 0 ≤ n}
  let C : Set LatticeConfiguration := (horizontalStripLocalClosedCutSuccess M n)ᶜ
  have hH : MeasurableSet H := by
    change MeasurableSet {ω | horizontalStripHeight n ω 0 ≤ n}
    rw [horizontalStripHeightLE_eq_iUnion_finiteRectangleEvent]
    exact MeasurableSet.iUnion fun k =>
      (isClopen_horizontalStripHeightFiniteRectangleEvent k n).2.measurableSet
  have hC : MeasurableSet C :=
    (isClopen_horizontalStripLocalClosedCutFailure M n).2.measurableSet
  have hsubset := horizontalStripAsymmetricCenterEvent_preimage_subset N M n hMN
  calc
    measure (horizontalStripAsymmetricRectangle N n) q
        (horizontalStripAsymmetricTopSidesBoundary N n)
        (horizontalStripAsymmetricCenterThreeSidesEvent N n) ≤
      measure (horizontalStripAsymmetricRectangle N n) q
        (horizontalStripAsymmetricTopSidesBoundary N n)
        {A | horizontalStripAsymmetricPlaneExtension N n A ∈ H ∪ C} :=
          measure_mono hsubset
    _ = (μ : Measure LatticeConfiguration) (H ∪ C) := by
      symm
      exact horizontalStripAsymmetricTopSidesProbabilityMeasure_apply_preimage q N n
        (H ∪ C) (hH.union hC)
    _ ≤ (μ : Measure LatticeConfiguration) H + (μ : Measure LatticeConfiguration) C :=
      measure_union_le H C

end
end PottsContinuity.FKC.Medial
