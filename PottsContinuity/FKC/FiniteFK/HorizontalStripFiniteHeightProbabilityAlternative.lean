-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripFiniteHeightProbabilityAlternative.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripReflectedHeightDualAlternative
public import PottsContinuity.FKC.FiniteFK.HorizontalStripFiniteHeightLawTransport
public import Mathlib.MeasureTheory.Measure.NullMeasurable

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial MeasureTheory

noncomputable section

/-- Lower-center face bases in the retained core of the expanded dual
rectangle. -/
def horizontalStripDualLowerCenterSeeds (N n : ℕ) :
    Set (generalRectangleDualBottomCoreVertex (-(N : ℤ), 0) (2*N) (2*n)) :=
  {u | u.1.1.1 = 0 ∧ u.1.1.2 < (n : ℤ)}

private theorem reflected_failure_mem_dualSeedBoundary
    (N n : ℕ) (B : Configuration (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)))
    (hfail : configurationIso
      (rectangleGraphVerticalReflectionIso (-(N : ℤ), 0) (2*N) (2*n)) B ∉
        rectangleCenterTopConnectionEvent N n) :
    rectanglePrimalDualConfigurationEquiv (-(N : ℤ), 0) (2*N) (2*n) B ∈
      generalRectangleDualBottomCoreTrueDualSeedBoundaryEvent
        (-(N : ℤ), 0) (2*N) (2*n) (horizontalStripDualLowerCenterSeeds N n) := by
  obtain ⟨s, t, hsx, hslo, hshi, hpath, htarget⟩ :=
    rectangle_reflected_no_center_top_connection_dual_left_or_top_path N n B hfail
  let u : generalRectangleDualBottomCoreVertex (-(N : ℤ), 0) (2*N) (2*n) :=
    ⟨s, hslo⟩
  have hu : u ∈ horizontalStripDualLowerCenterSeeds N n := by
    change u.1.1.1 = 0 ∧ u.1.1.2 < (n : ℤ)
    exact ⟨hsx, hshi⟩
  have ht : t ∈ generalRectangleDualBottomCollarInnerThreeSides
      (-(N : ℤ), 0) (2*N) (2*n) := by
    change t.1.1 = -((N : ℤ)) - 1 ∨
      t.1.1 = -(N : ℤ) + (2*N : ℤ) ∨ t.1.2 = 0 + (2*n : ℤ)
    rcases htarget with hleft | htop
    · exact Or.inl hleft
    · exact Or.inr (Or.inr (by simpa using htop))
  refine ⟨u, hu, t, ht, ?_⟩
  change ActualConnected (rectangleDualGraph (-(N : ℤ), 0) (2*N) (2*n))
    (rectangleDualConfiguration (-(N : ℤ), 0) (2*N) (2*n) B) u.1 t
  exact hpath

/-- The finite-height alternative under the top-wired law: either the primal
center reaches the top, or the complementary dual reaches a retained lower
center seed to the true left/top boundary. -/
theorem horizontalStripFiniteHeight_probability_alternative
    (q : ClusterWeight) (N n : ℕ) :
    1 ≤
      (measure (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)) q
        (horizontalStripTopWiredBoundary N n)
        (rectangleCenterTopConnectionEvent N n)).toReal +
      (measure (rectangleGraph (-(N : ℤ)-1, 0) (2*N+1) (2*n)) q
        (BoundaryCondition.wired
          (generalRectangleDualBottomCoreAmbientBoundary
            (-(N : ℤ), 0) (2*N) (2*n)))
        (generalRectangleDualBottomCoreAmbientSeedBoundaryEvent
          (-(N : ℤ), 0) (2*N) (2*n)
          (horizontalStripDualLowerCenterSeeds N n))).toReal := by
  classical
  let a : LatticeVertex := (-(N : ℤ), 0)
  let G := rectangleGraph a (2*N) (2*n)
  let ξ := BoundaryCondition.wired
    (rectangleArbitraryBottomCollarBottom a (2*N) (2*n))
  let E : Set (Configuration G) :=
    {B | configurationIso (rectangleGraphVerticalReflectionIso a (2*N) (2*n)) B ∈
      rectangleCenterTopConnectionEvent N n}
  let S := horizontalStripDualLowerCenterSeeds N n
  let F : Set (Configuration G) :=
    {B | rectanglePrimalDualConfigurationEquiv a (2*N) (2*n) B ∈
      generalRectangleDualBottomCoreTrueDualSeedBoundaryEvent a (2*N) (2*n) S}
  let : MeasurableSpace (Configuration G) := configurationMeasurableSpace G
  let : DiscreteMeasurableSpace (Configuration G) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  let : Fintype G.edgeSet := Fintype.ofFinite _
  let : Fintype (Configuration G) := Fintype.ofFinite _
  let μ : Measure (Configuration G) := measure G q ξ
  have hsubset : Eᶜ ⊆ F := by
    intro B hB
    apply reflected_failure_mem_dualSeedBoundary N n B
    simpa [E, G, a] using hB
  have hcomp : (μ Eᶜ).toReal ≤ (μ F).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)
  have hsum : μ E + μ Eᶜ = μ Set.univ := by
    exact measure_add_measure_compl₀
      (μ := μ) ((MeasurableSet.of_discrete (s := E)).nullMeasurableSet)
  have huniv : μ Set.univ = 1 := by
    simp [μ, FiniteFK.measure]
  have hsumReal : (μ E).toReal + (μ Eᶜ).toReal = 1 := by
    have h := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), huniv] at h
    exact h
  have htop : (μ E).toReal =
      (measure G q (horizontalStripTopWiredBoundary N n)
        (rectangleCenterTopConnectionEvent N n)).toReal := by
    simpa [μ, E, G, a, FiniteFK.measure] using
      (rectangleBottomWired_reflection_preimage_centerTop_probability_eq q N n)
  have hdual : (μ F).toReal =
      (measure (rectangleGraph (-(N : ℤ)-1, 0) (2*N+1) (2*n)) q
        (BoundaryCondition.wired
          (generalRectangleDualBottomCoreAmbientBoundary a (2*N) (2*n)))
        (generalRectangleDualBottomCoreAmbientSeedBoundaryEvent a (2*N) (2*n) S)).toReal := by
    simpa [μ, F, G, ξ, a, S, FiniteFK.measure] using
      (generalRectangleBottomWired_dualEvent_ambient_probability_eq
        a (2*N) (2*n) q S)
  calc
    1 = (μ E).toReal + (μ Eᶜ).toReal := hsumReal.symm
    _ ≤ (measure G q (horizontalStripTopWiredBoundary N n)
          (rectangleCenterTopConnectionEvent N n)).toReal +
        (measure (rectangleGraph (-(N : ℤ)-1, 0) (2*N+1) (2*n)) q
          (BoundaryCondition.wired
            (generalRectangleDualBottomCoreAmbientBoundary a (2*N) (2*n)))
          (generalRectangleDualBottomCoreAmbientSeedBoundaryEvent a (2*N) (2*n) S)).toReal := by
      have hb := add_le_add_right hcomp ((μ E).toReal)
      simpa only [htop, hdual] using hb
    _ = _ := by rfl

end
end PottsContinuity.FKC.FiniteFK
