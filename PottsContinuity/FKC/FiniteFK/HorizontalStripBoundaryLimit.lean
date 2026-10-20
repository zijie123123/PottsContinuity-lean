-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripBoundaryLimit.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.CylinderConvergenceCriterion
public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutCylinderBound
public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutFailureDecay
public import PottsContinuity.FKC.FiniteFK.HorizontalStripCylinderSupportDichotomy
public import PottsContinuity.FKC.FiniteFK.HorizontalStripBoundaryCylinderLower
public import Mathlib.Topology.Instances.NNReal.Lemmas

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK

noncomputable section

private theorem horizontalStripProbabilityMeasure_toReal_apply_eq_coe
    (μ : ProbabilityMeasure LatticeConfiguration) (s : Set LatticeConfiguration) :
    ((μ s : NNReal) : ℝ) = ((μ : Measure LatticeConfiguration) s).toReal := by
  let z : ENNReal := (μ : Measure LatticeConfiguration) s
  have htop : z ≠ (⊤ : ENNReal) := measure_ne_top _ _
  have hcoe := ENNReal.coe_toNNReal htop
  change (z.toNNReal : ℝ) = z.toReal
  calc
    (z.toNNReal : ℝ) = (z.toNNReal : ENNReal).toReal := by simp
    _ = z.toReal := congrArg ENNReal.toReal hcoe

/-- Any admissible finite-boundary sequence has the canonical top-wired weak
limit, provided that the canonical top-wired exhaustion converges to that
limit. -/
theorem horizontalStripBoundaryProbabilityMeasures_tendsto_of_topWired
    (q : PottsContinuity.FKC.ClusterWeight) (n : ℕ)
    (ξ : ∀ N : ℕ, BoundaryCondition (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)))
    (hξ : ∀ N, (ξ N).boundary ⊆ horizontalStripTopSidesSet N n)
    (hTop : ∀ N, (BoundaryCondition.wired (horizontalStripTopWiredSet N n)).partition ≤
      (ξ N).partition)
    (μ : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (horizontalStripTopWiredProbabilityMeasures q n) atTop (𝓝 μ)) :
    Tendsto (fun N => horizontalStripRectangleProbabilityMeasure q N n (ξ N))
      atTop (𝓝 μ) := by
  let ν : ℕ → ProbabilityMeasure LatticeConfiguration :=
    fun N => horizontalStripRectangleProbabilityMeasure q N n (ξ N)
  have hcoord (F : Finset squareLattice.edgeSet) :
      Tendsto (fun N => ν N (LatticeConfiguration.allOpen F)) atTop
      (𝓝 (μ (LatticeConfiguration.allOpen F))) := by
    by_cases hNo : ¬ ∃ K : ℕ, ∀ e ∈ F,
        e ∈ Set.range (horizontalStripRectangleOriginalEdge K n)
    · have hempty : ∀ N, horizontalStripRectangleCylinderEvent N n F = ∅ :=
        (horizontalStripRectangleCylinder_finiteSupport_or_empty n F).resolve_left hNo
      have hμzero := horizontalStripTopWiredLimit_allOpen_eq_zero_of_no_finiteSupport
        q n F μ hμ hNo
      have hzero : ∀ N, ν N (LatticeConfiguration.allOpen F) = 0 := by
        intro N
        have hfinitezero := horizontalStripRectangleCylinder_probability_zero_of_no_finiteSupport
          q n N F (ξ N) hNo
        change (((horizontalStripRectangleProbabilityMeasure q N n (ξ N) :
          Measure LatticeConfiguration) (LatticeConfiguration.allOpen F)).toNNReal) = 0
        rw [horizontalStripRectangleProbabilityMeasure_allOpen]
        rw [hfinitezero]
        simp
      have htarget : μ (LatticeConfiguration.allOpen F) = 0 := hμzero
      rw [htarget]
      have hconst : (fun N => ν N (LatticeConfiguration.allOpen F)) = fun _ => (0 : NNReal) := by
        funext N
        exact hzero N
      rw [hconst]
      exact tendsto_const_nhds
    · have hsupport : ∃ K : ℕ, ∀ e ∈ F,
          e ∈ Set.range (horizontalStripRectangleOriginalEdge K n) := by
        exact not_not.mp hNo
      obtain ⟨K, hF⟩ := hsupport
      let topCoord : ℕ → ℝ := fun N =>
        ((horizontalStripTopWiredProbabilityMeasures q n N
          (LatticeConfiguration.allOpen F) : NNReal) : ℝ)
      let outerCoord : ℕ → ℝ := fun N =>
        ((ν N (LatticeConfiguration.allOpen F) : NNReal) : ℝ)
      let c : ℝ := ((μ (LatticeConfiguration.allOpen F) : NNReal) : ℝ)
      have htopNN := LatticeConfiguration.tendsto_allOpen_of_weak hμ F
      have htopR : Tendsto topCoord atTop (𝓝 c) := by
        change Tendsto
          (fun N => ((horizontalStripTopWiredProbabilityMeasures q n N
            (LatticeConfiguration.allOpen F) : NNReal) : ℝ)) atTop
          (𝓝 ((μ (LatticeConfiguration.allOpen F) : NNReal) : ℝ))
        exact (NNReal.continuous_coe.tendsto _).comp htopNN
      have hfail : Tendsto
          (fun N => (measure (horizontalStripCutRectangle N n) q (ξ N)
            (horizontalStripClosedCutFailureEvent N n K)).toReal)
          atTop (𝓝 0) := by
        simpa [horizontalStripClosedCutFailureEvent] using
          (tendsto_horizontalStripEitherBlockScan_none_probability_zero q n K ξ)
      have hupper : ∀ᶠ N : ℕ in atTop, outerCoord N ≤ c +
          (measure (horizontalStripCutRectangle N n) q (ξ N)
            (horizontalStripClosedCutFailureEvent N n K)).toReal := by
        filter_upwards [Filter.eventually_atTop.2 ⟨K, fun N hKN => hKN⟩] with N hKN
        have hbound := horizontalStripClosedCut_cylinder_probability_le_limit_add_failure
          hKN q (ξ N) (hξ N) (hTop N) F hF μ hμ
        have hmeasureEq : outerCoord N =
            (measure (horizontalStripCutRectangle N n) q (ξ N)
              (horizontalStripRectangleCylinderEvent N n F)).toReal := by
          dsimp [outerCoord, ν]
          rw [horizontalStripProbabilityMeasure_toReal_apply_eq_coe]
          rw [horizontalStripRectangleProbabilityMeasure_allOpen]
        simpa [c] using hmeasureEq ▸ hbound
      have hlower : ∀ᶠ N : ℕ in atTop, topCoord N ≤ outerCoord N :=
        Filter.Eventually.of_forall fun N => by
          have h := horizontalStripRectangleProbabilityMeasure_allOpen_boundary_lower
            q N n (ξ N) (hTop N) F
          change (((horizontalStripTopWiredProbabilityMeasures q n N
              (LatticeConfiguration.allOpen F) : NNReal) : ℝ) ≤
            ((ν N (LatticeConfiguration.allOpen F) : NNReal) : ℝ))
          rw [horizontalStripProbabilityMeasure_toReal_apply_eq_coe,
            horizontalStripProbabilityMeasure_toReal_apply_eq_coe]
          exact h
      have hupperLimit : Tendsto
          (fun N => c + (measure (horizontalStripCutRectangle N n) q (ξ N)
            (horizontalStripClosedCutFailureEvent N n K)).toReal)
          atTop (𝓝 c) := by
        simpa using tendsto_const_nhds.add hfail
      have hreal : Tendsto outerCoord atTop (𝓝 c) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le' htopR hupperLimit hlower hupper
      have hnn : Tendsto (fun N => ν N (LatticeConfiguration.allOpen F)) atTop
          (𝓝 (μ (LatticeConfiguration.allOpen F))) := by
        apply NNReal.tendsto_coe.mp
        change Tendsto (fun N => ((ν N (LatticeConfiguration.allOpen F) : NNReal) : ℝ))
          atTop (𝓝 ((μ (LatticeConfiguration.allOpen F) : NNReal) : ℝ))
        exact hreal
      exact hnn
  exact probabilityMeasures_tendsto_iff_allOpen_coordinates ν μ |>.2 hcoord

end
end PottsContinuity.FKC.Medial
