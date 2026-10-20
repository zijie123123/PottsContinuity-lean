-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripHeightFrontier.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripHeightFiniteExhaustion
public import PottsContinuity.FKC.FiniteFK.HorizontalStripLocalCutClopen
public import PottsContinuity.FKC.FiniteFK.HorizontalStripLocalCutProbability
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Continuity
public import PottsContinuity.FKC.FiniteFK.HorizontalStripLocalCutAlmostSure
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.FKC.Medial

noncomputable section

open PottsContinuity.FKC.FiniteFK

/-- On the open success region of any fixed-radius local-cut event, the
original height event agrees exactly with the actual finite-rectangle event.
Consequently its frontier cannot meet that clopen success region. -/
theorem horizontalStripHeightLE_frontier_subset_localCutFailure
    (M n : ℕ) :
    frontier {ω | horizontalStripHeight n ω 0 ≤ n} ⊆
      (horizontalStripLocalClosedCutSuccess M n)ᶜ := by
  classical
  intro ω hfront hsuccess
  rw [frontier_eq_closure_inter_closure] at hfront
  let U : Set LatticeConfiguration := horizontalStripLocalClosedCutSuccess M n ∩
    if ω ∈ horizontalStripHeightFiniteRectangleEvent M n then
      horizontalStripHeightFiniteRectangleEvent M n
    else (horizontalStripHeightFiniteRectangleEvent M n)ᶜ
  have hUopen : IsOpen U := by
    change IsOpen (horizontalStripLocalClosedCutSuccess M n ∩
      if ω ∈ horizontalStripHeightFiniteRectangleEvent M n then
        horizontalStripHeightFiniteRectangleEvent M n
      else (horizontalStripHeightFiniteRectangleEvent M n)ᶜ)
    apply (isClopen_horizontalStripLocalClosedCutSuccess M n).2.inter
    by_cases hωfinite : ω ∈ horizontalStripHeightFiniteRectangleEvent M n
    · simpa [hωfinite] using
        (isClopen_horizontalStripHeightFiniteRectangleEvent M n).2
    · simpa [hωfinite] using
        ((isClopen_horizontalStripHeightFiniteRectangleEvent M n).compl).2
  have hωU : ω ∈ U := by
    simp only [U, Set.mem_inter_iff]
    exact ⟨hsuccess, by by_cases h : ω ∈ horizontalStripHeightFiniteRectangleEvent M n <;> simp [h]⟩
  have hUeq : ∀ y ∈ U,
      (y ∈ {z | horizontalStripHeight n z 0 ≤ n} ↔
        y ∈ horizontalStripHeightFiniteRectangleEvent M n) := by
    intro y hy
    have hysuccess : y ∈ horizontalStripLocalClosedCutSuccess M n := hy.1
    by_cases hωfinite : ω ∈ horizontalStripHeightFiniteRectangleEvent M n
    · constructor
      · intro hheight
        exact horizontalStripHeightLE_and_localClosedCutSuccess_subset_finiteRectangle
          M n ⟨hheight, hysuccess⟩
      · intro hfinite
        exact horizontalStripHeightFiniteRectangleEvent_subset_heightLE M n hfinite
    · have hyNotFinite : y ∉ horizontalStripHeightFiniteRectangleEvent M n := by
        simpa [U, hωfinite] using hy.2
      constructor
      · intro hheight
        exact (hyNotFinite
          (horizontalStripHeightLE_and_localClosedCutSuccess_subset_finiteRectangle
            M n ⟨hheight, hysuccess⟩)).elim
      · intro hfinite
        exact (hyNotFinite hfinite).elim
  have hUcontained : U ⊆ {ω | horizontalStripHeight n ω 0 ≤ n} ∨
      U ⊆ ({ω | horizontalStripHeight n ω 0 ≤ n})ᶜ := by
    by_cases hωfinite : ω ∈ horizontalStripHeightFiniteRectangleEvent M n
    · left
      intro y hy
      exact (hUeq y hy).2 (by simpa [U, hωfinite] using hy.2)
    · right
      intro y hy
      change y ∉ {ω | horizontalStripHeight n ω 0 ≤ n}
      intro hheight
      have hfinite : y ∈ horizontalStripHeightFiniteRectangleEvent M n :=
        (hUeq y hy).1 hheight
      have hnot : y ∉ horizontalStripHeightFiniteRectangleEvent M n := by
        simpa [U, hωfinite] using hy.2
      exact hnot hfinite
  rcases hUcontained with hUheight | hUheightCompl
  · have hhit := (mem_closure_iff_nhds.mp hfront.2) U (hUopen.mem_nhds hωU)
    rcases hhit with ⟨y, hyU, hycompl⟩
    exact hycompl (hUheight hyU)
  · have hhit := (mem_closure_iff_nhds.mp hfront.1) U (hUopen.mem_nhds hωU)
    rcases hhit with ⟨y, hyU, hyheight⟩
    exact (hUheightCompl hyU) hyheight

/-- Almost surely some local closed-cut success occurs, so the frontier of the
original height event has zero mass under the actual canonical top-wired
fixed-height limit. -/
theorem horizontalStripHeightLE_frontier_measure_zero
    (q : PottsContinuity.FKC.ClusterWeight) (n : ℕ)
    (μ : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (horizontalStripTopWiredProbabilityMeasures q n) atTop (𝓝 μ)) :
    ((μ : Measure LatticeConfiguration)
      (frontier {ω | horizontalStripHeight n ω 0 ≤ n})) = 0 := by
  have hae := horizontalStripLocalClosedCutSuccess_ae_exists q n μ hμ
  have haeNot : ∀ᵐ ω ∂(μ : Measure LatticeConfiguration),
      ω ∉ frontier {ω | horizontalStripHeight n ω 0 ≤ n} := by
    filter_upwards [hae] with ω hsuccess
    intro hfront
    rcases hsuccess with ⟨M, hsuccess⟩
    exact (horizontalStripHeightLE_frontier_subset_localCutFailure M n hfront) hsuccess
  exact (measure_eq_zero_iff_ae_notMem).2 haeNot

end
end PottsContinuity.FKC.Medial
