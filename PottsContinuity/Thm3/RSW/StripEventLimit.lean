module

public import PottsContinuity.Thm3.RSW.StripInterlacing

/-!
# Transport of finite-window connection bounds to the genuine strip law

Events are evaluated on the literal closed extension of the sampled window.
For clopen strip events their actual finite probabilities converge to the
constructed strip law. Uniform estimates from finite stopped explorations
therefore pass to the source strip event without assuming an infinite DMP.
-/

@[expose] public section

namespace PottsContinuity.RSW

open MeasureTheory Filter Topology PD.FK

/-- Actual finite top-wired window probability of an event read on its literal
closed extension to the strip. This definition applies on its entire carrier. -/
noncomputable def stripWindowEventProbability (θ : Parameters) (n m : ℕ)
    (E : Set (StripConfiguration n)) : ℝ :=
  (measure (squareLattice.induce (stripWindow n m : Set (ℤ × ℤ))) θ
    (stripWindowBoundary n m 0)
    {C | stripPlaneRestriction n (stripWindowPlaneConfiguration n m C) ∈ E}).toReal

/-- Every clopen actual strip event has the expected finite-window probability
limit under the genuine top-only strip law. -/
theorem stripWindowEventProbability_tendsto (θ : Parameters) (n : ℕ)
    (μ : Measure (StripConfiguration n)) (hμ : IsTopWiredStripLimit θ n 0 μ)
    (E : Set (StripConfiguration n)) (hE : IsClopen E) :
    Tendsto (fun m => stripWindowEventProbability θ n m E) atTop (𝓝 (μ.real E)) := by
  obtain ⟨ν, hν, _⟩ := stripWindowPlaneProbabilityMeasure_top_existsUnique_limit θ n
  have hmap := isTopWiredStripLimit_of_plane_tendsto θ n 0 ν hν
  have heq := isTopWiredStripLimit_unique θ n 0 μ _ hμ hmap
  have hpre : IsClopen ((stripPlaneRestriction n) ⁻¹' E) :=
    hE.preimage (stripPlaneRestriction_continuous n)
  have htarget : μ.real E = ν.toMeasure.real ((stripPlaneRestriction n) ⁻¹' E) := by
    rw [heq]
    change (ν.toMeasure.map (stripPlaneRestriction n)).real E = _
    unfold Measure.real
    rw [Measure.map_apply (stripPlaneRestriction_continuous n).measurable
      hE.isOpen.measurableSet]
  have hfinite (m : ℕ) : stripWindowEventProbability θ n m E =
      (stripWindowPlaneProbabilityMeasure θ n 0 m).toMeasure.real
        ((stripPlaneRestriction n) ⁻¹' E) := by
    unfold stripWindowEventProbability Measure.real
    rw [stripWindowPlaneProbabilityMeasure_apply θ n 0 m _ hpre.isOpen.measurableSet]
    rfl
  simp_rw [hfinite]
  rw [htarget]
  have hconv := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hν hpre
  simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, Function.comp_def] using
    NNReal.continuous_coe.continuousAt.tendsto.comp hconv

/-- Eventual finite-window bounds pass to the actual strip event probability. -/
theorem strip_event_lower_of_finite_window_bounds (θ : Parameters) (n : ℕ)
    (μ : Measure (StripConfiguration n)) (hμ : IsTopWiredStripLimit θ n 0 μ)
    (E : Set (StripConfiguration n)) (hE : IsClopen E) (c : ℝ)
    (hfinite : ∀ᶠ m : ℕ in atTop, c ≤ stripWindowEventProbability θ n m E) :
    c ≤ μ.real E :=
  le_of_tendsto_of_tendsto tendsto_const_nhds
    (stripWindowEventProbability_tendsto θ n μ hμ E hE) hfinite

end PottsContinuity.RSW
