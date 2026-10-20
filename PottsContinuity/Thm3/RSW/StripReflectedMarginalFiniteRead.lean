module

public import PottsContinuity.Thm3.RSW.StripAsymmetricLimit
public import PottsContinuity.Thm3.RSW.StripReflectedCentralLawConditional

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality DualityExt MeasureTheory Filter Topology
noncomputable section
attribute [local instance] configurationMeasurableSpace

section
variable (n k : ℕ) (hn : 1 ≤ n)
variable (read : ∀ M : ℕ,
  Configuration (rectangleSubgraphDualGraph (stripRectangleWithoutTop_map_le n M)) →
    Configuration (rectangleDualGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)))
variable
  (hsource : ∀ M : ℕ, k*n+1 ≤ M →
    ∀ C : Configuration (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))),
      read M (stripWindowPrunedDualConfiguration n M C) =
        stripCentralDualConfiguration n k (stripWindowOriginalRead n M C))
  (hreflect : ∀ M : ℕ, k*n+1 ≤ M →
    ∀ C : Configuration (rectangleGraph (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n)),
      read M (stripAsymmetricPrunedDualRead n M C) =
        stripReflectedCentralDualConfiguration n k hn (stripAsymmetricCenteredRead n M C))

include read hsource hreflect

/-- The exact finite reflected law gives the exact central-event equality
once the two literal statewise read transports are identified. The remaining
premises are deterministic identities, never probability bounds or laws. -/
theorem selfDual_finite_central_dual_probability_eq_of_finiteRead
    (q : Set.Ici (1:ℝ)) (M : ℕ) (hM : k*n+1 ≤ M)
    (E : Set (Configuration (rectangleDualGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)))) :
    (stripWindowReadProbabilityMeasure (selfDualParameters q) n 0 M).toMeasure.real
      {ω | stripCentralDualConfiguration n k ω ∈ E} =
    (stripAsymmetricCenteredProbabilityMeasure (selfDualParameters q) n M).toMeasure.real
      {ω | stripReflectedCentralDualConfiguration n k hn ω ∈ E} := by
  rw [stripWindowReadProbabilityMeasure_apply _ _ _ _ _
      (stripCentralDualConfiguration_event_isClopen n k E).isOpen.measurableSet,
    stripAsymmetricCenteredProbabilityMeasure_apply _ _ _ _
      (stripReflectedCentralDualConfiguration_event_isClopen n k hn E).isOpen.measurableSet]
  have h := congrArg (fun p => p.map (read M))
    (selfDual_stripWindowPrunedDual_eq_asymmetric_reflected n M q)
  rw [PMF.map_comp,PMF.map_comp] at h
  have hp := congrArg (fun p => (p.toMeasure E).toReal) h
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top,
    PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at hp
  have hs : {C | (read M ∘ stripWindowPrunedDualConfiguration n M) C ∈ E} =
      {C | stripCentralDualConfiguration n k (stripWindowOriginalRead n M C) ∈ E} := by
    ext C
    simp only [Set.mem_ofPred_eq,Function.comp_apply,hsource M hM C]
  have ht : {C | (read M ∘ stripAsymmetricPrunedDualRead n M) C ∈ E} =
      {C | stripReflectedCentralDualConfiguration n k hn (stripAsymmetricCenteredRead n M C) ∈ E} := by
    ext C
    simp only [Set.mem_ofPred_eq,Function.comp_apply,hreflect M hM C]
  change ((law _ _ _).toMeasure {C | (read M ∘ stripWindowPrunedDualConfiguration n M) C ∈ E}).toReal =
    ((law _ _ _).toMeasure {C | (read M ∘ stripAsymmetricPrunedDualRead n M) C ∈ E}).toReal at hp
  rw [hs,ht] at hp
  exact hp

/-- The exact remaining finite read identities suffice for the infinite
reflected local marginal. All finite mixed laws, boundary partitions,
asymmetric exhaustion limits and probability transports are proved. -/
theorem selfDual_strip_reflected_marginal_of_finiteRead (q : Set.Ici (1:ℝ)) :
    Measure.map (stripCentralDualConfiguration n k) (selfDualStripMeasure q n) =
      Measure.map (stripReflectedCentralDualConfiguration n k hn) (selfDualStripMeasure q n) := by
  have hsrc : Measurable (stripCentralDualConfiguration n k) := by
    intro E hE
    exact (stripCentralDualConfiguration_event_isClopen n k E).isOpen.measurableSet
  have href : Measurable (stripReflectedCentralDualConfiguration n k hn) := by
    intro E hE
    exact (stripReflectedCentralDualConfiguration_event_isClopen n k hn E).isOpen.measurableSet
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply hsrc hE,Measure.map_apply href hE]
  have hwindow := stripWindowReadProbabilityMeasures_tendsto (selfDualParameters q) n 0
    (⟨selfDualStripMeasure q n,inferInstance⟩ : ProbabilityMeasure (StripConfiguration n))
    (selfDualStripMeasure_isLimit q n)
  have hasym := selfDual_stripAsymmetricCenteredProbabilityMeasures_tendsto q n
  have hl : Tendsto (fun M => (stripWindowReadProbabilityMeasure (selfDualParameters q) n 0 M).toMeasure.real
      {ω | stripCentralDualConfiguration n k ω ∈ E}) atTop
      (𝓝 ((selfDualStripMeasure q n).real {ω | stripCentralDualConfiguration n k ω ∈ E})) := by
    have h := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hwindow
      (stripCentralDualConfiguration_event_isClopen n k E)
    change Tendsto _ atTop (𝓝 ((ProbabilityMeasure.toMeasure (⟨selfDualStripMeasure q n,inferInstance⟩ :
      ProbabilityMeasure (StripConfiguration n))).real _))
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn,ProbabilityMeasure.coeFn_def,
      ProbabilityMeasure.coe_mk,ProbabilityMeasure.mk_apply,Measure.real,ENNReal.toReal,Function.comp_def] using
      NNReal.continuous_coe.continuousAt.tendsto.comp h
  have hr : Tendsto (fun M => (stripAsymmetricCenteredProbabilityMeasure (selfDualParameters q) n M).toMeasure.real
      {ω | stripReflectedCentralDualConfiguration n k hn ω ∈ E}) atTop
      (𝓝 ((selfDualStripMeasure q n).real {ω | stripReflectedCentralDualConfiguration n k hn ω ∈ E})) := by
    have h := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hasym
      (stripReflectedCentralDualConfiguration_event_isClopen n k hn E)
    change Tendsto _ atTop (𝓝 ((ProbabilityMeasure.toMeasure (⟨selfDualStripMeasure q n,inferInstance⟩ :
      ProbabilityMeasure (StripConfiguration n))).real _))
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn,ProbabilityMeasure.coeFn_def,
      ProbabilityMeasure.coe_mk,ProbabilityMeasure.mk_apply,Measure.real,ENNReal.toReal,Function.comp_def] using
      NNReal.continuous_coe.continuousAt.tendsto.comp h
  have hr' : Tendsto (fun M => (stripWindowReadProbabilityMeasure (selfDualParameters q) n 0 M).toMeasure.real
      {ω | stripCentralDualConfiguration n k ω ∈ E}) atTop
      (𝓝 ((selfDualStripMeasure q n).real {ω | stripReflectedCentralDualConfiguration n k hn ω ∈ E})) := by
    apply hr.congr'
    filter_upwards [eventually_ge_atTop (k*n+1)] with M hM
    rw [selfDual_finite_central_dual_probability_eq_of_finiteRead n k hn read hsource hreflect q M hM E]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    (tendsto_nhds_unique hl hr')

end
end
end PottsContinuity.RSW
