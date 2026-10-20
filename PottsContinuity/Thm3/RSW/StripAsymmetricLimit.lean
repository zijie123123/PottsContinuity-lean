module

public import PottsContinuity.Thm3.RSW.StripAsymmetricReadMeasures

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory Filter Topology
noncomputable section

/-- The exact source cylinder-limit predicate gives weak convergence of the
actual centered-window reads under either lateral convention. -/
theorem stripWindowReadProbabilityMeasures_tendsto (θ : Parameters) (n : ℕ) (i : Fin 2)
    (μ : ProbabilityMeasure (StripConfiguration n))
    (hμ : IsTopWiredStripLimit θ n i μ.toMeasure) :
    Tendsto (fun M => stripWindowReadProbabilityMeasure θ n i M) atTop (𝓝 μ) := by
  apply stripProbabilityMeasures_tendsto_of_allOpen_coordinates n
  intro A
  apply NNReal.tendsto_coe.mp
  have hr : Tendsto (fun M => (stripWindowReadProbabilityMeasure θ n i M).toMeasure.real
      (stripCoordinateAllOpen n A)) atTop (𝓝 (μ.toMeasure.real (stripCoordinateAllOpen n A))) := by
    change Tendsto (fun M => (stripWindowReadProbabilityMeasure θ n i M).toMeasure.real
      {ω | ∀ e ∈ A, ω e=true}) atTop (𝓝 (μ.toMeasure.real {ω | ∀ e ∈ A, ω e=true}))
    apply (hμ.2 A (fun _ => true)).congr'
    filter_upwards [eventually_stripWindow_finset_edge_lift n A] with M hM
    rw [stripWindowReadProbabilityMeasure_pattern θ n i M A (fun _ => true) hM]
  simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn] using hr

/-- The asymmetric top/ends exhaustion converges to the SAME actual strip
law. The proof uses the all-Parameters finite domain sandwich and the proved
lateral-boundary independence, rather than a presumed asymmetric limit. -/
theorem stripAsymmetricCenteredProbabilityMeasures_tendsto (θ : Parameters) (n : ℕ)
    (μ : ProbabilityMeasure (StripConfiguration n))
    (hμ : IsTopWiredStripLimit θ n 0 μ.toMeasure) :
    Tendsto (stripAsymmetricCenteredProbabilityMeasure θ n) atTop (𝓝 μ) := by
  have htop := stripWindowReadProbabilityMeasures_tendsto θ n 0 μ hμ
  have hends := stripWindowReadProbabilityMeasures_tendsto θ n 1 μ
    ((isTopWiredStripLimit_iff_top θ n 1 μ.toMeasure).mpr hμ)
  apply stripProbabilityMeasures_tendsto_of_allOpen_coordinates n
  intro A
  have hclopen := stripCoordinateAllOpen_isClopen n A
  have hupper := stripCoordinateAllOpen_isUpperSet n A
  have hlow := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto htop hclopen
  have hhigh := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hends hclopen
  have hlo : ∀ M, stripWindowReadProbabilityMeasure θ n 0 M (stripCoordinateAllOpen n A) ≤
      stripAsymmetricCenteredProbabilityMeasure θ n M (stripCoordinateAllOpen n A) := by
    intro M
    apply NNReal.coe_le_coe.mp
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn] using
      (stripAsymmetricCentered_probability_sandwich θ n M _ hclopen.isOpen.measurableSet hupper).1
  have hhi : ∀ M, stripAsymmetricCenteredProbabilityMeasure θ n M (stripCoordinateAllOpen n A) ≤
      stripWindowReadProbabilityMeasure θ n 1 M (stripCoordinateAllOpen n A) := by
    intro M
    apply NNReal.coe_le_coe.mp
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn] using
      (stripAsymmetricCentered_probability_sandwich θ n M _ hclopen.isOpen.measurableSet hupper).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh
    (Eventually.of_forall hlo) (Eventually.of_forall hhi)

/-- At the explicit self-dual parameter, the actual asymmetric source reads
converge to the already constructed strip measure for every real q>=1. -/
theorem selfDual_stripAsymmetricCenteredProbabilityMeasures_tendsto
    (q : Set.Ici (1:ℝ)) (n : ℕ) :
    Tendsto (stripAsymmetricCenteredProbabilityMeasure (selfDualParameters q) n) atTop
      (𝓝 (⟨selfDualStripMeasure q n,inferInstance⟩ : ProbabilityMeasure (StripConfiguration n))) :=
  stripAsymmetricCenteredProbabilityMeasures_tendsto (selfDualParameters q) n
    ⟨selfDualStripMeasure q n,inferInstance⟩ (selfDualStripMeasure_isLimit q n)

end
end PottsContinuity.RSW
