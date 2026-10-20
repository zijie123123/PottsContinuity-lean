module

public import PottsContinuity.Infinite.ComparisonStatements
public import PottsContinuity.Infinite.MeasurableApprox
public import PottsContinuity.PD.RCInfinite.SubgraphExhaustion

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Infinite

open PottsContinuity
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

/-- Free-to-wired stochastic domination for every measurable increasing event. -/
theorem free_infinite_le_wired_infinite_measurable
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit p q 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit p q 1 μ₁)
    (A : Set LatticeConfiguration) (hA : MeasurableSet A)
    (hupper : IsUpperSet A) : μ₀.real A ≤ μ₁.real A := by
  let ν₀ : ProbabilityMeasure LatticeConfiguration := ⟨μ₀, hμ₀.1⟩
  let ν₁ : ProbabilityMeasure LatticeConfiguration := ⟨μ₁, hμ₁.1⟩
  have hν₀ : (ν₀ : Measure LatticeConfiguration) = μ₀ := rfl
  have hν₁ : (ν₁ : Measure LatticeConfiguration) = μ₁ := rfl
  have hclopen : ∀ U : Set LatticeConfiguration, IsClopen U → IsUpperSet U →
      (((ν₀ U : NNReal) : ℝ) ≤ ((ν₁ U : NNReal) : ℝ)) := by
    intro U hUcl hUupper
    have hUcyl : IsCylinder U := isCylinder_of_clopen_upper hUcl hUupper
    obtain ⟨F, hF⟩ := hUcyl
    obtain ⟨m, hm⟩ := exists_box_supporting_edge_finset F
    have hFbox : (F : Set Edge) ⊆ boxEdges (0, 0) m := by
      intro e he
      exact hm e (Finset.mem_coe.mp he)
    have hUcyl' : IsCylinder U := ⟨F, hF⟩
    have hlocal := free_infinite_le_wired_infinite_local p q hp0 hp1 hq
      μ₀ μ₁ hμ₀ hμ₁ m hUcyl' (hF.mono hFbox) hUupper
    have hlocal' : (ν₀ : Measure LatticeConfiguration).real U ≤
        (ν₁ : Measure LatticeConfiguration).real U := by
      rw [hν₀, hν₁]
      exact hlocal
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn] using hlocal'
  have h := probabilityMeasure_measurable_upper_domination_of_clopen ν₀ ν₁ hclopen hA hupper
  have h' : (ν₀ : Measure LatticeConfiguration).real A ≤
      (ν₁ : Measure LatticeConfiguration).real A := by simpa using h
  simpa [hν₀, hν₁] using h'

end
end PottsContinuity.Infinite
