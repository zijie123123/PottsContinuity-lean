module

public import PottsContinuity.PlanarTopology.AssociationReversal
public import PottsContinuity.PD.Duality.WholePlaneDualConfiguration
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial
noncomputable section

/-- The actual complementary crossing-bond transform reverses configuration order. -/
theorem wholePlaneDualConfiguration_antitone : Antitone wholePlaneDualConfigurationHomeomorph := by
  intro ω η h e
  simp only [wholePlaneDualConfigurationHomeomorph_apply]
  have hh := h (wholePlaneDualCrossingEdgeEquiv e)
  cases hω : ω (wholePlaneDualCrossingEdgeEquiv e) <;>
    cases hη : η (wholePlaneDualCrossingEdgeEquiv e) <;> simp_all

/-- The actual complementary-dual law inherits measurable-upper positive association. -/
theorem wholePlaneDualLaw_FKG
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (A B : Set LatticeConfiguration) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAu : IsUpperSet A) (hBu : IsUpperSet B) :
    μ.map wholePlaneDualConfigurationHomeomorph A * μ.map wholePlaneDualConfigurationHomeomorph B ≤
      μ.map wholePlaneDualConfigurationHomeomorph (A ∩ B) :=
  upperSet_FKG_map_of_antitone μ hFKG wholePlaneDualConfigurationHomeomorph
    wholePlaneDualConfigurationHomeomorph_measurable wholePlaneDualConfiguration_antitone A B hA hB hAu hBu

end
end PottsContinuity.PlanarTopology
