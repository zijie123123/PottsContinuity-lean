module

public import PottsContinuity.PlanarTopology.TransposeConfiguration
public import PottsContinuity.PlanarTopology.InfiniteClusterIsometry
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Polish

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite
noncomputable section

theorem configurationIsoLaw_ae_iff (e : PD.squareLattice ≃g PD.squareLattice)
    (μ : Measure LatticeConfiguration) (P : LatticeConfiguration → Prop) :
    (∀ᵐ η ∂μ.map (latticeConfigurationIsoHomeomorph e), P η) ↔
      ∀ᵐ ω ∂μ, P (latticeConfigurationIsoHomeomorph e ω) := by
  have hh := (latticeConfigurationIsoHomeomorph e).toMeasurableEquiv.map_ae μ
  simp only [Homeomorph.toMeasurableEquiv_coe] at hh
  rw [← hh]
  rfl

/-- The transposed law is translation invariant even when the original law
has no coordinate-interchange symmetry. -/
theorem transposeLaw_translation_invariant (μ : Measure LatticeConfiguration)
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ) (a : LatticeVertex) :
    (μ.map (latticeConfigurationIsoHomeomorph latticeTransposeIso)).map (edgeTranslate a) =
      μ.map (latticeConfigurationIsoHomeomorph latticeTransposeIso) := by
  rw [Measure.map_map (edgeTranslate_measurable _) (latticeConfigurationIsoHomeomorph_measurable _)]
  have hcomm : (edgeTranslate a) ∘ latticeConfigurationIsoHomeomorph latticeTransposeIso =
      latticeConfigurationIsoHomeomorph latticeTransposeIso ∘ edgeTranslate a.swap := by
    funext ω
    simpa only [Prod.swap_swap,Function.comp_def] using (transposeConfiguration_translate a.swap ω).symm
  rw [hcomm,← Measure.map_map (latticeConfigurationIsoHomeomorph_measurable _) (edgeTranslate_measurable _),htranslation]

theorem transposeLaw_FKG (μ : Measure LatticeConfiguration)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (A B : Set LatticeConfiguration) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAu : IsUpperSet A) (hBu : IsUpperSet B) :
    μ.map (latticeConfigurationIsoHomeomorph latticeTransposeIso) A *
      μ.map (latticeConfigurationIsoHomeomorph latticeTransposeIso) B ≤
      μ.map (latticeConfigurationIsoHomeomorph latticeTransposeIso) (A ∩ B) := by
  have hm := latticeConfigurationIsoHomeomorph_measurable latticeTransposeIso
  rw [Measure.map_apply hm hA,Measure.map_apply hm hB,Measure.map_apply hm (hA.inter hB)]
  apply hFKG _ _ (hm hA) (hm hB)
  · intro ω η hωη hω
    exact hAu (transposeConfiguration_monotone hωη) hω
  · intro ω η hωη hω
    exact hBu (transposeConfiguration_monotone hωη) hω

theorem configurationIsoLaw_unique (e : PD.squareLattice ≃g PD.squareLattice)
    (μ : Measure LatticeConfiguration) (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster ω) :
    ∀ᵐ η ∂μ.map (latticeConfigurationIsoHomeomorph e), atMostOneInfiniteCluster η := by
  apply (configurationIsoLaw_ae_iff e μ _).mpr
  filter_upwards [hunique] with ω hω
  exact (atMostOneInfiniteCluster_configurationIso_iff e ω).mpr hω

theorem configurationIsoLaw_infinite (e : PD.squareLattice ≃g PD.squareLattice)
    (μ : Measure LatticeConfiguration) (hinfinite : ∀ᵐ ω ∂μ, ω ∈ infiniteClusterEvent) :
    ∀ᵐ η ∂μ.map (latticeConfigurationIsoHomeomorph e), η ∈ infiniteClusterEvent := by
  apply (configurationIsoLaw_ae_iff e μ _).mpr
  filter_upwards [hinfinite] with ω hω
  exact (infiniteClusterEvent_configurationIso_iff e ω).mpr hω

theorem transposeLaw_dual_unique (μ : Measure LatticeConfiguration)
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω)) :
    ∀ᵐ η ∂μ.map (latticeConfigurationIsoHomeomorph latticeTransposeIso),
      atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph η) := by
  apply (configurationIsoLaw_ae_iff latticeTransposeIso μ _).mpr
  filter_upwards [hunique] with ω hω
  rw [wholePlaneDualConfiguration_transpose]
  exact (atMostOneInfiniteCluster_configurationIso_iff latticeTransposeIso _).mpr hω

theorem transposeLaw_dual_infinite (μ : Measure LatticeConfiguration)
    (hinfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent) :
    ∀ᵐ η ∂μ.map (latticeConfigurationIsoHomeomorph latticeTransposeIso),
      wholePlaneDualConfigurationHomeomorph η ∈ infiniteClusterEvent := by
  apply (configurationIsoLaw_ae_iff latticeTransposeIso μ _).mpr
  filter_upwards [hinfinite] with ω hω
  rw [wholePlaneDualConfiguration_transpose]
  exact (infiniteClusterEvent_configurationIso_iff latticeTransposeIso _).mpr hω

end
end PottsContinuity.PlanarTopology
