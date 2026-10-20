module

public import PottsContinuity.PlanarTopology.ReflectionConfiguration
public import PottsContinuity.PlanarTopology.TransposeLaw
public import PottsContinuity.PlanarTopology.HalfPlaneNonpercolation

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite
noncomputable section

theorem latticeConfigurationIso_translation (a : LatticeVertex) (ω : LatticeConfiguration) :
    latticeConfigurationIsoHomeomorph (latticeTranslationIso a) ω = edgeTranslate a ω := rfl

theorem atMostOneInfiniteCluster_translate_iff (a : LatticeVertex) (ω : LatticeConfiguration) :
    atMostOneInfiniteCluster (edgeTranslate a ω) ↔ atMostOneInfiniteCluster ω := by
  simpa only [latticeConfigurationIso_translation] using
    atMostOneInfiniteCluster_configurationIso_iff (latticeTranslationIso a) ω

theorem infiniteClusterEvent_translate_iff (a : LatticeVertex) (ω : LatticeConfiguration) :
    edgeTranslate a ω ∈ infiniteClusterEvent ↔ ω ∈ infiniteClusterEvent := by
  simpa only [latticeConfigurationIso_translation] using
    infiniteClusterEvent_configurationIso_iff (latticeTranslationIso a) ω

theorem reflectionXLaw_translation_invariant (μ : Measure LatticeConfiguration)
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ) (a : LatticeVertex) :
    (μ.map (latticeConfigurationIsoHomeomorph kstReflectionXIso)).map (edgeTranslate a) =
      μ.map (latticeConfigurationIsoHomeomorph kstReflectionXIso) := by
  rw [Measure.map_map (edgeTranslate_measurable _) (latticeConfigurationIsoHomeomorph_measurable _)]
  have hcomm : (edgeTranslate a) ∘ latticeConfigurationIsoHomeomorph kstReflectionXIso =
      latticeConfigurationIsoHomeomorph kstReflectionXIso ∘ edgeTranslate (-a.1,a.2) := by
    funext ω
    simpa only [Prod.fst,Prod.snd,neg_neg,Function.comp_def] using
      (reflectionXConfiguration_translate (-a.1,a.2) ω).symm
  rw [hcomm,← Measure.map_map (latticeConfigurationIsoHomeomorph_measurable _) (edgeTranslate_measurable _),htranslation]

theorem reflectionXLaw_FKG (μ : Measure LatticeConfiguration)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (A B : Set LatticeConfiguration) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAu : IsUpperSet A) (hBu : IsUpperSet B) :
    μ.map (latticeConfigurationIsoHomeomorph kstReflectionXIso) A *
      μ.map (latticeConfigurationIsoHomeomorph kstReflectionXIso) B ≤
      μ.map (latticeConfigurationIsoHomeomorph kstReflectionXIso) (A ∩ B) := by
  have hm := latticeConfigurationIsoHomeomorph_measurable kstReflectionXIso
  rw [Measure.map_apply hm hA,Measure.map_apply hm hB,Measure.map_apply hm (hA.inter hB)]
  apply hFKG _ _ (hm hA) (hm hB)
  · intro ω η hωη hω
    exact hAu (reflectionXConfiguration_monotone hωη) hω
  · intro ω η hωη hω
    exact hBu (reflectionXConfiguration_monotone hωη) hω

theorem reflectionXLaw_dual_unique (μ : Measure LatticeConfiguration)
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω)) :
    ∀ᵐ η ∂μ.map (latticeConfigurationIsoHomeomorph kstReflectionXIso),
      atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph η) := by
  apply (configurationIsoLaw_ae_iff kstReflectionXIso μ _).mpr
  filter_upwards [hunique] with ω hω
  rw [wholePlaneDualConfiguration_reflectionX]
  apply (atMostOneInfiniteCluster_translate_iff (-1,0) _).mpr
  exact (atMostOneInfiniteCluster_configurationIso_iff kstReflectionXIso _).mpr hω

theorem reflectionXLaw_dual_infinite (μ : Measure LatticeConfiguration)
    (hinfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent) :
    ∀ᵐ η ∂μ.map (latticeConfigurationIsoHomeomorph kstReflectionXIso),
      wholePlaneDualConfigurationHomeomorph η ∈ infiniteClusterEvent := by
  apply (configurationIsoLaw_ae_iff kstReflectionXIso μ _).mpr
  filter_upwards [hinfinite] with ω hω
  rw [wholePlaneDualConfiguration_reflectionX]
  apply (infiniteClusterEvent_translate_iff (-1,0) _).mpr
  exact (infiniteClusterEvent_configurationIso_iff kstReflectionXIso _).mpr hω

end
end PottsContinuity.PlanarTopology
