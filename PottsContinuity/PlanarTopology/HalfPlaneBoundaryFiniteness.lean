module

public import PottsContinuity.PlanarTopology.HalfPlaneScreenAlmostSure
public import PottsContinuity.PlanarTopology.DualConfigurationTranslation
public import PottsContinuity.PlanarTopology.DualLawAssociation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.MetricSpace.Polish

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite
noncomputable section

/-- The actual dual homeomorphism transports almost-sure predicates in both directions. -/
theorem wholePlaneDualLaw_ae_iff (μ : Measure LatticeConfiguration) (P : LatticeConfiguration → Prop) :
    (∀ᵐ η ∂μ.map wholePlaneDualConfigurationHomeomorph, P η) ↔
      ∀ᵐ ω ∂μ, P (wholePlaneDualConfigurationHomeomorph ω) := by
  have hh := wholePlaneDualConfigurationHomeomorph.toMeasurableEquiv.map_ae μ
  simp only [Homeomorph.toMeasurableEquiv_coe] at hh
  rw [← hh]
  rfl

/-- A translation-invariant positively associated law whose actual dual has
one existing infinite cluster almost surely has finite primal boundary components. -/
theorem halfPlane_finite_unit_ae
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hinfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent) :
    ∀ᵐ ω ∂μ, ω ∈ halfPlaneFiniteUnitEvent := by
  apply halfPlane_finite_unit_ae_of_dualLaw μ (μ.map wholePlaneDualConfigurationHomeomorph) rfl
  · exact wholePlaneDualLaw_translation_invariant μ htranslation
  · exact wholePlaneDualLaw_FKG μ hFKG
  · exact (wholePlaneDualLaw_ae_iff μ _).mpr hunique
  · exact (wholePlaneDualLaw_ae_iff μ _).mpr hinfinite

end
end PottsContinuity.PlanarTopology
