module

public import PottsContinuity.PlanarTopology.HalfPlaneClusterEvents
public import PottsContinuity.PlanarTopology.HalfPlaneExitArch
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Int.Star
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite
noncomputable section

/-- The actual complementary-dual exit and local-uniqueness probabilities
bound the probability that both primal boundary roots have finite components. -/
theorem halfPlane_screen_probability_lower_bound_of_dualLaw
    (μ ν : Measure LatticeConfiguration) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : μ.map wholePlaneDualConfigurationHomeomorph = ν)
    (S T U : Set LatticeVertex) (hSU : S ⊆ U) (hTU : T ⊆ U) :
    ν.real (halfPlaneExitEvent S {y : ℤ | y ≤ -1}) +
      ν.real (halfPlaneExitEvent T {y : ℤ | 1 ≤ y}) +
      ν.real (halfPlaneLocalUniquenessEvent U) - 2 ≤ μ.real halfPlaneFiniteUnitEvent := by
  let L := halfPlaneExitEvent S {y : ℤ | y ≤ -1}
  let R := halfPlaneExitEvent T {y : ℤ | 1 ≤ y}
  let A := halfPlaneLocalUniquenessEvent U
  have hR : MeasurableSet R := halfPlaneExitEvent_measurableSet _ _
  have hA : MeasurableSet A := halfPlaneLocalUniquenessEvent_measurableSet _
  have hE : MeasurableSet ((L ∩ R) ∩ A) :=
    ((halfPlaneExitEvent_measurableSet _ _).inter hR).inter hA
  have hsub : wholePlaneDualConfigurationHomeomorph ⁻¹' ((L ∩ R) ∩ A) ⊆
      halfPlaneFiniteUnitEvent := by
    intro ω hω
    exact (mem_halfPlaneFiniteUnitEvent_iff ω).mpr
      (opposite_dual_first_exits_screen_unit_segment ω S T U hSU hTU hω.1.1 hω.1.2 hω.2)
  have hmono := measureReal_mono (μ := μ) hsub
  have hmap : ν.real ((L ∩ R) ∩ A) =
      μ.real (wholePlaneDualConfigurationHomeomorph ⁻¹' ((L ∩ R) ∩ A)) := by
    rw [← hν,Measure.real_def,Measure.map_apply wholePlaneDualConfigurationHomeomorph_measurable hE]
    rfl
  have h₁ := measureReal_union_add_inter (μ := ν) (s := L) hR
  have h₂ := measureReal_union_add_inter (μ := ν) (s := L ∩ R) hA
  have hu₁ : ν.real (L ∪ R) ≤ 1 := measureReal_le_one
  have hu₂ : ν.real ((L ∩ R) ∪ A) ≤ 1 := measureReal_le_one
  change ν.real L + ν.real R + ν.real A - 2 ≤ _
  linarith

end
end PottsContinuity.PlanarTopology
