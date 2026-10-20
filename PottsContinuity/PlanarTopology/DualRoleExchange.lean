module

public import PottsContinuity.PlanarTopology.HalfPlaneNonpercolation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite
noncomputable section

/-- The face-base convention makes the square of actual crossing-bond
complementation the fixed lattice translation by (-1,-1). -/
theorem wholePlaneDualConfiguration_twice (ω : LatticeConfiguration) :
    wholePlaneDualConfigurationHomeomorph (wholePlaneDualConfigurationHomeomorph ω) =
      edgeTranslate (-1,-1) ω := by
  funext e
  obtain ⟨b,rfl⟩ := wholePlaneBondEdgeEquiv.surjective e
  change latticeConfigurationBondState
    (wholePlaneDualConfigurationHomeomorph (wholePlaneDualConfigurationHomeomorph ω)) b =
      latticeConfigurationBondState (edgeTranslate (-1,-1) ω) b
  rw [wholePlaneDualConfigurationHomeomorph_bondState,wholePlaneDualConfigurationHomeomorph_bondState,
    Bool.not_not,latticeConfigurationBondState_translate]
  congr 1
  rcases b with ⟨⟨x,y⟩,ax⟩
  cases ax <;> simp [primalBondOfDual,latticeTranslate]

/-- For an invariant law the second actual dual pushforward is the original law. -/
theorem wholePlaneDualLaw_twice (μ : Measure LatticeConfiguration)
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ) :
    (μ.map wholePlaneDualConfigurationHomeomorph).map wholePlaneDualConfigurationHomeomorph = μ := by
  rw [Measure.map_map wholePlaneDualConfigurationHomeomorph_measurable wholePlaneDualConfigurationHomeomorph_measurable]
  have heq : wholePlaneDualConfigurationHomeomorph ∘ wholePlaneDualConfigurationHomeomorph =
      edgeTranslate (-1,-1) := funext wholePlaneDualConfiguration_twice
  rw [heq,htranslation]

end
end PottsContinuity.PlanarTopology
