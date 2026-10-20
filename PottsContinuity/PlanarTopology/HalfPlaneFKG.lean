module

public import PottsContinuity.PlanarTopology.HalfPlaneEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite
noncomputable section

/-- Translation transports the literal marked infinite-root event. -/
theorem infiniteHit_translate_preimage (a : LatticeVertex) (S : Set LatticeVertex) :
    latticeConfigurationTranslate a ⁻¹' infiniteHit (latticeTranslate a '' S) = infiniteHit S := by
  ext ω
  constructor
  · rintro ⟨u,⟨v,hv,rfl⟩,hui⟩
    exact ⟨v,hv,(infiniteAt_translation a ω v).mp hui⟩
  · rintro ⟨u,hu,hui⟩
    exact ⟨latticeTranslate a u,⟨u,hu,rfl⟩,(infiniteAt_translation a ω u).mpr hui⟩

theorem measure_infiniteHit_translate (μ : Measure LatticeConfiguration)
    (a : LatticeVertex) (hμ : μ.map (latticeConfigurationTranslate a) = μ) (S : Set LatticeVertex) :
    μ (infiniteHit (latticeTranslate a '' S)) = μ (infiniteHit S) := by
  have hh := congrArg (fun ν : Measure LatticeConfiguration => ν (infiniteHit (latticeTranslate a '' S))) hμ
  rw [Measure.map_apply (latticeConfigurationTranslate_measurable a)
    (infiniteHit_measurableSet _),infiniteHit_translate_preimage] at hh
  exact hh.symm

end
end PottsContinuity.PlanarTopology
