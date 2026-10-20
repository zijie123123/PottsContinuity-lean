module

public import PottsContinuity.PD.Duality.WholePlaneDualConfiguration
public import PottsContinuity.PD.RCInfinite.EdgeErgodicity
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite
noncomputable section

/-- Translation reads the old state of the same normalized bond translated back. -/
theorem latticeConfigurationBondState_translate (a : LatticeVertex) (ω : LatticeConfiguration)
    (b : LatticeBond) :
    latticeConfigurationBondState (edgeTranslate a ω) b =
      latticeConfigurationBondState ω ⟨latticeTranslate (-a) b.base,b.axis⟩ := by
  change latticeConfigurationTranslate a ω (latticeBondEdge b) = _
  rw [latticeConfigurationTranslate_apply]
  apply congrArg ω
  apply Subtype.ext
  rcases b with ⟨⟨x,y⟩,ax⟩
  cases ax <;>
    simp [SimpleGraph.Iso.mapEdgeSet,SimpleGraph.Hom.mapEdgeSet,latticeBondEdge,
      LatticeBond.toSym2,LatticeBond.source,LatticeBond.target,latticeTranslationIso,latticeTranslate,add_assoc,add_comm,add_left_comm]

/-- Crossing-bond duality commutes with every actual lattice translation. -/
theorem wholePlaneDualConfiguration_translate (a : LatticeVertex) (ω : LatticeConfiguration) :
    wholePlaneDualConfigurationHomeomorph (edgeTranslate a ω) =
      edgeTranslate a (wholePlaneDualConfigurationHomeomorph ω) := by
  funext e
  obtain ⟨b,rfl⟩ := wholePlaneBondEdgeEquiv.surjective e
  change latticeConfigurationBondState (wholePlaneDualConfigurationHomeomorph (edgeTranslate a ω)) b =
    latticeConfigurationBondState (edgeTranslate a (wholePlaneDualConfigurationHomeomorph ω)) b
  rw [wholePlaneDualConfigurationHomeomorph_bondState,latticeConfigurationBondState_translate,
    latticeConfigurationBondState_translate,wholePlaneDualConfigurationHomeomorph_bondState]
  congr 2
  rcases b with ⟨⟨x,y⟩,ax⟩
  cases ax <;> simp [primalBondOfDual,latticeTranslate,add_assoc,add_comm,add_left_comm]

/-- The actual complementary-dual pushforward inherits translation invariance. -/
theorem wholePlaneDualLaw_translation_invariant
    (μ : Measure LatticeConfiguration)
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (a : LatticeVertex) :
    (μ.map wholePlaneDualConfigurationHomeomorph).map (edgeTranslate a) =
      μ.map wholePlaneDualConfigurationHomeomorph := by
  rw [Measure.map_map (edgeTranslate_measurable _) wholePlaneDualConfigurationHomeomorph_measurable]
  have hcomm : (edgeTranslate a) ∘ wholePlaneDualConfigurationHomeomorph =
      wholePlaneDualConfigurationHomeomorph ∘ (edgeTranslate a) := by
    funext ω
    exact (wholePlaneDualConfiguration_translate a ω).symm
  rw [hcomm,← Measure.map_map wholePlaneDualConfigurationHomeomorph_measurable (edgeTranslate_measurable _),
    htranslation]

end
end PottsContinuity.PlanarTopology
