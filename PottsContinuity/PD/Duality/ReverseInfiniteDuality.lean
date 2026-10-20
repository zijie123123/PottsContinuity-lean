-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Duality/ReverseInfiniteDuality.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import TauCeti.Topology.Circle.Degree
public import PottsContinuity.PD.Duality.FreeAssociation
public import PottsContinuity.PD.Duality.InfiniteDuality
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.Map

/-! Applying the planar dual transform twice translates face-base coordinates.
Translation invariance therefore also gives wired-to-free infinite-volume duality. -/

@[expose] public section

namespace PottsContinuity.PD.Duality
open FK FK.Medial MeasureTheory
noncomputable section

lemma dualConfiguration_twice (ω : LatticeConfiguration) :
    wholePlaneDualConfigurationHomeomorph (wholePlaneDualConfigurationHomeomorph ω) =
      latticeConfigurationIsoHomeomorph (latticeTranslationIso (-1,-1)) ω := by
  funext e
  obtain ⟨b, rfl⟩ := wholePlaneBondEdgeEquiv.surjective e
  change latticeConfigurationBondState
    (wholePlaneDualConfigurationHomeomorph (wholePlaneDualConfigurationHomeomorph ω)) b = _
  rw [wholePlaneDualConfigurationHomeomorph_bondState,
    wholePlaneDualConfigurationHomeomorph_bondState]
  simp only [Bool.not_not, latticeConfigurationBondState,
    latticeConfigurationIsoHomeomorph_apply]
  congr 1
  apply Subtype.ext
  rcases b with ⟨⟨x,y⟩, ax⟩
  cases ax <;>
    simp [primalBondOfDual, wholePlaneBondEdgeEquiv, latticeBondEdge, LatticeBond.toSym2, LatticeBond.source,
      LatticeBond.target, SimpleGraph.Iso.mapEdgeSet_apply, SimpleGraph.Hom.mapEdgeSet_coe,
      latticeTranslationIso, latticeTranslate]

/-- The wired measure at p* maps to the free measure at p under the actual dual
transform. Its square is the harmless lattice translation (-1,-1). -/
theorem wired_map_dual_eq_free (θ : Parameters)
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (dualParameters θ).toP (dualParameters θ).toQ 1 μ₁) :
    μ₁.map wholePlaneDualConfigurationHomeomorph = μ₀ := by
  rw [← free_map_dual_eq_wired θ μ₀ μ₁ hμ₀ hμ₁,
    Measure.map_map wholePlaneDualConfigurationHomeomorph_measurable
      wholePlaneDualConfigurationHomeomorph_measurable]
  have heq : (wholePlaneDualConfigurationHomeomorph ∘ wholePlaneDualConfigurationHomeomorph) =
      latticeConfigurationIsoHomeomorph (latticeTranslationIso (-1,-1)) :=
    funext dualConfiguration_twice
  rw [heq]
  exact free_limit_map_latticeIso θ μ₀ hμ₀ (latticeTranslationIso (-1,-1))
    (fun c v r => mem_latticeBox_translate_iff (-1,-1) c v r)

end
end PottsContinuity.PD.Duality
