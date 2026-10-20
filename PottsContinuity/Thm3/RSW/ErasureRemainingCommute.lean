module

public import PottsContinuity.Thm3.RSW.InducedConfiguration
public import PottsContinuity.PD.FK.EdgeRestriction
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- Closing bonds outside a fixed vertex set commutes with inclusion of the
remaining sampled graph into the original graph, on the full original carrier. -/
theorem edgeRestrictionConfigurationEquiv_inducedErasure
    {Y : Type*} [Finite Y] (H : SimpleGraph Y) (R : Configuration H) (W : Set Y)
    (A : Configuration (edgeRestriction H R)) :
    (edgeRestrictionConfigurationEquiv H R (inducedConfigurationErasure W A)).val =
      inducedConfigurationErasure W (edgeRestrictionConfigurationEquiv H R A).val := by
  classical
  rw [edgeRestrictionConfigurationEquiv_val,edgeRestrictionConfigurationEquiv_val]
  ext e
  constructor
  · intro he
    obtain ⟨d,hd,rfl⟩ := Finset.mem_map.mp he
    obtain ⟨hdA,hW⟩ := (mem_inducedConfigurationErasure W A d).mp hd
    apply (mem_inducedConfigurationErasure W _ _).mpr
    exact ⟨Finset.mem_map.mpr ⟨d,hdA,rfl⟩,by
      simpa only [edgeRestrictionEdgeEmbedding_coe] using hW⟩
  · intro he
    obtain ⟨heA,hW⟩ := (mem_inducedConfigurationErasure W _ e).mp he
    obtain ⟨d,hdA,rfl⟩ := Finset.mem_map.mp heA
    apply Finset.mem_map.mpr
    refine ⟨d,(mem_inducedConfigurationErasure W A d).mpr ⟨hdA,?_⟩,rfl⟩
    simpa only [edgeRestrictionEdgeEmbedding_coe] using hW

end
end PottsContinuity.RSW
