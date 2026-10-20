module

public import PottsContinuity.Thm3.RSW.FiniteDualRectangleEmpty

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The empty side sample supplies an actual source crossing at every
positive scale, including the single-row dual bands at scale one. -/
theorem empty_mem_lemma4SideReferenceEvent (n : ℕ) (hn : 1 ≤ n) (i : Fin 2) :
    (∅ : Configuration (lemma4SideResidualGraph n (lemma4SideSign i))) ∈
      lemma4SideReferenceEvent n i := by
  change (edgeRestrictionConfigurationEquiv (lemma4AmbientGraph n) (lemma4MiddleReveal n)
    (inducedConfigurationExtension (lemma4SideVertices n (lemma4SideSign i)) ∅)).val ∈
      lemma4DualBandEvent n i
  simp only [inducedConfigurationExtension,embeddedConfigurationEmbedding_eq_map,
    Finset.map_empty,edgeRestrictionConfigurationEquiv_val]
  refine Fin.cases ?_ (fun j => ?_) i
  · exact empty_mem_finiteClosedDualHorizontalRectangle _ _ _ _ _ (by omega) (by omega)
  · exact empty_mem_finiteClosedDualHorizontalRectangle _ _ _ _ _ (by omega) (by omega)

/-- Every literal finite side-reference crossing has positive probability
at all positive scales and all admissible parameters, independently of q. -/
theorem lemma4SideReferenceProbability_pos (θ : Parameters) (n : ℕ) (hn : 1 ≤ n) (i : Fin 2) :
    0 < lemma4SideReferenceProbability θ n i := by
  rw [lemma4SideReferenceProbability,ENNReal.toReal_pos_iff]
  refine ⟨?_,measure_lt_top _ _⟩
  exact (measure_pos_iff (lemma4SideResidualGraph n (lemma4SideSign i)) θ _ _).mpr ⟨∅,empty_mem_lemma4SideReferenceEvent n hn i⟩

end
end PottsContinuity.RSW
