module

public import PottsContinuity.Thm3.RSW.Lemma4SideRemovalEvent
public import PottsContinuity.Thm3.RSW.Lemma4BandProduct

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Deleting precisely the observed base bonds maps the full side law to the
accepted residual reference law, with its original sampled configuration type. -/
theorem lemma4SideFull_law_map_reference (θ : Parameters) (n : ℕ) (σ : ℤ)
    (hσ : σ = 1 ∨ σ = -1) :
    (law (lemma4SideFullGraph n σ) θ
      (BoundaryCondition.wired (lemma4SideBase n σ))).map
      (fun C => (lemma4SideRemainingEquiv n σ).symm
        (configurationSplitEquiv (lemma4SideFullGraph n σ)
          (lemma4SideBaseReveal n σ) C).1) =
    law (lemma4SideResidualGraph n σ) θ
      (BoundaryCondition.wired (lemma4SideBase n σ)) := by
  change (law _ θ _).map ((lemma4SideRemainingEquiv n σ).symm ∘
    (fun C => (configurationSplitEquiv (lemma4SideFullGraph n σ)
      (lemma4SideBaseReveal n σ) C).1)) = _
  rw [← PMF.map_comp,← lemma4SideReference_law_eq_fullSide_marginal θ n σ hσ,
    PMF.map_comp]
  change (law _ θ _).map (fun C =>
    (lemma4SideRemainingEquiv n σ).symm (lemma4SideRemainingEquiv n σ C)) = _
  simp only [Equiv.symm_apply_apply]
  exact PMF.map_id _

/-- The actual source side-reference crossing probability equals the literal
original band crossing under the full side rectangle with its base wired.
There is no finite dual-law or uniform crossing estimate in the premises. -/
theorem lemma4SideReferenceProbability_eq_fullSide (θ : Parameters) (n : ℕ) (i : Fin 2) :
    lemma4SideReferenceProbability θ n i =
    (measure (lemma4SideFullGraph n (lemma4SideSign i)) θ
      (BoundaryCondition.wired (lemma4SideBase n (lemma4SideSign i)))
      {C | inducedConfigurationExtension (lemma4SideVertices n (lemma4SideSign i)) C ∈
        lemma4DualBandEvent n i}).toReal := by
  have hlaw := lemma4SideFull_law_map_reference θ n (lemma4SideSign i) (lemma4SideSign_eq_one_or_neg_one i)
  have hset : (fun C => (lemma4SideRemainingEquiv n (lemma4SideSign i)).symm
      (configurationSplitEquiv (lemma4SideFullGraph n (lemma4SideSign i))
        (lemma4SideBaseReveal n (lemma4SideSign i)) C).1) ⁻¹' lemma4SideReferenceEvent n i =
      {C | inducedConfigurationExtension (lemma4SideVertices n (lemma4SideSign i)) C ∈
        lemma4DualBandEvent n i} := by
    ext C
    exact (lemma4SideFull_band_restore_iff n i C).symm
  unfold lemma4SideReferenceProbability PD.FK.measure
  rw [← hlaw,PMF.toMeasure_map_apply _ _ _ measurable_from_top
    MeasurableSpace.measurableSet_top,hset]

end
end PottsContinuity.RSW
