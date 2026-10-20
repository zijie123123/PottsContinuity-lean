module

public import PottsContinuity.Thm3.RSW.Lemma4SideResidualDeletion
public import PottsContinuity.PD.FK.Isomorphism

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- The identity on every original side vertex identifies the two descriptions
of the residual graph. No vertex, including an isolated one, is removed. -/
def lemma4SideDeletionIso (n : ℕ) (σ : ℤ) :
    lemma4SideResidualGraph n σ ≃g
      edgeRestriction (lemma4SideFullGraph n σ) (lemma4SideBaseReveal n σ) where
  toEquiv := Equiv.refl _
  map_rel_iff' := by
    intro u v
    exact Iff.of_eq (congrArg (fun G => G.Adj u v)
      (lemma4SideResidualGraph_eq_delete_base n σ)).symm

/-- The sampled residual configuration, with precisely its original edge
labels, as a remaining configuration of the full side rectangle. -/
def lemma4SideRemainingEquiv (n : ℕ) (σ : ℤ) :
    Configuration (lemma4SideResidualGraph n σ) ≃
      RemainingConfiguration (lemma4SideFullGraph n σ) (lemma4SideBaseReveal n σ) :=
  (configurationIso (lemma4SideDeletionIso n σ)).trans
    (edgeRestrictionConfigurationEquiv (lemma4SideFullGraph n σ) (lemma4SideBaseReveal n σ))

/-- The reference residual FK law is exactly the marginal of the full side
rectangle with the base wired. Only independent prewired bonds are forgotten. -/
theorem lemma4SideReference_law_eq_fullSide_marginal (θ : Parameters)
    (n : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    (law (lemma4SideResidualGraph n σ) θ
      (BoundaryCondition.wired (lemma4SideBase n σ))).map (lemma4SideRemainingEquiv n σ) =
    (law (lemma4SideFullGraph n σ) θ
      (BoundaryCondition.wired (lemma4SideBase n σ))).map
      (fun C => (configurationSplitEquiv (lemma4SideFullGraph n σ)
        (lemma4SideBaseReveal n σ) C).1) := by
  classical
  rw [law_map_remove _ θ _ _ (lemma4SideBaseReveal_prewired n σ hσ)]
  change (law _ θ _).map
    ((edgeRestrictionConfigurationEquiv _ _) ∘ (configurationIso (lemma4SideDeletionIso n σ))) = _
  rw [← PMF.map_comp,law_configurationIso_map]
  have hξ : (boundaryConditionIso (lemma4SideDeletionIso n σ)
      (BoundaryCondition.wired (lemma4SideBase n σ))).partition =
      (BoundaryCondition.wired (lemma4SideBase n σ)).partition := rfl
  rw [law_eq_of_boundary_partition_eq θ _ _ hξ]
  exact law_edgeRestriction_map _ θ _ _

end
end PottsContinuity.RSW
