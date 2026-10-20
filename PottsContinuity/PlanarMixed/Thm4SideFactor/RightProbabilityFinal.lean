module

public import PottsContinuity.PlanarMixed.Thm4SideFactor.RightProbability
public import PottsContinuity.PlanarMixed.Thm4SideFactor.RightBoundaryComparison
public import PottsContinuity.PlanarMixed.Thm4SideFactor.RightCrossingTransport

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open MeasureTheory PD.FK Thm4Side
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

theorem nativeSideReduced_probability_le_rightResidual
    (q : Set.Icc (1 : ℝ) 4) (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    (measure (nativeSideReducedGraph m) (RSW.selfDualParameters (⟨q,q.2.1⟩ : Set.Ici (1:ℝ)))
      (nativeSideFullBoundary m) (nativeSideReducedCrossingEvent m)).toReal ≤
        slitRightResidualCrossingProbability q m X := by
  apply nativeSideReduced_probability_le_rightResidual_of_boundary_and_surgery q m hm X
  · exact right_native_further_boundary_le m X
  · intro D hD
    let H : RemovedConfiguration (FKC.FiniteFK.slitBoxGraph (16*m))
        (slitRightDualRectangleReveal m X) := ⟨X ∩ slitRightDualRectangleReveal m X,Finset.inter_subset_right⟩
    let Y := (configurationSplitEquiv (FKC.FiniteFK.slitBoxGraph (16*m))
      (slitRightDualRectangleReveal m X)).symm (D,H)
    have hsplit : (configurationSplitEquiv (FKC.FiniteFK.slitBoxGraph (16*m))
        (slitRightDualRectangleReveal m X) Y).1 = D :=
      congrArg Prod.fst ((configurationSplitEquiv (FKC.FiniteFK.slitBoxGraph (16*m))
        (slitRightDualRectangleReveal m X)).apply_symm_apply (D,H))
    have hread : rightNativeRemainingRead m hm X D ∈ nativeSideReducedCrossingEvent m := hD
    have htransport := rightNative_crossing_implies_source_screen m hm X Y
    have hproof : Y ∈ FKC.FiniteFK.slitScreenRightCrossingEvent m := by
      apply htransport
      rw [hsplit]
      exact hread
    convert hproof using 1
    congr 1
    congr 1; exact Subsingleton.elim _ _
    all_goals
      dsimp only [H,slitRightDualRectangleReveal]
      congr 1; (congr 1; exact Subsingleton.elim _ _)

theorem rightResidual_crossing_uniform_pos (q : Set.Icc (1 : ℝ) 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
      ∀ X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)),
        c ≤ slitRightResidualCrossingProbability q m X := by
  obtain ⟨c,hc,hbound⟩ := nativeSideReduced_crossing_uniform_pos
    (⟨q,q.2.1⟩ : Set.Ici (1:ℝ))
  exact ⟨c,hc,fun m hm X => (hbound m hm).trans
    (nativeSideReduced_probability_le_rightResidual q m hm X)⟩

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
