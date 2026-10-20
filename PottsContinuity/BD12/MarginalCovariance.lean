module

public import PottsContinuity.BD12.ReindexedMarginal
public import PottsContinuity.BD12.PositiveMean
public import PottsContinuity.BD12.FiniteOSSS
public import Mathlib.Tactic

/-! Expectations, covariances and actual exploration OSSS transferred from a
true coordinate marginal to the original outer law. -/

@[expose] public section

namespace PottsContinuity.BD12
noncomputable section
variable {E F O : Type*} [Fintype E] [DecidableEq E]
    [Fintype F] [DecidableEq F] [Fintype O] [DecidableEq O]

theorem finitePartitionMarginalWeight_covariance (e : E ⊕ F ≃ O)
    (w : Finset O → Set.Ioi (0 : ℝ)) (f g : Finset E → ℝ) :
    finitePositiveCovariance (finitePartitionMarginalWeight e w) f g =
      finitePositiveCovariance w (fun C => f (finitePartitionProjection e C))
        (fun C => g (finitePartitionProjection e C)) := by
  unfold finitePositiveCovariance finitePositiveMean
  simp only [finitePartitionMarginalWeight_mean]

theorem finitePartitionMarginalWeight_edge_covariance (e : E ⊕ F ≃ O)
    (w : Finset O → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ) (a : E) :
    finitePositiveCovariance (finitePartitionMarginalWeight e w) f
        (fun A => if a ∈ A then 1 else 0) =
      finitePositiveCovariance w (fun C => f (finitePartitionProjection e C))
        (fun C => if e (Sum.inl a) ∈ C then 1 else 0) := by
  rw [finitePartitionMarginalWeight_covariance]
  simp only [finitePartitionProjection_mem]

end
end PottsContinuity.BD12
