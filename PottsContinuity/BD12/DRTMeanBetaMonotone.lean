module

public import PottsContinuity.BD12.DRTAssociation
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! Monotonicity in inverse temperature for increasing finite observables,
derived from the actual corrected derivative and finite positive association. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance betaMonoEdges : Fintype G.edgeSet := Fintype.ofFinite _
local instance betaMonoEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Increasing nonnegative finite observables have increasing actual beta-means. -/
theorem drtMean_mono_beta (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (ξ : BoundaryCondition V) (J : G.edgeSet → Set.Ioi (0 : ℝ))
    (f : Configuration G → ℝ) (hf0 : ∀ A, 0 ≤ f A) (hf : Monotone f)
    (β γ : Set.Ioi (0 : ℝ)) (hβγ : (β : ℝ) ≤ γ) :
    drtMean G q ξ J β f ≤ drtMean G q ξ J γ f := by
  let F := fun t : ℝ => (∑ A, drtWeight G q ξ J t A * f A) / ∑ A, drtWeight G q ξ J t A
  have hD (x : ℝ) (hx : 0 < x) := drtMean_hasDerivAt_score_corrected G q ξ J ⟨x,hx⟩ f
  have hcov (x : ℝ) (hx : 0 < x) :
      0 ≤ drtCovariance G q ξ J ⟨x,hx⟩ f (fun A => ∑ e ∈ A, drtEdgeScore G J ⟨x,hx⟩ e) := by
    refine drtCovariance_nonneg G q hq ξ J ⟨x,hx⟩ f _ hf0 ?_ hf ?_
    · intro A
      exact Finset.sum_nonneg (fun e _ => (drtEdgeScore_pos G J ⟨x,hx⟩ e).le)
    · intro A B hAB
      exact Finset.sum_le_sum_of_subset_of_nonneg hAB
        (fun e _ _ => (drtEdgeScore_pos G J ⟨x,hx⟩ e).le)
  have hcont : ContinuousOn F (Set.Icc (β : ℝ) γ) := by
    intro x hx
    exact (hD x (β.property.trans_le hx.1)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ F (interior (Set.Icc (β : ℝ) γ)) := by
    rw [interior_Icc]
    intro x hx
    exact (hD x (β.property.trans hx.1)).differentiableAt.differentiableWithinAt
  have hm : MonotoneOn F (Set.Icc (β : ℝ) γ) :=
    monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont hdiff (by
      rw [interior_Icc]
      intro x hx
      rw [(hD x (β.property.trans hx.1)).deriv]
      exact hcov x (β.property.trans hx.1))
  exact hm ⟨le_rfl,hβγ⟩ ⟨hβγ,le_rfl⟩ hβγ

end
end PottsContinuity.BD12
