module

public import PottsContinuity.BD12.DRTFiniteLaw
public import PottsContinuity.BD12.DRTRussoCorrection

/-! The corrected weighted finite-graph Russo identity, expanded edge by edge. -/

@[expose] public section

namespace PottsContinuity.BD12

open PD.FK
open scoped BigOperators
noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance drtRussoEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _

/-- Actual sampled open-edge indicator. Boundary identifications do not enter. -/
def drtEdgeIndicator (e : G.edgeSet) (A : Configuration G) : ℝ := by
  classical
  exact if e ∈ A then 1 else 0

theorem drtMean_sum {ι : Type*} [Fintype ι] (q : Set.Ioi (0 : ℝ))
    (ξ : BoundaryCondition V) (J : G.edgeSet → Set.Ioi (0 : ℝ))
    (β : Set.Ioi (0 : ℝ)) (f : ι → Configuration G → ℝ) :
    drtMean G q ξ J β (fun A => ∑ i, f i A) = ∑ i, drtMean G q ξ J β (f i) := by
  simp only [drtMean, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_div]

theorem drtMean_const_mul (q : Set.Ioi (0 : ℝ))
    (ξ : BoundaryCondition V) (J : G.edgeSet → Set.Ioi (0 : ℝ))
    (β : Set.Ioi (0 : ℝ)) (c : ℝ) (f : Configuration G → ℝ) :
    drtMean G q ξ J β (fun A => c * f A) = c * drtMean G q ξ J β f := by
  unfold drtMean
  have hsum : (∑ A, drtWeight G q ξ J β A * (c * f A)) =
      c * ∑ A, drtWeight G q ξ J β A * f A := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    ring
  rw [hsum]
  ring

theorem drtCovariance_snd_sum {ι : Type*} [Fintype ι] (q : Set.Ioi (0 : ℝ))
    (ξ : BoundaryCondition V) (J : G.edgeSet → Set.Ioi (0 : ℝ))
    (β : Set.Ioi (0 : ℝ)) (f : Configuration G → ℝ)
    (g : ι → Configuration G → ℝ) :
    drtCovariance G q ξ J β f (fun A => ∑ i, g i A) =
      ∑ i, drtCovariance G q ξ J β f (g i) := by
  simp only [drtCovariance, Finset.mul_sum, drtMean_sum, Finset.sum_sub_distrib]

theorem drtCovariance_snd_const_mul (q : Set.Ioi (0 : ℝ))
    (ξ : BoundaryCondition V) (J : G.edgeSet → Set.Ioi (0 : ℝ))
    (β : Set.Ioi (0 : ℝ)) (f g : Configuration G → ℝ) (c : ℝ) :
    drtCovariance G q ξ J β f (fun A => c * g A) =
      c * drtCovariance G q ξ J β f g := by
  have heq : (fun A => f A * (c * g A)) = (fun A => c * (f A * g A)) := by
    funext A
    ring
  unfold drtCovariance
  rw [heq, drtMean_const_mul, drtMean_const_mul]
  ring

theorem drtScore_eq_sum_indicators (J : G.edgeSet → Set.Ioi (0 : ℝ))
    (β : Set.Ioi (0 : ℝ)) (A : Configuration G) :
    (∑ e ∈ A, drtEdgeScore G J β e) =
      ∑ e : G.edgeSet, drtEdgeScore G J β e * drtEdgeIndicator G e A := by
  classical
  calc
    _ = ∑ e ∈ A, drtEdgeScore G J β e * drtEdgeIndicator G e A := by
      apply Finset.sum_congr rfl
      intro e he
      simp only [drtEdgeIndicator, ite_eq_left he, mul_one]
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ A)
      intro e _ he
      simp only [drtEdgeIndicator, ite_eq_right he, mul_zero]

/-- Weighted finite-volume Russo formula with the accepted corrected
coefficient J_e exp(beta J_e)/(exp(beta J_e)-1), for every real observable. -/
theorem drt_russo_corrected (q : Set.Ioi (0 : ℝ))
    (ξ : BoundaryCondition V) (J : G.edgeSet → Set.Ioi (0 : ℝ))
    (β : Set.Ioi (0 : ℝ)) (f : Configuration G → ℝ) :
    HasDerivAt
      (fun t : ℝ => (∑ A, drtWeight G q ξ J t A * f A) /
        ∑ A, drtWeight G q ξ J t A)
      (∑ e : G.edgeSet, drtEdgeScore G J β e *
        drtCovariance G q ξ J β f (drtEdgeIndicator G e)) β := by
  have h := drtMean_hasDerivAt_score_corrected G q ξ J β f
  have hscore : (fun A => ∑ e ∈ A, drtEdgeScore G J β e) =
      (fun A => ∑ e : G.edgeSet, drtEdgeScore G J β e * drtEdgeIndicator G e A) :=
    funext (drtScore_eq_sum_indicators G J β)
  rw [hscore, drtCovariance_snd_sum] at h
  simp_rw [drtCovariance_snd_const_mul] at h
  exact h

/-- The source's smaller coefficient remains a valid lower bound whenever
the edge covariances are nonnegative. FKG discharges this premise separately. -/
theorem drt_russo_lower_bound_of_covariance_nonneg (q : Set.Ioi (0 : ℝ))
    (ξ : BoundaryCondition V) (J : G.edgeSet → Set.Ioi (0 : ℝ))
    (β : Set.Ioi (0 : ℝ)) (f : Configuration G → ℝ)
    (hcov : ∀ e : G.edgeSet, 0 ≤ drtCovariance G q ξ J β f (drtEdgeIndicator G e)) :
    (∑ e : G.edgeSet, ((J e : ℝ) / (Real.exp ((β : ℝ) * (J e : ℝ)) - 1)) *
      drtCovariance G q ξ J β f (drtEdgeIndicator G e)) ≤
    deriv (fun t : ℝ => (∑ A, drtWeight G q ξ J t A * f A) /
      ∑ A, drtWeight G q ξ J t A) β := by
  rw [(drt_russo_corrected G q ξ J β f).deriv]
  apply Finset.sum_le_sum
  intro e _
  exact drt_russo_coefficient_lower_bound β (J e)
    (drtCovariance G q ξ J β f (drtEdgeIndicator G e)) β.property (J e).property (hcov e)

end
end PottsContinuity.BD12
