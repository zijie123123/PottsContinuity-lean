module

public import PottsContinuity.BD12.DRTWiredSourceDifferential
public import PottsContinuity.BD12.DRTMeanBetaMonotone
public import PottsContinuity.BD12.DRTStrictMean
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! A uniform strict upper bound for the actual finite wired one-arm sequence.
Both the domain comparison and the failure configuration are explicit. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section
open scoped Classical

/-- Increasing inverse temperature increases each actual wired one-arm mean. -/
theorem drtWiredOneArmMean_mono_beta (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β γ : Set.Ioi (0 : ℝ)) (hβγ : (β : ℝ) ≤ γ) (n : ℕ) :
    drtWiredOneArmMean q β n ≤ drtWiredOneArmMean q γ n :=
  drtMean_mono_beta _ q hq _ _ _
    (fun A => (finiteConnectionToSetIndicator_mem_Icc _ _ _ A).1)
    (finiteConnectionToSetIndicator_monotone _ _ _) β γ hβγ

/-- The empty configuration is a genuine failure for every positive radius. -/
theorem radiusOneArmIndicator_empty {V : Type*} [Fintype V] (G : SimpleGraph V)
    (r : V → ℕ) (o : V) (ho : r o = 0) (n : ℕ) (hn : 1 ≤ n) :
    radiusOneArmIndicator G r o n ∅ = 0 := by
  have hfail : ¬ ∃ b, b ∈ finiteRadiusShell r n ∧ FKC.FiniteFK.ActualConnected G ∅ o b := by
    rintro ⟨b, hb, hconn⟩
    have heq := (FKC.FiniteFK.actualConnected_empty G o b).mp hconn
    have hr := (mem_finiteRadiusShell r n b).mp hb
    rw [← heq, ho] at hr
    omega
  exact ite_eq_right hfail

/-- At every finite inverse temperature, the actual one-arm probability is below one. -/
theorem drtWiredOneArmMean_lt_one (q : Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ))
    (n : ℕ) (hn : 1 ≤ n) : drtWiredOneArmMean q β n < 1 := by
  apply drtMean_lt_one_of_exists_failure
  · intro A
    exact (finiteConnectionToSetIndicator_mem_Icc _ _ _ A).2
  · refine ⟨∅, ?_⟩
    exact (radiusOneArmIndicator_empty _ _ _ (boxGlobalRadius_center (0,0) _) n hn).trans_lt zero_lt_one

/-- Larger target radii and their larger wired domains are bounded by theta_1. -/
theorem drtWiredOneArmMean_le_one_scale (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β : Set.Ioi (0 : ℝ)) (n : ℕ) (hn : 1 ≤ n) :
    drtWiredOneArmMean q β n ≤ drtWiredOneArmMean q β 1 := by
  let H := boxGraph (0,0) (2*n)
  let ξ := BoundaryCondition.wired (boxVertexBoundary (0,0) (2*n))
  let J : H.edgeSet → Set.Ioi (0 : ℝ) := fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩
  have hanti := drt_radius_one_arm_antitone H q ξ J β (boxGlobalRadius (0,0) (2*n))
    (radiusBoxCenter (0,0) (2*n)) (boxGlobalRadius_center (0,0) _) (boxGlobalRadius_step (0,0) _)
  have hST : latticeBox (0,0) (2*1) ⊆ latticeBox (0,0) (2*n) := latticeBox_mono _ (by omega)
  have hcomp := drt_finite_wired_one_arm_mean_le q hq β hST (0,0) 1
    (latticeBox_mono _ (by omega : 1 ≤ 2*1)) (radiusBoxCenter (0,0) (2*1)) rfl
  exact (hanti hn).trans hcomp

/-- The bound is uniform throughout a bounded positive temperature interval. -/
theorem drtWiredOneArmMean_le_one_scale_upper (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β β₀ : Set.Ioi (0 : ℝ)) (hβ : (β : ℝ) ≤ β₀) (n : ℕ) (hn : 1 ≤ n) :
    drtWiredOneArmMean q β n ≤ drtWiredOneArmMean q β₀ 1 :=
  (drtWiredOneArmMean_le_one_scale q hq β n hn).trans
    (drtWiredOneArmMean_mono_beta q hq β β₀ hβ 1)

end
end PottsContinuity.BD12
