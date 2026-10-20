module

public import PottsContinuity.BD12.DRTPressureDerivative
public import PottsContinuity.BD12.DRTMeanBetaMonotone
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! Log edge activity parametrizes all physical homogeneous temperatures. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK
open scoped BigOperators
noncomputable section

/-- Inverse temperature corresponding to edge activity exp(s), for every real s. -/
def drtLogActivityTemperature (s : ℝ) : Set.Ioi (0 : ℝ) :=
  ⟨Real.log (1 + Real.exp s), Real.log_pos (by linarith only [Real.exp_pos s])⟩

@[simp] theorem exp_drtLogActivityTemperature (s : ℝ) :
    Real.exp (drtLogActivityTemperature s : ℝ) = 1 + Real.exp s :=
  Real.exp_log (by linarith only [Real.exp_pos s])

theorem drtLogActivityTemperature_monotone :
    Monotone (fun s : ℝ => (drtLogActivityTemperature s : ℝ)) := by
  intro s t hst
  exact Real.log_le_log (by linarith only [Real.exp_pos s])
    (add_le_add le_rfl (Real.exp_le_exp.mpr hst))

theorem drtLogActivityTemperature_hasDerivAt (s : ℝ) :
    HasDerivAt (fun t : ℝ => (drtLogActivityTemperature t : ℝ))
      (Real.exp s / (1 + Real.exp s)) s := by
  exact ((Real.hasDerivAt_exp s).const_add 1).log
    (by linarith only [Real.exp_pos s])

variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance logActivityEdges : Fintype G.edgeSet := Fintype.ofFinite _

/-- The actual homogeneous finite FK log partition in log edge activity. -/
def drtActivityLogPartition (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition V)
    (s : ℝ) : ℝ :=
  Real.log (∑ A, drtWeight G q ξ
    (fun _ => ⟨(1 : ℝ), (show (0 : ℝ) < 1 from one_pos)⟩)
    (drtLogActivityTemperature s) A)

/-- Expected number of sampled open edges under that physical finite law. -/
def drtActivityEdgeSum (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition V)
    (s : ℝ) : ℝ :=
  ∑ e : G.edgeSet, drtMean G q ξ
    (fun _ => ⟨(1 : ℝ), (show (0 : ℝ) < 1 from one_pos)⟩)
    (drtLogActivityTemperature s) (drtEdgeIndicator G e)

/-- In log activity the common corrected score cancels the temperature derivative. -/
theorem drtActivityLogPartition_hasDerivAt (q : Set.Ioi (0 : ℝ))
    (ξ : BoundaryCondition V) (s : ℝ) :
    HasDerivAt (drtActivityLogPartition G q ξ) (drtActivityEdgeSum G q ξ s) s := by
  have h := (drtLogPartition_homogeneous_hasDerivAt G q ξ
    (drtLogActivityTemperature s)).comp s (drtLogActivityTemperature_hasDerivAt s)
  have he : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
  have he1 : 1 + Real.exp s ≠ 0 := by linarith only [Real.exp_pos s]
  convert h using 1
  · rfl
  · dsimp only [drtActivityEdgeSum]
    rw [exp_drtLogActivityTemperature]
    field_simp;
    ring

/-- The expected edge count increases with log activity, for all real q>=1. -/
theorem drtActivityEdgeSum_monotone (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (ξ : BoundaryCondition V) : Monotone (drtActivityEdgeSum G q ξ) := by
  intro s t hst
  apply Finset.sum_le_sum
  intro e _
  exact drtMean_mono_beta G q hq ξ _ (drtEdgeIndicator G e)
    (drtEdgeIndicator_nonneg G e) (drtEdgeIndicator_monotone G e)
    _ _ (drtLogActivityTemperature_monotone hst)

end
end PottsContinuity.BD12
