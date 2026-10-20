module

public import PottsContinuity.BD12.BoxOneArmTranslation
public import PottsContinuity.BD12.DRTBoxHomogeneous
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-! The actual finite wired one-arm sequence and its source partial sums.
Inverse temperature is positive on the whole declared parameter carrier. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section
open scoped Classical

/-- DRT's theta_n: radius-n connection in the wired box of radius 2n. -/
def drtWiredOneArmMean (q : Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ)) (n : ℕ) : ℝ :=
  drtMean (boxGraph (0,0) (2*n)) q (BoundaryCondition.wired (boxVertexBoundary (0,0) (2*n)))
    (fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩) β (boxOuterOneArmIndicator (0,0) n (2*n))

/-- DRT's S_n, including its true empty value at n=0. -/
def drtWiredOneArmSum (q : Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ)) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, drtWiredOneArmMean q β k

/-- A centred radius-zero connection is the sure event in every open graph. -/
theorem radiusOneArmIndicator_zero_of_center {V : Type*} [Fintype V] (G : SimpleGraph V)
    (r : V → ℕ) (o : V) (ho : r o = 0) : radiusOneArmIndicator G r o 0 = fun _ => (1 : ℝ) := by
  funext A
  have hevent : ∃ b, b ∈ finiteRadiusShell r 0 ∧ FKC.FiniteFK.ActualConnected G A o b :=
    ⟨o, (mem_finiteRadiusShell r 0 o).mpr ho, ⟨.nil⟩⟩
  simp only [radiusOneArmIndicator, finiteConnectionToSetIndicator, ite_eq_left hevent]

@[simp] theorem drtWiredOneArmMean_zero (q : Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ)) :
    drtWiredOneArmMean q β 0 = 1 := by
  have hf : boxOuterOneArmIndicator (0,0) 0 (2*0) = fun _ => (1 : ℝ) :=
    radiusOneArmIndicator_zero_of_center _ _ _ (boxGlobalRadius_center (0,0) _)
  unfold drtWiredOneArmMean
  rw [hf]
  simp only [drtMean, mul_one]
  exact div_self (drtPartition_pos _ q _ _ β).ne'

theorem drtWiredOneArmMean_mem_Icc (q : Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ)) (n : ℕ) :
    drtWiredOneArmMean q β n ∈ Set.Icc (0 : ℝ) 1 :=
  drt_box_one_arm_mean_mem_Icc (0,0) n (2*n) q _ _ β

theorem drtWiredOneArmSum_ge_one (q : Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ))
    (n : ℕ) (hn : 1 ≤ n) : 1 ≤ drtWiredOneArmSum q β n := by
  rw [← drtWiredOneArmMean_zero q β]
  exact Finset.single_le_sum (fun k _ => (drtWiredOneArmMean_mem_Icc q β k).1)
    (Finset.mem_range.mpr (by omega))

end
end PottsContinuity.BD12
