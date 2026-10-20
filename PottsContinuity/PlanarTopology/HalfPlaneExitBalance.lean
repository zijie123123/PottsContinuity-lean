module

public import PottsContinuity.PlanarTopology.HalfPlaneExitTargetLimits
public import PottsContinuity.PlanarTopology.AdjacentProbabilityBalance
public import PottsContinuity.BD12.KSTProbability
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Int.Star
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite Filter Topology
noncomputable section

/-- Adjacent vertical locations have opposite first-exit probabilities above
any strict level below the genuine FKG square-root bound. The targets partition
all exterior heights before the source's additional unit vertical shift. -/
theorem halfPlaneExitEvent_adjacent_balancing
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (S : Set LatticeVertex) (r : ℝ)
    (hr : r < 1-Real.sqrt (1-μ.real (halfPlaneExitEvent S Set.univ))) :
    ∃ j : ℤ,
      r < μ.real (halfPlaneExitEvent S {y : ℤ | y ≤ -j-1}) ∧
      r < μ.real (halfPlaneExitEvent S {y : ℤ | -(j+1) ≤ y}) := by
  let A := fun j : ℤ => μ.real (halfPlaneExitEvent S {y : ℤ | y ≤ -j-1})
  let B := fun j : ℤ => μ.real (halfPlaneExitEvent S {y : ℤ | -j ≤ y})
  have hFKGr : ∀ E F : Set LatticeConfiguration, MeasurableSet E → MeasurableSet F →
      IsUpperSet E → IsUpperSet F → μ.real E * μ.real F ≤ μ.real (E ∩ F) := by
    intro E F hE hF hEu hFu
    have hh := ENNReal.toReal_mono (measure_ne_top μ (E ∩ F)) (hFKG E F hE hF hEu hFu)
    simpa only [Measure.real_def,ENNReal.toReal_mul] using hh
  have hcover : ∀ j, r < max (A j) (B j) := by
    intro j
    have hpart : ({y : ℤ | y ≤ -j-1} ∪ {y : ℤ | -j ≤ y}) = Set.univ := by
      ext y
      simp only [Set.mem_union,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
      omega
    have hevent : halfPlaneExitEvent S {y : ℤ | y ≤ -j-1} ∪
        halfPlaneExitEvent S {y : ℤ | -j ≤ y} = halfPlaneExitEvent S Set.univ := by
      rw [← halfPlaneExitEvent_union,hpart]
    have hh := BD12.kst_square_root_trick μ hFKGr
      (halfPlaneExitEvent_measurableSet S {y : ℤ | y ≤ -j-1})
      (halfPlaneExitEvent_measurableSet S {y : ℤ | -j ≤ y})
      (halfPlaneExitEvent_isUpperSet S _) (halfPlaneExitEvent_isUpperSet S _)
    rw [hevent] at hh
    exact hr.trans_le hh
  have hB : Monotone B := by
    intro m n hmn
    apply measureReal_mono (h₂ := measure_ne_top μ _)
    apply halfPlaneExitEvent_mono Set.Subset.rfl
    intro y hy
    change -n ≤ y
    change -m ≤ y at hy
    omega
  have hrF : r < μ.real (halfPlaneExitEvent S Set.univ) := by
    have hnonneg : 0 ≤ μ.real (halfPlaneExitEvent S Set.univ) := measureReal_nonneg
    have hh := Real.le_sqrt_self_iff.mpr (show 1-μ.real (halfPlaneExitEvent S Set.univ) ≤ 1 by linarith)
    linarith
  have hstart : ∃ j, r < A j := by
    have he := (tendsto_order.mp (halfPlaneExitEvent_lower_target_real_probability_tendsto μ S)).1 r hrF
    obtain ⟨N,hN⟩ := eventually_atTop.mp he
    refine ⟨-N-1,?_⟩
    change r < μ.real (halfPlaneExitEvent S {y : ℤ | y ≤ -(-N-1)-1})
    have hi : -(-N-1)-1 = N := by omega
    rw [hi]
    exact hN N le_rfl
  exact exists_adjacent_above_threshold_of_tendsto A B r
    (μ.real (halfPlaneExitEvent S Set.univ)) hB hcover hstart
    (halfPlaneExitEvent_upper_target_real_probability_tendsto μ S) hrF

end
end PottsContinuity.PlanarTopology
