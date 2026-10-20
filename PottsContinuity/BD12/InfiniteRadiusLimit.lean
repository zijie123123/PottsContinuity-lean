module

public import PottsContinuity.BD12.InfiniteRadiusEvent
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! Decreasing shell events recover the actual infinite open cluster and its
probability by continuity from above. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite MeasureTheory Filter
open scoped Topology
noncomputable section
open scoped Classical

/-- Reaching every coordinate radius is exactly an infinite actual cluster. -/
theorem infiniteRadiusEvent_iInter (c : LatticeVertex) :
    (⋂ n : ℕ, infiniteRadiusEvent c n) = infiniteAt c := by
  ext ω
  constructor
  · intro hω
    change (cluster ω c).Infinite
    intro hfin
    let F := hfin.toFinset
    let N := F.sup (latticeRadius c)
    obtain ⟨v,hv,hconn⟩ := Set.mem_iInter.mp hω (N+1)
    have hvF : v ∈ F := hfin.mem_toFinset.mpr hconn
    have hb : latticeRadius c v ≤ N := Finset.le_sup hvF
    omega
  · intro hω
    apply Set.mem_iInter.mpr
    intro n
    obtain ⟨v,hv,hout⟩ := hω.exists_notMem_finset (latticeBox c n)
    have hr : n ≤ latticeRadius c v := by
      have hnot : ¬ latticeRadius c v ≤ n := fun h => hout ((latticeRadius_le_iff_mem_box c v n).mp h)
      omega
    obtain ⟨p⟩ := hv
    obtain ⟨z,q,hz,_⟩ := walk_reaches_radius_inside_ball (latticeRadius c)
      (infinite_open_radius_step c ω) p n (by simp) hr
    exact ⟨z,hz,⟨q⟩⟩

/-- Actual shell probabilities converge to the infinite-cluster probability. -/
theorem infiniteRadiusEvent_probability_tendsto (μ : Measure LatticeConfiguration)
    [IsFiniteMeasure μ] (c : LatticeVertex) :
    Tendsto (fun n => μ.real (infiniteRadiusEvent c n)) atTop (𝓝 (μ.real (infiniteAt c))) := by
  have h := tendsto_measure_iInter_atTop
    (fun n => (infiniteRadiusEvent_isCylinder c n).measurableSet.nullMeasurableSet)
    (infiniteRadiusEvent_antitone c) ⟨0,measure_ne_top μ _⟩
  rw [infiniteRadiusEvent_iInter] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp h

end
end PottsContinuity.BD12
