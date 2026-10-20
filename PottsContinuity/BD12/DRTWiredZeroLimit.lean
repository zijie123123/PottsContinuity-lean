module

public import PottsContinuity.BD12.InfiniteRadiusLimit
public import PottsContinuity.BD12.WiredBoxRadiusProbability
public import PottsContinuity.Infinite.Bridge

/-! The actual finite wired one-arm sequence vanishes whenever its frozen
infinite-volume wired limit has no infinite origin cluster. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory Filter PD.FK PD.RCInfinite
open scoped Topology
noncomputable section

/-- The finite-to-infinite zero-limit bridge with the frozen every-exhaustion
limit predicate and genuine actual-cluster event. -/
theorem drtWiredOneArmMean_tendsto_zero_of_wired_nonpercolation
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (β : Set.Ioi (0 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (drtHomogeneousParameters q hq β).toP
      (drtHomogeneousParameters q hq β).toQ 1 μ)
    (hzero : μ {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0,0) y}.Infinite} = 0) :
    Tendsto (drtWiredOneArmMean q β) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.1
  let θ := drtHomogeneousParameters q hq β
  have hμpd := Infinite.isRCInfiniteVolumeLimit_to_PD_box _ _ _ _ hμ
  have hz : μ (infiniteAt (0,0)) = 0 := hzero
  have hlim : Tendsto (fun m => μ.real (infiniteRadiusEvent (0,0) m)) atTop (𝓝 0) := by
    simpa only [Measure.real, hz, ENNReal.toReal_zero] using infiniteRadiusEvent_probability_tendsto μ (0,0)
  have htwice : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by omega : ∀ n : ℕ, n ≤ 2*n) tendsto_id
  have hbox (m : ℕ) : Tendsto
      (fun n => (wiredBoxProbabilityMeasure θ (0,0) (2*n) : Measure LatticeConfiguration).real
        (infiniteRadiusEvent (0,0) m)) atTop (𝓝 (μ.real (infiniteRadiusEvent (0,0) m))) := by
    have h := (tendsto_cylinder_probability θ 1 μ hμpd (infiniteRadiusEvent_isCylinder (0,0) m)).comp htwice
    simpa only [boxMeasure_wired, Function.comp_def] using h
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (drtWiredOneArmMean_mem_Icc q β n).1)
  · intro a ha
    obtain ⟨m, hm⟩ : ∃ m, μ.real (infiniteRadiusEvent (0,0) m) < a :=
      (hlim.eventually (gt_mem_nhds ha)).exists
    filter_upwards [(hbox m).eventually (gt_mem_nhds hm), eventually_ge_atTop m] with n hn hmn
    exact (drtWiredOneArmMean_le_radius_box_probability q hq β n m hmn).trans_lt hn

end
end PottsContinuity.BD12
