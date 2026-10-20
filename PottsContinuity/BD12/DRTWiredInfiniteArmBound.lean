module

public import PottsContinuity.BD12.WiredBoxRadiusIdentity
public import PottsContinuity.BD12.FiniteWiredOneArmComparison
public import PottsContinuity.Infinite.Bridge

/-! Infinite wired shell probabilities are bounded by the actual finite
source theta_n, by domain comparison and fixed-cylinder convergence. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite MeasureTheory Filter
open scoped Topology
noncomputable section

/-- The infinite wired arm is bounded above by the radius-n arm in Lambda_2n. -/
theorem wired_infinite_radius_le_finite_one_arm (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ) (n : ℕ) :
    μ.real (infiniteRadiusEvent (0,0) n) ≤
      (measure (boxGraph (0,0) (2*n)) θ (BoundaryCondition.wired (boxVertexBoundary (0,0) (2*n)))
        (finiteDomainOneArmEvent (latticeBox (0,0) (2*n)) (0,0) (radiusBoxCenter (0,0) (2*n)) n)).toReal := by
  have hlim := tendsto_cylinder_probability θ 1 μ
    (Infinite.isRCInfiniteVolumeLimit_to_PD_box _ _ _ _ hμ) (infiniteRadiusEvent_isCylinder (0,0) n)
  simp only [boxMeasure_wired] at hlim
  apply le_of_tendsto_of_tendsto hlim tendsto_const_nhds
  filter_upwards [eventually_ge_atTop (2*n)] with N hN
  rw [wired_box_radius_probability_eq_finite θ (0,0) N n (by omega)]
  exact finite_wired_one_arm_probability_le θ (latticeBox_mono (0,0) hN) (0,0) n
    (latticeBox_mono (0,0) (by omega : n ≤ 2*n)) (radiusBoxCenter (0,0) (2*n)) rfl

/-- The same bound in the exact homogeneous source inverse-temperature law. -/
theorem drt_wired_infinite_radius_le_one_arm_mean (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β : Set.Ioi (0 : ℝ)) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (drtHomogeneousParameters q hq β).toP
      (drtHomogeneousParameters q hq β).toQ 1 μ) (n : ℕ) :
    μ.real (infiniteRadiusEvent (0,0) n) ≤ drtWiredOneArmMean q β n := by
  have h := wired_infinite_radius_le_finite_one_arm (drtHomogeneousParameters q hq β) μ hμ n
  let G := finiteLatticeGraph (latticeBox (0,0) (2*n))
  let ξ := BoundaryCondition.wired (boxVertexBoundary (0,0) (2*n))
  let J : G.edgeSet → Set.Ioi (0 : ℝ) := fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩
  let M := drtMean G q ξ J β
  have hi := finiteDomainOneArmEvent_indicator (latticeBox (0,0) (2*n)) (0,0) (radiusBoxCenter (0,0) (2*n)) n
  have heq := drt_mean_indicator_eq_fk_probability G q hq ξ β
    (finiteDomainOneArmEvent (latticeBox (0,0) (2*n)) (0,0) (radiusBoxCenter (0,0) (2*n)) n)
  exact h.trans_eq ((congrArg M hi).symm.trans heq).symm

end
end PottsContinuity.BD12
