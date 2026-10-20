module

public import PottsContinuity.Thm3.RSW.FinitePlaneConnections

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section

/-- Finite annulus circuit probability is bounded by the sum of the translated
plane arm probabilities over its actual possible starting vertices. -/
theorem annulusProbability_le_boxCard_mul_oneArm
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (R n : ℕ) :
    annulusProbability θ R n ≤ ((box (2*n)).card : ℝ)*oneArmProbability μ n := by
  classical
  let : IsProbabilityMeasure μ := hμ.1
  let X := {x : LatticeVertex // x ∈ box (2*n)}
  let AnnulusArmBound_startFintype : Fintype X := (box (2*n)).finite_toSet.fintype
  have hfinite := finite_free_event_le_infinite θ (box (R*n))
    (fun ω => ω ∈ annulusCircuitEvent (box (R*n)) (0,0) n)
    (annulusCircuitEvent_isUpperSet _ _ _) μ hμ
  have hmono := measureReal_mono (μ := μ)
    (plane_annulus_subset_oneArm_union (box (R*n)) n)
  have hunion := measureReal_iUnion_fintype_le (μ := μ)
    (fun x : X => Thm3.Easy.oneArmBoundaryEvent x.val n)
  have hsum : (∑ x : X, μ.real (Thm3.Easy.oneArmBoundaryEvent x.val n)) =
      ((box (2*n)).card : ℝ)*oneArmProbability μ n := by
    calc
      _ = ∑ _x : X, oneArmProbability μ n := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact free_oneArmBoundaryEvent_real_eq θ μ hμ x.val n
      _ = _ := by
        rw [Finset.sum_const]
        simp only [Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,X]
  exact hfinite.trans (hmono.trans (hunion.trans_eq hsum))

/-- The exact polynomial prefactor in the source exclusivity union bound.
The result holds at every scale and for every finite ambient radius multiplier. -/
theorem annulusProbability_le_polynomial_mul_oneArm
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (R n : ℕ) :
    annulusProbability θ R n ≤ (4*(n:ℝ)+1)^2*oneArmProbability μ n := by
  have hb : box (2*n) = latticeBox (0,0) (2*n) := by
    simp only [latticeBox,box,zero_sub,zero_add]
  have hcard : ((box (2*n)).card : ℝ) = (4*(n:ℝ)+1)^2 := by
    rw [hb,card_latticeBox]
    push_cast
    ring
  rw [← hcard]
  exact annulusProbability_le_boxCard_mul_oneArm θ μ hμ R n

end
end PottsContinuity.RSW
