module

public import PottsContinuity.Thm3.Prop4.FiniteArmComparison
public import PottsContinuity.Thm3.Prop4.ClusterFactorization
public import PottsContinuity.Thm3.Prop4.TubeBoundaryArms
public import PottsContinuity.Thm3.RSW.SelfDualSetup

/-!
# Actual disconnected endpoint arms bounded by the infinite one-arm product

This is the probabilistic factorization used in Lemma 7. Planar dual paths
only need to imply that the two actual clusters differ. All finite-volume,
stopping-record, comparison and frozen infinite-volume inputs are proved.
-/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
noncomputable section
attribute [local instance] PD.FK.configurationMeasurableSpace
local instance finiteArmProductEdgeDecidableEq (n : ℕ) :
    DecidableEq (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet := Classical.decEq _

/-- Center the embedded box at the specified root, leaving the actual box carrier intact. -/
def boxCenteringEmbedding (n : ℕ) (a : (box n : Set (ℤ × ℤ))) :
    (box n : Set (ℤ × ℤ)) ↪ (ℤ × ℤ) where
  toFun z := z.val-a.val
  inj' := fun _x _y h => Subtype.ext (sub_left_inj.mp h)

theorem boxCenteringEmbedding_map_le (n : ℕ) (a : (box n : Set (ℤ × ℤ))) :
    (squareLattice.induce (box n : Set (ℤ × ℤ))).map (boxCenteringEmbedding n a) ≤ squareLattice := by
  intro x y hxy
  obtain ⟨z,w,hadj,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ x y).mp hxy
  change |z.val.1-w.val.1|+|z.val.2-w.val.2|=1 at hadj
  change |(z.val.1-a.val.1)-(w.val.1-a.val.1)|+
    |(z.val.2-a.val.2)-(w.val.2-a.val.2)|=1
  simpa only [sub_sub_sub_cancel_right] using hadj

/-- The complete translated finite arm is bounded by its infinite counterpart,
with no union bound over its possible endpoint. -/
theorem finiteEndpointArm_probability_le_infinite (θ : PD.FK.Parameters)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (n : ℕ) (a : (box n : Set (ℤ × ℤ))) (r : ℕ) :
    (PD.FK.measure (squareLattice.induce (box n : Set (ℤ × ℤ))) θ
      (PD.FK.BoundaryCondition.free ∅) (finiteEndpointArmEvent n a r)).toReal ≤
      RSW.oneArmProbability μ r := by
  exact finite_free_target_le_infinite_arm _ θ (boxCenteringEmbedding n a)
    (boxCenteringEmbedding_map_le n a) a
    {z | z.val-a.val ∈ vertexBoundary (box r)} r (by ext <;> simp [boxCenteringEmbedding])
    (fun _ hz => hz) μ hμ

/-- The two arms and disconnection concern the SAME actual sampled configuration. -/
theorem free_disconnected_endpoint_arms_le_infinite_product (θ : PD.FK.Parameters)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (n : ℕ) (a b : (box n : Set (ℤ × ℤ))) (k l : ℕ) :
    (PD.FK.measure (squareLattice.induce (box n : Set (ℤ × ℤ))) θ
      (PD.FK.BoundaryCondition.free ∅)
      {A | A ∈ finiteEndpointArmEvent n a k ∧ A ∈ finiteEndpointArmEvent n b l ∧
        ¬ PD.FK.ActualConnected _ A a b}).toReal ≤
      RSW.oneArmProbability μ k*RSW.oneArmProbability μ l := by
  have h := free_disconnected_target_product
    (G := squareLattice.induce (box n : Set (ℤ × ℤ))) θ a b
    {z | z.val-a.val ∈ vertexBoundary (box k)}
    {z | z.val-b.val ∈ vertexBoundary (box l)}
  exact h.trans (mul_le_mul (finiteEndpointArm_probability_le_infinite θ μ hμ n a k)
    (finiteEndpointArm_probability_le_infinite θ μ hμ n b l)
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

end
end PottsContinuity.Thm3.Prop4
