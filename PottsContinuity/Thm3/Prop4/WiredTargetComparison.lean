module

public import PottsContinuity.Thm3.Prop4.ClusterConnection
public import PottsContinuity.Thm3.RSW.EmbeddedPath
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! # Adding vertices while keeping the same single wired target arc -/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
variable {V U : Type*} [Finite V] [Finite U]
    (G : SimpleGraph V) (H : SimpleGraph U) (f : V ↪ U) (hGH : G.map f ≤ H)
attribute [local instance] configurationMeasurableSpace

omit [Finite V] [Finite U] in
/-- Pulling back a single wired block gives the single literal preimage block. -/
theorem pullback_wired_partition : ∀ W : Set U,
    (isolatedExtensionPullbackBoundary f (BoundaryCondition.wired W)).partition =
      (BoundaryCondition.wired (f ⁻¹' W)).partition := by
  intro W
  apply Setoid.ext
  intro a b
  change (BoundaryCondition.wired W).partition.r (f a) (f b) ↔
    (BoundaryCondition.wired (f ⁻¹' W)).partition.r a b
  rw [BoundaryCondition.wired_rel,BoundaryCondition.wired_rel]
  exact or_congr f.injective.eq_iff Iff.rfl

include hGH in
/-- A whole root-to-arc event under the smaller wired-arc law is bounded by
that event under the larger law, without a sum over target vertices. -/
theorem embedded_wired_target_probability_le (θ : Parameters) (W : Set U) (x : V) :
    (measure G θ (BoundaryCondition.wired (f ⁻¹' W))
      (targetConnectionEvent x (f ⁻¹' W))).toReal ≤
    (measure H θ (BoundaryCondition.wired W) (targetConnectionEvent (f x) W)).toReal := by
  have h := RSW.embedded_boundary_probability_le G H f hGH θ (BoundaryCondition.wired W)
    (targetConnectionEvent x (f ⁻¹' W)) (targetConnectionEvent_upper x (f ⁻¹' W))
  have hlaw := law_eq_of_boundary_partition_eq (G := G) θ
    (isolatedExtensionPullbackBoundary f (BoundaryCondition.wired W))
    (BoundaryCondition.wired (f ⁻¹' W)) (pullback_wired_partition f W)
  change ((law G θ (isolatedExtensionPullbackBoundary f (BoundaryCondition.wired W))).toMeasure
      (targetConnectionEvent x (f ⁻¹' W))).toReal ≤ _ at h
  rw [hlaw] at h
  apply h.trans (measureReal_mono _ (measure_ne_top _ _))
  rintro A ⟨z,hz,hxz⟩
  exact ⟨f z,hz,RSW.embedded_restriction_actualConnected_mono f hGH A hxz⟩

end
end PottsContinuity.Thm3.Prop4
