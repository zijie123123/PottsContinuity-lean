module

public import PottsContinuity.Thm3.Prop4.WiredTargetComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Embedded wired-target comparison retaining the actual path support

Only one open path is required to stay in the embedded domain. No confinement
of its entire cluster is imposed or inferred. The event is increasing in the
actual sampled open bonds.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- An actual root-to-target open path with all its vertices in D. -/
def pathConfinedTargetEvent {V : Type*} (G : SimpleGraph V) (D T : Set V) (x : V) :
    Set (Configuration G) :=
  {A | ∃ y ∈ T, ∃ p : (openGraph G A).Walk x y, ∀ z ∈ p.support, z ∈ D}

/-- The whole source wired-target probability is bounded by the larger law's
actual target connection witnessed by a path in the original embedded carrier. -/
theorem embedded_wired_confined_target_probability_le {V U : Type*} [Finite V] [Finite U]
    (G : SimpleGraph V) (H : SimpleGraph U) (f : V ↪ U) (hGH : G.map f ≤ H)
    (θ : Parameters) (W : Set U) (x : V) :
    (measure G θ (BoundaryCondition.wired (f ⁻¹' W))
      (targetConnectionEvent x (f ⁻¹' W))).toReal ≤
    (measure H θ (BoundaryCondition.wired W)
      (pathConfinedTargetEvent H (Set.range f) W (f x))).toReal := by
  have h := RSW.embedded_boundary_probability_le G H f hGH θ (BoundaryCondition.wired W)
    (targetConnectionEvent x (f ⁻¹' W)) (targetConnectionEvent_upper x (f ⁻¹' W))
  have hlaw := law_eq_of_boundary_partition_eq (G := G) θ
    (isolatedExtensionPullbackBoundary f (BoundaryCondition.wired W))
    (BoundaryCondition.wired (f ⁻¹' W)) (pullback_wired_partition f W)
  change ((law G θ (isolatedExtensionPullbackBoundary f (BoundaryCondition.wired W))).toMeasure
    (targetConnectionEvent x (f ⁻¹' W))).toReal ≤ _ at h
  rw [hlaw] at h
  apply h.trans (measureReal_mono _ (measure_ne_top _ _))
  rintro A ⟨y,hy,hxy⟩
  obtain ⟨p,hp⟩ := RSW.embedded_restriction_confined_path G H f hGH A x y hxy
  exact ⟨f y,hy,p,hp⟩

end
end PottsContinuity.Thm3.Prop4
