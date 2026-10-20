module

public import PottsContinuity.Thm3.Prop4.DeletedReferenceInteriorAgreement
public import PottsContinuity.Thm3.Prop4.FirstTargetPrefix
public import PottsContinuity.Thm3.Prop4.ConfinedTargetComparison

/-!
# First physical exit survives restriction to genuine sampled dual edges

The prefix before the first exterior face has every edge incident to a
physical interior face. Interior agreement transfers its exact support to
the true sampled graph. The proved ambient marginal then transfers the
probability without any cost or event-conditioning assumption.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- A confined ambient path to the physical exterior has an actual sampled
first-exit prefix with the same confinement, after exact edge restriction. -/
theorem rectangle_deleted_ambient_confined_exit_restrict (a : LatticeVertex) (w h : ℕ)
    (R : Configuration (rectangleGraph a w h))
    (A : Configuration (edgeRestriction (rectangleDualAmbientGraph a w h) (rectangleAmbientCrossedReveal a w h R)))
    (D : Set (RectangleDualVertex a w h)) (x : RectangleDualVertex a w h)
    (hA : A ∈ pathConfinedTargetEvent _ D
      {z | z.val ∈ rectangleDualBoundary a w h} x) :
    subgraphConfigurationRestriction (rectangle_deleted_dual_le_ambient a w h R) A ∈
      pathConfinedTargetEvent _ D {z | z.val ∈ rectangleDualBoundary a w h} x := by
  let W : Set (RectangleDualVertex a w h) := {z | z.val ∈ rectangleDualBoundary a w h}
  obtain ⟨y,hy,p,hD⟩ := hA
  obtain ⟨z,hz,q,hsub,hedges⟩ := walk_to_first_target W hy p
  have hinside (v : RectangleDualVertex a w h) (hv : v ∉ W) :
      v.val ∈ rectangleDualInterior a w h := by
    by_contra hi
    exact hv (Finset.mem_filter.mpr ⟨v.property,hi⟩)
  obtain ⟨q',hqsupport⟩ := incident_supported_walk_transfer
    {v : RectangleDualVertex a w h | v.val ∈ rectangleDualInterior a w h}
    (fun v hv b => rectangle_deleted_open_interior_agreement a w h R A v hv b) q (by
      intro e he
      obtain ⟨v,hve,hv⟩ := hedges e he
      exact ⟨v,hve,hinside v hv⟩)
  refine ⟨z,hz,q',?_⟩
  intro v hv
  rw [hqsupport] at hv
  exact hD v (hsub v hv)

/-- The true sampled deleted reference exit probability is at least the
ambient one, retaining confinement of the actual first-exit path. -/
theorem rectangle_deleted_ambient_confined_exit_probability_le_actual
    (a : LatticeVertex) (w h : ℕ) (R : Configuration (rectangleGraph a w h)) (θ : Parameters)
    (D : Set (RectangleDualVertex a w h)) (x : RectangleDualVertex a w h) :
    (measure (edgeRestriction (rectangleDualAmbientGraph a w h) (rectangleAmbientCrossedReveal a w h R))
      θ (rectangleDualBoundaryCondition a w h)
      (pathConfinedTargetEvent _ D {z | z.val ∈ rectangleDualBoundary a w h} x)).toReal ≤
    (measure (edgeRestriction (rectangleDualGraph a w h) (rectangleCrossedEdges a w h R))
      θ (rectangleDualBoundaryCondition a w h)
      (pathConfinedTargetEvent _ D {z | z.val ∈ rectangleDualBoundary a w h} x)).toReal := by
  let E := pathConfinedTargetEvent
    (edgeRestriction (rectangleDualGraph a w h) (rectangleCrossedEdges a w h R)) D
    {z | z.val ∈ rectangleDualBoundary a w h} x
  have hlaw := congrArg (fun ρ : PMF (Configuration
    (edgeRestriction (rectangleDualGraph a w h) (rectangleCrossedEdges a w h R))) => ρ.toMeasure E)
      (rectangle_deleted_ambient_law_restrict a w h R θ)
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at hlaw
  apply (measureReal_mono (fun A hA =>
    rectangle_deleted_ambient_confined_exit_restrict a w h R A D x hA) (measure_ne_top _ _)).trans
  exact (congrArg ENNReal.toReal hlaw).le

end
end PottsContinuity.Thm3.Prop4
