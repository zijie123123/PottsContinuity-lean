module

public import PottsContinuity.Thm3.Prop4.BoxRectangleTubeTransport
public import PottsContinuity.Thm3.Prop4.TubeEventSplit
public import PottsContinuity.Thm3.RSW.FiniteIso

/-!
# Exact original-box trace transport to the literal sampled rectangle

The trace is read in the inverse source sample, retaining its original lattice
vertex labels. The graph isomorphism changes neither these labels nor the law.
-/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The actual box trace as original lattice vertices on the coordinate-identical
rectangle carrier, with no translated or rounded endpoint labels. -/
def boxTraceOnRectangle (n : ℕ)
    (trace : Configuration (squareLattice.induce (box n : Set LatticeVertex)) →
      Finset (box n : Set LatticeVertex))
    (A : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))) : Finset LatticeVertex :=
  (trace ((configurationIso (boxTubeRectangleIso n)).symm A)).image Subtype.val

/-- The rectangle excursion reads precisely the original trace vertices in
its upper outside region. -/
theorem boxTraceOnRectangle_excursion_iff (n : ℕ) (ε : ℝ)
    (u v : (box n : Set LatticeVertex))
    (trace : Configuration (squareLattice.induce (box n : Set LatticeVertex)) →
      Finset (box n : Set LatticeVertex))
    (A : Configuration (squareLattice.induce (box n : Set LatticeVertex))) :
    configurationIso (boxTubeRectangleIso n) A ∈
      tubeExcursionEvent n ε u.val v.val (boxTraceOnRectangle n trace) ↔
      ∃ z ∈ trace A, z.val ∈ inductionTubeAbove n ε u.val v.val := by
  classical
  change (∃ z ∈ inductionTubeAbove n ε u.val v.val,
    z ∈ (trace ((configurationIso (boxTubeRectangleIso n)).symm
      (configurationIso (boxTubeRectangleIso n) A))).image Subtype.val) ↔ _
  rw [Equiv.symm_apply_apply]
  constructor
  · rintro ⟨z,hz,htrace⟩
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp htrace
    exact ⟨w,hw,hz⟩
  · rintro ⟨z,hz,hAbove⟩
    exact ⟨z.val,hAbove,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩

/-- The genuine lower-trace source excursion is bounded by exactly the actual
rectangle trace event used by the recorded-witness convolution estimate. -/
theorem lower_excursion_probability_le_rectangle_trace_excursion (θ : Parameters)
    (n : ℕ) (ε : ℝ) (u v : (box n : Set LatticeVertex))
    (trace : Configuration (squareLattice.induce (box n : Set LatticeVertex)) →
      Finset (box n : Set LatticeVertex)) :
    (measure _ θ (BoundaryCondition.free ∅) (lowerTubeExcursionEvent n ε u v trace)).toReal ≤
      (measure _ θ (BoundaryCondition.free ∅)
        (tubeExcursionEvent n ε u.val v.val (boxTraceOnRectangle n trace))).toReal := by
  have hprob := RSW.free_probability_iso θ (boxTubeRectangleIso n)
    (tubeExcursionEvent n ε u.val v.val (boxTraceOnRectangle n trace))
  rw [hprob]
  apply measureReal_mono _ (measure_ne_top _ _)
  intro A hA
  exact (boxTraceOnRectangle_excursion_iff n ε u v trace A).mpr hA.2

end
end PottsContinuity.Thm3.Prop4
