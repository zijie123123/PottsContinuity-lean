module

public import PottsContinuity.Thm3.Prop4.BoxHalfTurn
public import PottsContinuity.Thm3.Prop4.TubeEventSplit

/-!
# Exact half-turn transport of the two actual trace excursion events

The original square is rotated and the endpoint order exchanged. The source
trace is read from the inverse-transformed sample before rotating its vertices.
-/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- Rotate the actual box trace, reading the original trace in the inverse
sample so that every original configuration is represented exactly once. -/
def halfTurnBoxTrace (n : ℕ)
    (trace : Configuration (squareLattice.induce (box n : Set LatticeVertex)) →
      Finset (box n : Set LatticeVertex))
    (A : Configuration (squareLattice.induce (box n : Set LatticeVertex))) :
    Finset (box n : Set LatticeVertex) :=
  (trace ((configurationIso (boxHalfTurnIso n)).symm A)).map (boxHalfTurnIso n).toEquiv.toEmbedding

/-- The upper-trace lower excursion is precisely the rotated lower-trace
upper excursion, with the two original endpoints exchanged. -/
theorem upperTubeExcursionEvent_halfTurn_iff
    (n : ℕ) (ε : ℝ) (u v : (box n : Set LatticeVertex))
    (upper : Configuration (squareLattice.induce (box n : Set LatticeVertex)) →
      Finset (box n : Set LatticeVertex))
    (A : Configuration (squareLattice.induce (box n : Set LatticeVertex))) :
    configurationIso (boxHalfTurnIso n) A ∈ lowerTubeExcursionEvent n ε
      (boxHalfTurnIso n v) (boxHalfTurnIso n u) (halfTurnBoxTrace n upper) ↔
      A ∈ upperTubeExcursionEvent n ε u v upper := by
  classical
  constructor
  · rintro ⟨hconn,z,hz,hzAbove⟩
    have hz' : z ∈ (upper A).map (boxHalfTurnIso n).toEquiv.toEmbedding := by
      simpa only [halfTurnBoxTrace,Equiv.symm_apply_apply] using hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hz'
    refine ⟨((actualConnected_configurationIso (boxHalfTurnIso n) A v u).mp hconn).symm,w,hw,?_⟩
    exact (inductionTubeAbove_neg_swap_mem_iff n ε u.val v.val w.val).mp hzAbove
  · rintro ⟨hconn,w,hw,hwBelow⟩
    refine ⟨(actualConnected_configurationIso (boxHalfTurnIso n) A v u).mpr hconn.symm,
      boxHalfTurnIso n w,?_,?_⟩
    · simp only [halfTurnBoxTrace,Equiv.symm_apply_apply]
      exact Finset.mem_map.mpr ⟨w,hw,rfl⟩
    · exact (inductionTubeAbove_neg_swap_mem_iff n ε u.val v.val w.val).mpr hwBelow

/-- Actual mixed path-event probabilities transform by the exact free box law;
no independence or monotonicity of the selected trace is required. -/
theorem upperTubeExcursion_probability_eq_rotated_lower (θ : Parameters)
    (n : ℕ) (ε : ℝ) (u v : (box n : Set LatticeVertex))
    (upper : Configuration (squareLattice.induce (box n : Set LatticeVertex)) →
      Finset (box n : Set LatticeVertex)) :
    (measure _ θ (BoundaryCondition.free ∅) (upperTubeExcursionEvent n ε u v upper)).toReal =
      (measure _ θ (BoundaryCondition.free ∅) (lowerTubeExcursionEvent n ε
        (boxHalfTurnIso n v) (boxHalfTurnIso n u) (halfTurnBoxTrace n upper))).toReal := by
  symm
  rw [boxHalfTurn_free_event_probability]
  congr 2
  ext A
  exact upperTubeExcursionEvent_halfTurn_iff n ε u v upper A

end
end PottsContinuity.Thm3.Prop4
