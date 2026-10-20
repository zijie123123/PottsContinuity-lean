module

public import PottsContinuity.Thm3.Prop4.TubeExcursion
public import PottsContinuity.Thm3.RSW.StoppingAverage

/-!
# Exact maximal-excursion events on complete path observations

The observed event is the image of the actual maximal event. Trace agreement
on complete records makes its preimage exactly that event, with no selected
representative and no additional maximal-vertex selection rule.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
variable {V : Type*} {G : SimpleGraph V}

/-- All attained complete observations on which the actual trace has this
maximizing vertex. Ties retain all maximizing vertices. -/
def maximalExcursionObservations (n : ℕ) (ε : ℝ) (u v : LatticeVertex)
    (trace : Configuration G → Finset LatticeVertex)
    (reveal : Configuration G → Configuration G) (z : LatticeVertex) :
    Set (RSW.StoppingObservationRange reveal) :=
  RSW.stoppingObservationMap reveal '' maximalTubeExcursionEvent n ε u v trace z

/-- The unchanged actual maximal event depends only on the trace. -/
theorem maximalTubeExcursionEvent_mem_iff_of_trace_eq
    (n : ℕ) (ε : ℝ) (u v z : LatticeVertex)
    (trace : Configuration G → Finset LatticeVertex) {A B : Configuration G}
    (h : trace A = trace B) :
    A ∈ maximalTubeExcursionEvent n ε u v trace z ↔
      B ∈ maximalTubeExcursionEvent n ε u v trace z := by
  simp only [maximalTubeExcursionEvent,Set.mem_ofPred_eq,h]

/-- Complete-observation selection is precisely the original maximal event
when the trace is determined on every attained observation fiber. -/
theorem mem_maximalExcursionObservations_iff
    (n : ℕ) (ε : ℝ) (u v z : LatticeVertex)
    (trace : Configuration G → Finset LatticeVertex)
    (reveal : Configuration G → Configuration G)
    (htrace : ∀ A B, RSW.stoppingObservationMap reveal A = RSW.stoppingObservationMap reveal B →
      trace A = trace B) (A : Configuration G) :
    RSW.stoppingObservationMap reveal A ∈ maximalExcursionObservations n ε u v trace reveal z ↔
      A ∈ maximalTubeExcursionEvent n ε u v trace z := by
  constructor
  · rintro ⟨B,hB,hBA⟩
    exact (maximalTubeExcursionEvent_mem_iff_of_trace_eq n ε u v z trace (htrace B A hBA)).mp hB
  · intro hA
    exact ⟨A,hA,rfl⟩

/-- The source excursion is exactly covered by the attained maximal records. -/
theorem tubeExcursion_eq_union_observed_maximal
    (n : ℕ) (ε : ℝ) (u v : LatticeVertex)
    (trace : Configuration G → Finset LatticeVertex)
    (reveal : Configuration G → Configuration G)
    (htrace : ∀ A B, RSW.stoppingObservationMap reveal A = RSW.stoppingObservationMap reveal B →
      trace A = trace B) :
    tubeExcursionEvent n ε u v trace = ⋃ z ∈ inductionTubeAbove n ε u v,
      (RSW.stoppingObservationMap reveal) ⁻¹' maximalExcursionObservations n ε u v trace reveal z := by
  rw [tubeExcursion_eq_union_maximal]
  congr 1
  funext z
  congr 1
  funext hz
  ext A
  exact (mem_maximalExcursionObservations_iff n ε u v z trace reveal htrace A).symm

end
end PottsContinuity.Thm3.Prop4
