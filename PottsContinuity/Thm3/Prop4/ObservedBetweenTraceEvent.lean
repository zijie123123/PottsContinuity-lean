module

public import PottsContinuity.Thm3.Prop4.RecordedObservationConnectivity
public import PottsContinuity.Thm3.Prop4.TubeEventSplit

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
local instance observedBetweenEdgeEq (n : ℕ) :
    DecidableEq (squareLattice.induce (box n : Set LatticeVertex)).edgeSet := Classical.decEq _

/-- The actual between-trace event is determined on complete records when
both traces are observed and the recorded open path witnesses its connection. -/
theorem betweenTubeTraceEvent_observation_invariant
    (n : ℕ) (ε : ℝ) (u v : (box n : Set LatticeVertex))
    (lower upper : Configuration (squareLattice.induce (box n : Set LatticeVertex)) →
      Finset (box n : Set LatticeVertex))
    (reveal : Configuration (squareLattice.induce (box n : Set LatticeVertex)) →
      Configuration (squareLattice.induce (box n : Set LatticeVertex)))
    (htrace : ∀ A C, RSW.stoppingObservationMap reveal A = RSW.stoppingObservationMap reveal C →
      lower A = lower C ∧ upper A = upper C)
    (hpath : ∀ A ∈ betweenTubeTraceEvent n ε u v lower upper,
      Nonempty ((openGraph _ (A ∩ reveal A)).Walk u v))
    (A C : Configuration (squareLattice.induce (box n : Set LatticeVertex)))
    (hA : A ∈ betweenTubeTraceEvent n ε u v lower upper)
    (hobs : RSW.stoppingObservationMap reveal A = RSW.stoppingObservationMap reveal C) :
    C ∈ betweenTubeTraceEvent n ε u v lower upper := by
  obtain ⟨hL,hU⟩ := htrace A C hobs
  refine ⟨actual_connection_of_same_observation _ reveal A C hobs (hpath A hA),?_,?_⟩
  · intro z hz
    exact hA.2.1 z (hL.symm ▸ hz)
  · intro z hz
    exact hA.2.2 z (hU.symm ▸ hz)

/-- The selected complete observations of the actual between-path event have
exactly that event as preimage, including the original connection condition. -/
theorem betweenTubeTraceEvent_eq_observation_preimage
    (n : ℕ) (ε : ℝ) (u v : (box n : Set LatticeVertex))
    (lower upper : Configuration (squareLattice.induce (box n : Set LatticeVertex)) →
      Finset (box n : Set LatticeVertex))
    (reveal : Configuration (squareLattice.induce (box n : Set LatticeVertex)) →
      Configuration (squareLattice.induce (box n : Set LatticeVertex)))
    (htrace : ∀ A C, RSW.stoppingObservationMap reveal A = RSW.stoppingObservationMap reveal C →
      lower A = lower C ∧ upper A = upper C)
    (hpath : ∀ A ∈ betweenTubeTraceEvent n ε u v lower upper,
      Nonempty ((openGraph _ (A ∩ reveal A)).Walk u v)) :
    betweenTubeTraceEvent n ε u v lower upper =
      (RSW.stoppingObservationMap reveal) ⁻¹'
        ((RSW.stoppingObservationMap reveal) '' betweenTubeTraceEvent n ε u v lower upper) := by
  symm
  apply observation_preimage_image_eq
  intro A hA C hobs
  exact betweenTubeTraceEvent_observation_invariant n ε u v lower upper reveal htrace hpath A C hA hobs

end
end PottsContinuity.Thm3.Prop4
