module

public import PottsContinuity.Thm3.Push.JointStoppingReveal
public import PottsContinuity.Thm3.RSW.StoppingAverage

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.Exploration
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance commonEventEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- An event can be read from a complete record if membership is constant
on each realized record fiber. This includes both success and failure. -/
def ReadFromReveal (r : RevealMap (G := G)) (E : Set (Configuration G)) : Prop :=
  ∀ A B, B ∈ revealRecordEvent r A → (B ∈ E ↔ A ∈ E)

omit [Finite V] in
/-- An event read by either constituent exploration is read by their common
record. Neither an independence assumption nor a disjointness assumption is used. -/
theorem readFromReveal_joint_left (r t : RevealMap (G := G))
    (hr : ∀ A B, B ∩ r A = A ∩ r A → r B = r A)
    (ht : ∀ A B, B ∩ t A = A ∩ t A → t B = t A)
    (E : Set (Configuration G)) (hE : ReadFromReveal r E) :
    ReadFromReveal (jointReveal r t) E := by
  intro A B hB
  rw [jointReveal_recordEvent r t hr ht A] at hB
  exact hE A B hB.1

omit [Finite V] in
/-- The simultaneous success event is determined by the single common record. -/
theorem readFromReveal_joint_inter (r t : RevealMap (G := G))
    (hr : ∀ A B, B ∩ r A = A ∩ r A → r B = r A)
    (ht : ∀ A B, B ∩ t A = A ∩ t A → t B = t A)
    (E F : Set (Configuration G)) (hE : ReadFromReveal r E) (hF : ReadFromReveal t F) :
    ReadFromReveal (jointReveal r t) (E ∩ F) := by
  intro A B hB
  rw [jointReveal_recordEvent r t hr ht A] at hB
  exact and_congr (hE A B hB.1) (hF A B hB.2)

/-- The selected observations are the image of the actual success event.
Only realized observations occur; no representative is selected. -/
def selectedRevealObservations (r : RevealMap (G := G)) (E : Set (Configuration G)) :
    Set (RSW.StoppingObservationRange r) := RSW.stoppingObservationMap r '' E

omit [Finite V] in
/-- Record-readability gives exactly the observation preimage identity used
by the stopping-record averaging of `Thm3.RSW.StoppingAverage`. -/
theorem preimage_selectedRevealObservations (r : RevealMap (G := G))
    (E : Set (Configuration G)) (hE : ReadFromReveal r E) :
    RSW.stoppingObservationMap r ⁻¹' selectedRevealObservations r E = E := by
  ext A
  constructor
  · rintro ⟨B, hB, hBA⟩
    have hfiber : B ∈ revealRecordEvent r A := by
      rw [← RSW.stoppingObservationMap_fiber r A]
      exact hBA
    exact (hE A B hfiber).mp hB
  · intro hA
    exact ⟨A, hA, rfl⟩

end
end PottsContinuity.Push
