module

public import PottsContinuity.Thm3.Prop4.RecordedWalkConnections
public import PottsContinuity.Thm3.RSW.StoppingAverage

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
variable {V : Type*} (G : SimpleGraph V)
local instance recordedObservationEdgeEq : DecidableEq G.edgeSet := Classical.decEq _

/-- A connection using recorded open bonds persists in every source sample
with the same complete observation, without any law assumption. -/
theorem actual_connection_of_same_observation
    (reveal : Configuration G → Configuration G) (A C : Configuration G)
    (hobs : RSW.stoppingObservationMap reveal A = RSW.stoppingObservationMap reveal C)
    {u v : V} (hconn : ActualConnected G (A ∩ reveal A) u v) : ActualConnected G C u v := by
  have hstate : A ∩ reveal A = C ∩ reveal C :=
    congrArg Prod.snd (congrArg Subtype.val hobs)
  have hle : A ∩ reveal A ⊆ C := by rw [hstate]; exact Finset.inter_subset_left
  exact hconn.mono (openGraph_mono hle)

/-- An event invariant under complete attained observations is exactly the
preimage of its observation image. No observation representative is chosen. -/
theorem observation_preimage_image_eq (reveal : Configuration G → Configuration G)
    (E : Set (Configuration G))
    (hE : ∀ A ∈ E, ∀ C, RSW.stoppingObservationMap reveal A = RSW.stoppingObservationMap reveal C → C ∈ E) :
    (RSW.stoppingObservationMap reveal) ⁻¹' ((RSW.stoppingObservationMap reveal) '' E) = E := by
  ext C
  constructor
  · rintro ⟨A,hA,hAC⟩
    exact hE A hA C hAC
  · intro hC
    exact ⟨C,hC,rfl⟩

end
end PottsContinuity.Thm3.Prop4
