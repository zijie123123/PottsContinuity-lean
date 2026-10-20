-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/WiredAvoidingRecordConnection.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.WiredAvoidingConnectionRestriction
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance recordConnectionEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance recordConnectionEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- A genuine all-incident reveal record fixes the actual masked cluster. -/
theorem wiredAvoidingClusterSet_eq_of_record
    (W : Set V) (S : Finset V) (A₀ A : Configuration G)
    (hrecord : A ∈ revealRecordEvent G (wiredAvoidingClusterReveal G W S) A₀) :
    wiredAvoidingClusterSet G W S A = wiredAvoidingClusterSet G W S A₀ := by
  change wiredAvoidingClusterReveal G W S A = wiredAvoidingClusterReveal G W S A₀ ∧
    A ∩ wiredAvoidingClusterReveal G W S A₀ =
      A₀ ∩ wiredAvoidingClusterReveal G W S A₀ at hrecord
  exact wiredAvoidingClusterSet_consistent W S A₀ A hrecord.2


omit [Finite V] in
private theorem wiredAvoidingRestrictedConnection_congr
    (W : Set V) (T U : Set V) (hTU : T = U) (A : Configuration G) {x : V}
    (hxT : x ∈ T) (hxU : x ∈ U) :
    (∃ y : T, y.val ∈ W ∧ ActualConnected (G.induce T)
      (embeddedConfigurationRestriction (G.induce T) G
        (⟨Subtype.val, Subtype.val_injective⟩ : T ↪ V)
        (by
          intro a b hab
          rcases (SimpleGraph.map_adj (⟨Subtype.val, Subtype.val_injective⟩ : T ↪ V)
            (G.induce T) a b).mp hab with ⟨a', b', hadj, rfl, rfl⟩
          exact SimpleGraph.induce_adj.mp hadj) A)
      ⟨x, hxT⟩ y) ↔
    (∃ y : U, y.val ∈ W ∧ ActualConnected (G.induce U)
      (embeddedConfigurationRestriction (G.induce U) G
        (⟨Subtype.val, Subtype.val_injective⟩ : U ↪ V)
        (by
          intro a b hab
          rcases (SimpleGraph.map_adj (⟨Subtype.val, Subtype.val_injective⟩ : U ↪ V)
            (G.induce U) a b).mp hab with ⟨a', b', hadj, rfl, rfl⟩
          exact SimpleGraph.induce_adj.mp hadj) A)
      ⟨x, hxU⟩ y) := by
  subst U
  rfl

/-- Within a fixed actual reveal record, connection to W can be tested on the
fixed complement of the recorded masked cluster. -/
theorem wiredAvoidingConnection_toW_iff_record_complement
    (W : Set V) (S : Finset V) (A₀ A : Configuration G)
    (hrecord : A ∈ revealRecordEvent G (wiredAvoidingClusterReveal G W S) A₀)
    {x : V} (hx : x ∉ wiredAvoidingClusterSet G W S A₀) :
    (∃ w : V, w ∈ W ∧ ActualConnected G A x w) ↔
      ∃ y : wiredAvoidingComplementSet G W S A₀,
        y.val ∈ W ∧ ActualConnected (G.induce (wiredAvoidingComplementSet G W S A₀))
          (embeddedConfigurationRestriction
            (G.induce (wiredAvoidingComplementSet G W S A₀)) G
            (wiredAvoidingComplementEmbedding G W S A₀)
            (wiredAvoidingComplementGraph_le (G := G) W S A₀) A)
          ⟨x, hx⟩ y := by
  have hC := wiredAvoidingClusterSet_eq_of_record W S A₀ A hrecord
  have hxA : x ∉ wiredAvoidingClusterSet G W S A := by
    rw [hC]
    exact hx
  have hconn := wiredAvoidingConnection_toW_iff_complement W S A hxA
  have hsets : wiredAvoidingComplementSet G W S A =
      wiredAvoidingComplementSet G W S A₀ := by
    unfold wiredAvoidingComplementSet
    rw [hC]
  have htransport := wiredAvoidingRestrictedConnection_congr W
    (wiredAvoidingComplementSet G W S A)
    (wiredAvoidingComplementSet G W S A₀) hsets A hxA hx
  exact hconn.trans htransport

end
end PottsContinuity.FKC.FiniteFK
