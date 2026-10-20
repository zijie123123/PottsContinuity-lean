module

public import PottsContinuity.BD12.SeedClusterRevealment
public import PottsContinuity.BD12.SeparatingSeedConnection
public import PottsContinuity.BD12.WalkRadiusLevel
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-! Ordinary connection-event revealments from the actual seed exploration.
A radius-level shell discharges the separator hypothesis by graph walk induction. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory FKC.FiniteFK
open scoped Classical
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance separatingRevealEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance separatingRevealEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
variable [MeasurableSpace (Configuration G)] [MeasurableSingletonClass (Configuration G)]
    [MeasurableSpace (Option G.edgeSet)] [MeasurableSingletonClass (Option G.edgeSet)]

/-- Endpoint revealment bound for the ordinary connection event, assuming only
the configuration-independent structural graph separator. -/
theorem finiteConnection_seed_revealment_le_of_separator
    (rank : G.edgeSet ≃ Fin (Fintype.card G.edgeSet)) (S B : Finset V) (o : V)
    (hsep : ∀ b, b ∈ B → ∀ p : G.Walk o b, ∃ s, s ∈ p.support ∧ s ∈ S)
    (w : Configuration G → Set.Ioi (0 : ℝ)) (U : ℕ → ℝ)
    (e : G.edgeSet) (u v : V) (he : e.val = s(u,v)) :
    finiteRevealment w (finiteConnectionToSetIndicator G o B) U (seedClusterRevealTree G rank S ∅ ∅) e ≤
      finitePinnedMean w ∅ ∅ (fun A => if actualMultiClusterConnected G S A u then 1 else 0) +
      finitePinnedMean w ∅ ∅ (fun A => if actualMultiClusterConnected G S A v then 1 else 0) := by
  rw [finiteConnectionToSetIndicator_eq_seedMediated_of_separator G S B o hsep]
  exact seedClusterRevealTree_revealment_le_endpoints G rank S B o w U e u v he

end
end PottsContinuity.BD12
