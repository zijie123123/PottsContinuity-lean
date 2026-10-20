module

public import PottsContinuity.PD.FK.Isomorphism
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-! # Literal configuration relabeling through composed original graph maps -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
local instance markedIsoCompositionEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Original-bond labels compose with their actual graph isomorphisms. -/
theorem markedConfigurationIsoEdgeEquiv_trans {U V W : Type*}
    {G : SimpleGraph U} {H : SimpleGraph V} {J : SimpleGraph W}
    (e : G ≃g H) (f : H ≃g J) :
    configurationIsoEdgeEquiv (e.trans f) = (configurationIsoEdgeEquiv e).trans (configurationIsoEdgeEquiv f) := by
  apply Equiv.ext
  intro b
  apply Subtype.ext
  change b.val.map (fun x => f (e x)) = (b.val.map e).map f
  rw [Sym2.map_map]
  rfl

/-- The entire original configuration composes with its actual graph maps. -/
theorem markedConfigurationIso_trans {U V W : Type*}
    {G : SimpleGraph U} {H : SimpleGraph V} {J : SimpleGraph W}
    (e : G ≃g H) (f : H ≃g J) (A : Configuration G) :
    configurationIso (e.trans f) A = configurationIso f (configurationIso e A) := by
  unfold configurationIso
  rw [markedConfigurationIsoEdgeEquiv_trans]
  exact congrArg (fun q => q A) (Equiv.finsetCongr_trans (configurationIsoEdgeEquiv e) (configurationIsoEdgeEquiv f)).symm

end
end PottsContinuity.Thm3.Prop4

