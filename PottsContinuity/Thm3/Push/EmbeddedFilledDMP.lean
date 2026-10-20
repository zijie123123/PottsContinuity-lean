module

public import PottsContinuity.Thm3.Push.EmbeddedReveal
public import PottsContinuity.Thm3.Push.FilledFrontierDMP
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.Exploration
noncomputable section
variable {V : Type*} [Finite V]
local instance embeddedFilledEdgeDecidableEq {W : Type*} (G : SimpleGraph W) :
    DecidableEq G.edgeSet := Classical.decEq _
local instance embeddedFilledRemainingFintype (G : SimpleGraph V) (R : Configuration G) :
    Fintype (RemainingConfiguration G R) := Fintype.ofFinite _

/-- The canonical filled exploration of the inner rectangle, recorded on the
outer graph's SAME original bonds. No exterior configuration is discarded. -/
abbrev embeddedFilledTopReveal (a : LatticeVertex) (w h : ℕ) (G : SimpleGraph V)
    (f : RectangleVertex a w h ↪ V) (hRG : (rectangleGraph a w h).map f ≤ G) :=
  embeddedReveal (rectangleGraph a w h) G f hRG (rectangleFilledTopReveal a w h)

omit [Finite V] in
/-- Concrete one-sided stopping locality in an arbitrary containing graph. -/
theorem embeddedFilledTopReveal_stable (a : LatticeVertex) (w h : ℕ) (G : SimpleGraph V)
    (f : RectangleVertex a w h ↪ V) (hRG : (rectangleGraph a w h).map f ≤ G)
    (A B : Configuration G)
    (hagree : B ∩ embeddedFilledTopReveal a w h G f hRG A =
      A ∩ embeddedFilledTopReveal a w h G f hRG A) :
    embeddedFilledTopReveal a w h G f hRG B = embeddedFilledTopReveal a w h G f hRG A :=
  embeddedReveal_stable _ _ _ _ _ (rectangleFilledTopReveal_stable a w h) A B hagree

end
end PottsContinuity.Push
