module

public import PottsContinuity.Exploration.FiniteStoppingSetDMP
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# One-sided path-selector DMP interface

If a selected path is unchanged by edits strictly above it, revealing all
edges on or below that path is a stopping set. The finite FK DMP then gives
the exact conditional law on the unrevealed side with the boundary partition
induced by the revealed path states.
-/

@[expose] public section

namespace PottsContinuity.Exploration

open PottsContinuity.PD.FK

variable {V : Type*} [Finite V] {G : SimpleGraph V}

noncomputable section

local instance extremalPathEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance extremalPathEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance extremalPathRemainingFintype (R : Configuration G) :
    Fintype (RemainingConfiguration G R) := Fintype.ofFinite _

/-- The edges revealed by a one-sided extremal-path exploration. When there is
no selected path, reveal the complete finite configuration. -/
def extremalPathRevealMap {β : Type*} (selector : Configuration G → Option β)
    (onOrBelow : β → Configuration G) : Configuration G → Configuration G :=
  fun C => match selector C with
    | none => Finset.univ
    | some γ => onOrBelow γ

/-- The edges revealed by the reflected one-sided exploration: all edges on
or above the selected path. When no path is selected, the complete finite
configuration is revealed. -/
def extremalPathUpperRevealMap {β : Type*} (selector : Configuration G → Option β)
    (onOrAbove : β → Configuration G) : Configuration G → Configuration G :=
  fun C => match selector C with
    | none => Finset.univ
    | some γ => onOrAbove γ

/-- Agreement on or above a selected path preserves the upper-side selector
value, so the reflected reveal map is a stopping set. -/
theorem extremalPathUpperRevealMap_stable {β : Type*}
    (selector : Configuration G → Option β)
    (onOrAbove : β → Configuration G)
    (hselector : ∀ C C' γ, selector C = some γ →
      C' ∩ onOrAbove γ = C ∩ onOrAbove γ → selector C' = some γ) :
    ∀ C C', C' ∩ extremalPathUpperRevealMap selector onOrAbove C =
      C ∩ extremalPathUpperRevealMap selector onOrAbove C →
        extremalPathUpperRevealMap selector onOrAbove C' =
          extremalPathUpperRevealMap selector onOrAbove C := by
  intro C C' hagree
  classical
  cases hC : selector C with
  | none =>
      simp only [extremalPathUpperRevealMap, hC, Finset.inter_univ] at hagree ⊢
      subst C'
      simp [hC]
  | some γ =>
      have hC' : selector C' = some γ := by
        apply hselector C C' γ hC
        simpa [extremalPathUpperRevealMap, hC] using hagree
      simp [extremalPathUpperRevealMap, hC, hC']

end
end PottsContinuity.Exploration
