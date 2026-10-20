module

public import PottsContinuity.PlanarMixed.Square.FrozenBoundaryRetraction
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PlanarMixed.Square
noncomputable section

/-- The literal induced carrier remaining after deleting free pockets. -/
def pocketInclusion {V : Type*} (S : Set V) : S ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- A free pocket retracts to a retained vertex of its enclosing wired class. -/
def wiredPocketRetraction {V : Type*} (S : Set V) (a : S) (v : V) : S := by
  classical
  exact if h : v ∈ S then ⟨v,h⟩ else a

/-- The retained induced graph uses exactly its original bonds. -/
theorem pocketInduced_map_le {V : Type*} (H : SimpleGraph V) (S : Set V) :
    (H.induce S).map (pocketInclusion S) ≤ H := by
  rintro u v huv
  obtain ⟨x,y,hxy,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  exact hxy

end
end PottsContinuity.Push
