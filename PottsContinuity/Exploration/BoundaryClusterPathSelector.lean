module

public import Mathlib.Data.List.Lex
public import PottsContinuity.Exploration.BoundaryClusterStatisticDMP
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

@[expose] public section

namespace PottsContinuity.Exploration

open PottsContinuity.PD.FK

noncomputable section

variable {V : Type*} [Finite V] [LinearOrder V] {G : SimpleGraph V}

local instance boundaryClusterPathVertexFintype : Fintype V := Fintype.ofFinite _
local instance boundaryClusterPathEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance boundaryClusterPathEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance boundaryClusterPathOpenAdjDecidable (R : Configuration G) :
    DecidableRel (openGraph G R).Adj := by
  intro x y
  classical
  exact Classical.dec _
local instance boundaryClusterPathOpenEdgeFintype (R : Configuration G) :
    Fintype (openGraph G R).edgeSet := Fintype.ofFinite _
local instance boundaryClusterPathOpenEdgeDecidableEq (R : Configuration G) :
    DecidableEq (openGraph G R).edgeSet := Classical.decEq _
local instance boundaryClusterPathPathFintype (R : Configuration G) (x y : V) :
    Fintype ((openGraph G R).Path x y) := Fintype.ofFinite _

/-- A candidate path with endpoints in two fixed vertex sets. -/
abbrev BoundaryClusterPathWitness (R : Configuration G) :=
  Σ x : V, Σ y : V, (openGraph G R).Path x y

local instance boundaryClusterPathWitnessFintype (R : Configuration G) :
    Fintype (BoundaryClusterPathWitness (G := G) R) := Fintype.ofFinite _
local instance boundaryClusterPathWitnessValidDecidable (S T : Set V) (R : Configuration G) :
    DecidablePred (fun p : BoundaryClusterPathWitness (G := G) R =>
      p.1 ∈ S ∧ p.2.1 ∈ T) := fun _p => Classical.dec _

/-- The code records the endpoints and the chronological vertex trace. -/
def boundaryClusterPathCode (R : Configuration G)
    (p : BoundaryClusterPathWitness (G := G) R) : List V :=
  p.1 :: p.2.1 :: p.2.2.val.support

omit [Finite V] [LinearOrder V] in

def boundaryClusterPathCodeSet (S T : Set V) (R : Configuration G) :
    Finset (List V) :=
  ((Finset.univ : Finset (BoundaryClusterPathWitness (G := G) R)).filter
    (fun p => p.1 ∈ S ∧ p.2.1 ∈ T)).image
    (boundaryClusterPathCode R)

private theorem boundaryClusterPathCodeSet_nonempty_iff (S T : Set V)
    (R : Configuration G) :
    (boundaryClusterPathCodeSet S T R).Nonempty ↔
      ∃ x ∈ S, ∃ y ∈ T, Nonempty ((openGraph G R).Path x y) := by
  classical
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨p, hp, hcode⟩ := Finset.mem_image.mp hc
    exact ⟨p.1, (Finset.mem_filter.mp hp).2.1,
      p.2.1, (Finset.mem_filter.mp hp).2.2, ⟨p.2.2⟩⟩
  · rintro ⟨x, hx, y, hy, ⟨path⟩⟩
    refine ⟨boundaryClusterPathCode R ⟨x, y, path⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨x, y, path⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hx, hy⟩⟩, rfl⟩

/-- The least lexicographic vertex trace among recorded open paths joining
the two endpoint sets. -/
def boundaryClusterPathCodeSelector (S T : Set V) (R : Configuration G) :
    Option (List V) := by
  classical
  let codes := boundaryClusterPathCodeSet S T R
  exact if hc : codes.Nonempty then some (codes.min' hc) else none

/-- The code selector is defined exactly when the recorded configuration has
an open path between the endpoint sets. -/
theorem boundaryClusterPathCodeSelector_isSome_iff (S T : Set V)
    (R : Configuration G) :
    (boundaryClusterPathCodeSelector S T R).isSome ↔
      ∃ x ∈ S, ∃ y ∈ T, Nonempty ((openGraph G R).Path x y) := by
  classical
  unfold boundaryClusterPathCodeSelector
  dsimp only
  by_cases hc : (boundaryClusterPathCodeSet S T R).Nonempty
  · simp only [dite_eq_left hc, Option.isSome_some, true_iff]
    exact (boundaryClusterPathCodeSet_nonempty_iff S T R).mp hc
  · simp only [dite_eq_right hc, Option.isSome_none]
    constructor
    · intro h
      cases h
    · rintro ⟨x, hx, y, hy, ⟨p⟩⟩
      exact False.elim (hc ((boundaryClusterPathCodeSet_nonempty_iff S T R).mpr
        ⟨x, hx, y, hy, ⟨p⟩⟩))

omit [LinearOrder V] in

end
end PottsContinuity.Exploration
