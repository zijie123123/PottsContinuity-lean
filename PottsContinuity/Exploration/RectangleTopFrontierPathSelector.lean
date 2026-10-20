module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Prod.Lex
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import PottsContinuity.Exploration.RectangleTopFrontierDMP
public import PottsContinuity.Exploration.ExtremalPathDMP
public import Mathlib.Tactic

/-!
# A deterministic path witness attached to the upper-frontier record

The path is selected by minimizing its explicit endpoint-and-vertex-list code
in the finite lexicographic order. The code is injective, so the selected
witness is unique. This gives a path-valued form of the upper-frontier
exploration, but does not assert that the lexicographically least path is the
geometrically highest crossing.
-/

@[expose] public section

namespace PottsContinuity.Exploration

open PottsContinuity.PD.FK

noncomputable section

local instance rectangleFrontierPathVertexFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (RectangleVertex a w h) := Fintype.ofFinite _
local instance rectangleFrontierPathVertexDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (RectangleVertex a w h) := Classical.decEq _
local instance rectangleFrontierPathEdgeFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (rectangleGraph a w h).edgeSet := Fintype.ofFinite _
local instance rectangleFrontierPathEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _
local instance rectangleFrontierPathOpenAdjDecidable (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    DecidableRel (openGraph (rectangleGraph a w h) A).Adj := by
  intro u v
  classical
  exact Classical.dec _
local instance rectangleFrontierPathFintype (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (u v : RectangleVertex a w h) :
    Fintype ((openGraph (rectangleGraph a w h) A).Path u v) := Fintype.ofFinite _
/-- A simple open path with endpoints on the two vertical sides of a
rectangle. -/
structure RectangleOpenCrossingPathWitness (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) where
  left : RectangleVertex a w h
  right : RectangleVertex a w h
  left_mem : left.val ∈ rectangleLeftSide a w h
  right_mem : right.val ∈ rectangleRightSide a w h
  path : (openGraph (rectangleGraph a w h) A).Path left right
  deriving Fintype

local instance rectangleFrontierPathWitnessFintype (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    Fintype (RectangleOpenCrossingPathWitness a w h A) := Fintype.ofFinite _

end
end PottsContinuity.Exploration
