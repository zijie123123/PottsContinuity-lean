module

public import PottsContinuity.PD.FK.Lattice
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.Critical

open PottsContinuity.PD.FK

/-- The four unit steps from a square-lattice vertex. -/
def latticeStep (x : LatticeVertex) (d : Fin 4) : LatticeVertex :=
  if d.val = 0 then (x.1 + 1, x.2)
  else if d.val = 1 then (x.1 - 1, x.2)
  else if d.val = 2 then (x.1, x.2 + 1)
  else (x.1, x.2 - 1)

/-- A direction code for an adjacent pair; the branch order gives a definite
choice on the whole carrier. -/
def latticeDirection (x y : LatticeVertex) : Fin 4 :=
  if x.1 < y.1 then 0
  else if y.1 < x.1 then 1
  else if x.2 < y.2 then 2
  else 3

theorem latticeStep_adj (x : LatticeVertex) (d : Fin 4) :
    squareLattice.Adj x (latticeStep x d) := by
  fin_cases d <;> simp [squareLattice_adj_iff, latticeStep]

theorem latticeStep_direction (x y : LatticeVertex)
    (h : squareLattice.Adj x y) : latticeStep x (latticeDirection x y) = y := by
  have h' := (squareLattice_adj_iff x y).mp h
  rcases h' with ⟨(hxy | hyx), hsame⟩ | ⟨hsame, (hxy | hyx)⟩
  all_goals
    simp only [latticeDirection, latticeStep]
    split_ifs <;> simp_all <;> try ext <;> omega

/-- Finite direction sequences of a prescribed length. -/
abbrev WalkCode (n : ℕ) := List.Vector (Fin 4) n

instance walkCodeFintype (n : ℕ) : Fintype (WalkCode n) :=
  Fintype.ofEquiv (Fin n → Fin 4) (Equiv.vectorEquivFin (Fin 4) n).symm

theorem card_walkCode (n : ℕ) : Fintype.card (WalkCode n) = 4 ^ n := by
  calc
    Fintype.card (WalkCode n) = Fintype.card (Fin n → Fin 4) :=
      Fintype.card_congr (Equiv.vectorEquivFin (Fin 4) n)
    _ = 4 ^ n := by simp

/-- The unoriented edges traversed by a list of directions starting at `x`. -/
def walkCodeEdgesFrom (x : LatticeVertex) : List (Fin 4) → List (Sym2 LatticeVertex)
  | [] => []
  | d :: ds =>
      s(x, latticeStep x d) :: walkCodeEdgesFrom (latticeStep x d) ds

/-- The unoriented edges traversed by a finite direction code starting at `x`. -/
def walkCodeEdges {n : ℕ} (x : LatticeVertex) (c : WalkCode n) :
    List (Sym2 LatticeVertex) := walkCodeEdgesFrom x c.toList

/-- Read the four-direction sequence of a lattice walk. -/
noncomputable def walkDirections {x y : LatticeVertex} (p : squareLattice.Walk x y) : List (Fin 4) :=
  p.rec (motive := fun {_ _} _ => List (Fin 4))
    []
    (fun {x z _y} _ _ ih => latticeDirection x z :: ih)

theorem walkDirections_nil (x : LatticeVertex) :
    walkDirections (SimpleGraph.Walk.nil : squareLattice.Walk x x) = [] := rfl

theorem walkDirections_cons {x z : LatticeVertex} {_y : LatticeVertex}
    (h : squareLattice.Adj x z) (p : squareLattice.Walk z _y) :
    walkDirections (SimpleGraph.Walk.cons h p) = latticeDirection x z :: walkDirections p := rfl

theorem walkDirections_length {x y : LatticeVertex} (p : squareLattice.Walk x y) :
    (walkDirections p).length = p.length := by
  induction p with
  | nil => simp [walkDirections_nil]
  | @cons x z y h p ih =>
      rw [walkDirections_cons, SimpleGraph.Walk.length_cons, List.length_cons, ih]

/-- The direction sequence of a walk, packaged at its exact length. -/
noncomputable def walkCodeOfWalk {x y : LatticeVertex} (p : squareLattice.Walk x y) : WalkCode p.length :=
  ⟨walkDirections p, walkDirections_length p⟩

/-- The edge list decoded from a walk's direction code is its original edge list. -/
theorem walkCodeEdges_ofWalk {x y : LatticeVertex} (p : squareLattice.Walk x y) :
    walkCodeEdges x (walkCodeOfWalk p) = p.edges := by
  induction p with
  | nil => rfl
  | @cons x z y h p ih =>
      have ih' : walkCodeEdgesFrom z (walkDirections p) = p.edges := by
        simpa [walkCodeEdges, walkCodeOfWalk] using ih
      simp [walkCodeEdges, walkCodeEdgesFrom, walkCodeOfWalk, walkDirections_cons,
        latticeStep_direction x z h, ih', SimpleGraph.Walk.edges_cons]

end PottsContinuity.Critical
