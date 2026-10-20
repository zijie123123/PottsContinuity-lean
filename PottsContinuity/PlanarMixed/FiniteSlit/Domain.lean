module

public import PottsContinuity.PlanarMixed.SlitGlobalOpenGraph

/-! The balanced finite truncated slit box for the revised Case 2 route.
Outer left and right arcs are wired separately; no infinite law is used. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.FK.Medial BD12
noncomputable section

/-- Every original vertex of the balanced rectangle is retained. -/
abbrev Vertex (M : ℕ) (x : ℤ) :=
  RectangleVertex (x-(M : ℤ),0) (2*M-1) M

/-- Delete exactly the horizontal bonds crossing x-1/2 strictly above y. -/
def graph (M : ℕ) (x y : ℤ) : SimpleGraph (Vertex M x) where
  Adj u v := (rectangleGraph (x-(M : ℤ),0) (2*M-1) M).Adj u v ∧
    ¬ (y < u.val.2 ∧ y < v.val.2 ∧
      ((u.val.1 = x-1 ∧ v.val.1 = x) ∨ (v.val.1 = x-1 ∧ u.val.1 = x)))
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm,fun h' => h.2 ⟨h'.2.1,h'.1,h'.2.2.symm⟩⟩
  loopless := by
    constructor
    intro u h
    exact (rectangleGraph (x-(M : ℤ),0) (2*M-1) M).loopless.irrefl u h.1

/-- The bottom-left arc and the entire left outer arc form one wired class. -/
def alpha (M : ℕ) (x : ℤ) : Set (Vertex M x) :=
  {v | (v.val.2 = 0 ∧ v.val.1 ≤ x) ∨ v.val.1 = x-(M : ℤ) ∨
    (v.val.2 = (M : ℤ) ∧ v.val.1 ≤ x-1)}

/-- The marked ray and right outer arc form the other wired class. -/
def beta (M : ℕ) (x y : ℤ) : Set (Vertex M x) :=
  {v | v.val.1 = x+(M : ℤ)-1 ∨
    (v.val.2 = (M : ℤ) ∧ x ≤ v.val.1) ∨ (v.val.1 = x ∧ y ≤ v.val.2)}

/-- The free slit side includes its left tip at height y; the top is wired. -/
def freeSlit (M : ℕ) (x y : ℤ) : Set (Vertex M x) :=
  {v | v.val.1 = x-1 ∧ y ≤ v.val.2 ∧ v.val.2 < (M : ℤ)}

/-- Exact integer bounds, with no truncated natural subtraction remaining. -/
theorem mem_rectangle_iff (M : ℕ) (x : ℤ) (hM : 1 ≤ M) (z : LatticeVertex) :
    z ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M ↔
      x-(M : ℤ) ≤ z.1 ∧ z.1 ≤ x+(M : ℤ)-1 ∧ 0 ≤ z.2 ∧ z.2 ≤ (M : ℤ) := by
  rw [PD.FK.mem_latticeRectangle]
  have hw : ((2*M-1 : ℕ) : ℤ) = 2*(M : ℤ)-1 := by omega
  simp only [zero_add]
  rw [hw]
  omega

/-- The two outer wired arcs are disjoint in the actual finite regime. -/
theorem alpha_disjoint_beta (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (_hyM : y < (M : ℤ)) :
    Disjoint (alpha M x) (beta M x y) := by
  apply Set.disjoint_left.mpr
  intro v ha hb
  change ((v.val.2 = 0 ∧ v.val.1 ≤ x) ∨ v.val.1 = x-(M : ℤ) ∨
    (v.val.2 = (M : ℤ) ∧ v.val.1 ≤ x-1)) at ha
  change (v.val.1 = x+(M : ℤ)-1 ∨
    (v.val.2 = (M : ℤ) ∧ x ≤ v.val.1) ∨ (v.val.1 = x ∧ y ≤ v.val.2)) at hb
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> omega

/-- Alpha and beta are separate classes, with every other vertex free. -/
def boundary (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    BoundaryCondition (Vertex M x) :=
  twoBlockBoundary (alpha M x) (beta M x y) (alpha_disjoint_beta M x y hM hy hyM)

/-- The physical connection of the two wired arcs, without virtual links. -/
def connectionEvent (M : ℕ) (x y : ℤ) : Set (Configuration (graph M x y)) :=
  BD12.arcsConnectionEvent (graph M x y) (alpha M x) (beta M x y)

/-- Reflected dual bottom arc, with the actual one-column left offset. -/
def dualBottom (M : ℕ) (x : ℤ) : Set (Vertex M x) :=
  {v | v.val.2 = 0 ∧ x-(M : ℤ)+1 ≤ v.val.1 ∧ v.val.1 ≤ x-1}

/-- Reflected dual marked ray begins at y+1. -/
def dualRay (M : ℕ) (x y : ℤ) : Set (Vertex M x) :=
  {v | v.val.1 = x ∧ y+1 ≤ v.val.2}

/-- The two dual free-side arcs are wired together, with free boundary elsewhere. -/
def dualBoundary (M : ℕ) (x y : ℤ) : BoundaryCondition (Vertex M x) :=
  BoundaryCondition.wired (dualBottom M x ∪ dualRay M x y)

/-- The finite reference graph is a literal rectangle subgraph. -/
theorem graph_le_rectangle (M : ℕ) (x y : ℤ) :
    graph M x y ≤ rectangleGraph (x-(M : ℤ),0) (2*M-1) M := fun _ _ h => h.1

end
end PottsContinuity.PlanarMixed.FiniteSlit
