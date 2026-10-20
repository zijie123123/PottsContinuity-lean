-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxDomain.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Rectangle
public import PottsContinuity.FKC.FiniteFK.Graph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- Retained vertices of the square box Λₙ, including vertices isolated by
the slit-edge deletion. -/
abbrev SlitBoxVertex (n : ℕ) :=
  RectangleVertex (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n)

/-- The retained wired arc {(0,k) : 0 ≤ k ≤ n}. -/
def slitBoxWiredArc (n : ℕ) : Finset (SlitBoxVertex n) :=
  Finset.univ.filter fun v => v.val.1 = 0 ∧ 0 ≤ v.val.2 ∧ v.val.2 ≤ n

theorem mem_slitBoxWiredArc_iff (n : ℕ) (v : SlitBoxVertex n) :
    v ∈ slitBoxWiredArc n ↔ v.val.1 = 0 ∧ 0 ≤ v.val.2 ∧ v.val.2 ≤ n := by
  simp [slitBoxWiredArc]

/-- The slit domain keeps every Λₙ vertex and removes exactly edges whose two
endpoints both belong to the wired arc. -/
def slitBoxGraph (n : ℕ) : SimpleGraph (SlitBoxVertex n) where
  Adj u v := (rectangleGraph (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n)).Adj u v ∧
    ¬ (u ∈ slitBoxWiredArc n ∧ v ∈ slitBoxWiredArc n)
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm, fun hboth => h.2 ⟨hboth.2, hboth.1⟩⟩
  loopless := by
    constructor
    intro u h
    exact (rectangleGraph (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n)).loopless.irrefl u h.1

theorem slitBoxGraph_adj_iff (n : ℕ) (u v : SlitBoxVertex n) :
    (slitBoxGraph n).Adj u v ↔
      squareLattice.Adj u.val v.val ∧
        ¬ ((u.val.1 = 0 ∧ 0 ≤ u.val.2 ∧ u.val.2 ≤ n) ∧
           (v.val.1 = 0 ∧ 0 ≤ v.val.2 ∧ v.val.2 ≤ n)) := by
  rw [show (slitBoxGraph n).Adj u v ↔
      (rectangleGraph (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n)).Adj u v ∧
        ¬ (u ∈ slitBoxWiredArc n ∧ v ∈ slitBoxWiredArc n) from Iff.rfl,
    rectangleGraph_adj_iff, mem_slitBoxWiredArc_iff, mem_slitBoxWiredArc_iff]

/-- The Dobrushin boundary condition wires precisely the retained slit arc. -/
def slitBoxBoundary (n : ℕ) : BoundaryCondition (SlitBoxVertex n) :=
  BoundaryCondition.wired (slitBoxWiredArc n : Set (SlitBoxVertex n))

/-- Actual open connectivity from a retained vertex to the wired arc. Wiring
is recorded separately in `slitBoxBoundary` and does not itself make paths. -/
def slitBoxWiredArcConnectionEvent (n : ℕ) (u : SlitBoxVertex n) :
    Set (Configuration (slitBoxGraph n)) :=
  {A | ∃ v ∈ slitBoxWiredArc n, ActualConnected (slitBoxGraph n) A u v}

theorem slitBoxWiredArcConnectionEvent_mono (n : ℕ) (u : SlitBoxVertex n)
    {A B : Configuration (slitBoxGraph n)} (hAB : A ⊆ B)
    (hA : A ∈ slitBoxWiredArcConnectionEvent n u) :
    B ∈ slitBoxWiredArcConnectionEvent n u := by
  rcases hA with ⟨v, hv, hpath⟩
  exact ⟨v, hv, actualConnected_mono hAB hpath⟩

end PottsContinuity.FKC.FiniteFK
