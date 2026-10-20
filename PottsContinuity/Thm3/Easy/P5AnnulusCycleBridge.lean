module

public import PottsContinuity.DualityExt.PositivePolygonLatticeCycle
public import PottsContinuity.FKC.Domains.LatticePolygonOfCycle

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open PottsContinuity.DualityExt
open PottsContinuity.FKC
open SimpleGraph

private theorem polygonCyclicList_nonempty' {m : ℕ} (P : LatticePolygon m) :
    polygonCyclicList P ≠ [] := by
  simp [polygonCyclicList]

private theorem polygonCyclicList_chain' {m : ℕ} (P : LatticePolygon m) :
    (polygonCyclicList P).IsChain squareLattice.Adj := by
  change (List.ofFn (fun i : Fin (m + 3) =>
    P.vertex (i.val : ZMod (m + 3)))).IsChain squareLattice.Adj
  rw [List.isChain_ofFn]
  intro i hi
  change squareLattice.Adj
    (P.vertex (i : ZMod (m + 3)))
    (P.vertex ((i + 1 : ℕ) : ZMod (m + 3)))
  rw [Nat.cast_add]
  exact P.adjacent (i : ZMod (m + 3))

private theorem polygonCyclicWalk_length {m : ℕ} (P : LatticePolygon m) :
    (polygonCyclicWalk P).length = m + 2 := by
  change (Walk.ofSupport (polygonCyclicList P)
    (polygonCyclicList_nonempty' P) (polygonCyclicList_chain' P)).length = _
  rw [Walk.length_ofSupport]
  simp [polygonCyclicList]

 noncomputable def p5aForwardPolygonCycle {m : ℕ} (P : LatticePolygon m) :=
  (polygonCycle P).reverse

private theorem p5aForwardPolygonCycle_isCycle {m : ℕ} (P : LatticePolygon m) :
    (p5aForwardPolygonCycle P).IsCycle :=
  (polygonCycle_isCycle P).reverse

end PottsContinuity.Thm3.Easy
