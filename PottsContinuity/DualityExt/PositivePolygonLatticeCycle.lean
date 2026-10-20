module

public import PottsContinuity.FKC.Domains.LatticePolygon
public import Mathlib.Data.List.ChainOfFn
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.GetD
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.DualityExt
open PottsContinuity.FKC
open SimpleGraph
noncomputable section

def polygonCyclicList {m : ℕ} (P : LatticePolygon m) : List LatticeVertex :=
  List.ofFn (fun i : Fin (m + 3) => P.vertex (i.val : ZMod (m + 3)))

def polygonLastIndex (m : ℕ) : ZMod (m + 3) := (Fin.last (m + 2)).val

 theorem polygonCyclicList_nonempty {m : ℕ} (P : LatticePolygon m) :
    polygonCyclicList P ≠ [] := by
  simp [polygonCyclicList]

 theorem polygonCyclicList_chain {m : ℕ} (P : LatticePolygon m) :
    (polygonCyclicList P).IsChain squareLattice.Adj := by
  change (List.ofFn (fun i : Fin (m + 3) => P.vertex (i.val : ZMod (m + 3)))).IsChain squareLattice.Adj
  rw [List.isChain_ofFn]
  intro i hi
  change squareLattice.Adj
    (P.vertex (i : ZMod (m + 3)))
    (P.vertex ((i + 1 : ℕ) : ZMod (m + 3)))
  rw [Nat.cast_add]
  exact P.adjacent (i : ZMod (m + 3))

def polygonCyclicWalk {m : ℕ} (P : LatticePolygon m) :=
  SimpleGraph.Walk.ofSupport (polygonCyclicList P) (polygonCyclicList_nonempty P)
    (polygonCyclicList_chain P)

private theorem polygonCyclicList_head {m : ℕ} (P : LatticePolygon m) :
    (polygonCyclicList P).head (polygonCyclicList_nonempty P) = P.vertex 0 := by
  simp [polygonCyclicList]

private theorem polygonCyclicList_last {m : ℕ} (P : LatticePolygon m) :
    (polygonCyclicList P).getLast (polygonCyclicList_nonempty P) =
      P.vertex (polygonLastIndex m) := by
  change (List.ofFn (fun i : Fin ((m + 2).succ) => P.vertex (i.val : ZMod (m + 3)))).getLast _ = _
  rw [List.getLast_ofFn_succ]
  rfl

private theorem polygonLastIndex_succ (m : ℕ) : polygonLastIndex m + 1 = 0 := by
  change ((m + 2 : ℕ) : ZMod (m + 3)) + 1 = 0
  have hcast : ((m + 2 : ℕ) : ZMod (m + 3)) + 1 = (m + 3 : ℕ) := by
    push_cast
    ring
  rw [hcast]
  exact ZMod.natCast_self (m + 3)

 theorem polygonCyclicClosingAdj {m : ℕ} (P : LatticePolygon m) :
    squareLattice.Adj
      ((polygonCyclicList P).head (polygonCyclicList_nonempty P))
      ((polygonCyclicList P).getLast (polygonCyclicList_nonempty P)) := by
  rw [polygonCyclicList_head, polygonCyclicList_last]
  rw [← polygonLastIndex_succ m]
  exact (P.adjacent (polygonLastIndex m)).symm

noncomputable def polygonCycle {m : ℕ} (P : LatticePolygon m) :
    squareLattice.Walk
      ((polygonCyclicList P).head (polygonCyclicList_nonempty P))
      ((polygonCyclicList P).head (polygonCyclicList_nonempty P)) :=
  Walk.cons (polygonCyclicClosingAdj P) (polygonCyclicWalk P).reverse

theorem polygonCyclicWalk_isPath {m : ℕ} (P : LatticePolygon m) :
    (polygonCyclicWalk P).IsPath := by
  rw [Walk.isPath_def]
  have : NeZero (m + 3) := ⟨by omega⟩
  have hinj : Function.Injective (fun i : Fin (m + 3) => P.vertex (i.val : ZMod (m + 3))) := by
    intro i j hij
    apply Fin.ext
    have hcast : (i.val : ZMod (m + 3)) = (j.val : ZMod (m + 3)) :=
      P.vertex_injective hij
    have hv := congrArg ZMod.val hcast
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt,
      ZMod.val_natCast, Nat.mod_eq_of_lt j.isLt] at hv
    exact hv
  have hnd : (polygonCyclicList P).Nodup := by
    change (List.ofFn (fun i : Fin (m + 3) => P.vertex (i.val : ZMod (m + 3)))).Nodup
    exact List.nodup_ofFn_ofInjective hinj
  simpa [polygonCyclicWalk, Walk.support_ofSupport] using hnd

theorem polygonCycle_isCycle {m : ℕ} (P : LatticePolygon m) :
    (polygonCycle P).IsCycle := by
  rw [polygonCycle, Walk.cons_isCycle_iff]
  constructor
  · exact (polygonCyclicWalk_isPath P).reverse
  · intro he
    rw [Walk.edges_reverse, List.mem_reverse] at he
    let p := polygonCyclicWalk P
    obtain ⟨i, hi, hEq⟩ := (Walk.mk_mem_edges_iff_exists p).mp he
    have hlen : p.length = m + 2 := by
      change (Walk.ofSupport (polygonCyclicList P)
        (polygonCyclicList_nonempty P) (polygonCyclicList_chain P)).length = m + 2
      rw [Walk.length_ofSupport]
      simp [polygonCyclicList]
    have hiBound : i < m + 2 := by omega
    have hiNotLast : (i : ZMod (m + 3)) ≠ polygonLastIndex m := by
      intro h
      have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at hv
      have hlastval : (polygonLastIndex m).val = m + 2 := by
        change ((m + 2 : ℕ) : ZMod (m + 3)).val = m + 2
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      rw [hlastval] at hv
      omega
    have hget (j : ℕ) (hj : j ≤ m + 2) : p.getVert j = P.vertex (j : ZMod (m + 3)) := by
      change (Walk.ofSupport (polygonCyclicList P)
        (polygonCyclicList_nonempty P) (polygonCyclicList_chain P)).getVert j = _
      rw [Walk.getVert_eq_getD_support]
      rw [Walk.support_ofSupport (polygonCyclicList_nonempty P) (polygonCyclicList_chain P)]
      change (List.ofFn (fun k : Fin (m + 3) => P.vertex (k.val : ZMod (m + 3)))).getD j _ = _
      have hlistlen : (List.ofFn (fun k : Fin (m + 3) =>
          P.vertex (k.val : ZMod (m + 3)))).length = m + 3 := by simp
      have hjlt : j < (List.ofFn (fun k : Fin (m + 3) =>
          P.vertex (k.val : ZMod (m + 3)))).length := by rw [hlistlen]; omega
      rw [List.getD_eq_getElem _ _ hjlt]
      rw [List.getElem_ofFn]
    have hstart := hget i (by omega)
    have hnext := hget (i+1) (by omega)
    have hhead := polygonCyclicList_head P
    have hlast := polygonCyclicList_last P
    have hEq' : s(P.vertex (i : ZMod (m + 3)), P.vertex ((i + 1 : ℕ) : ZMod (m + 3))) =
        s(P.vertex 0, P.vertex (polygonLastIndex m)) := by
      calc
        _ = s(p.getVert i, p.getVert (i+1)) := by rw [hstart, hnext]
        _ = s((polygonCyclicList P).head (polygonCyclicList_nonempty P),
            (polygonCyclicList P).getLast (polygonCyclicList_nonempty P)) := hEq
        _ = _ := by rw [hhead, hlast]
    have hEdge : s(P.vertex (i : ZMod (m + 3)), P.vertex ((i + 1 : ℕ) : ZMod (m + 3))) =
        s(P.vertex (polygonLastIndex m), P.vertex (polygonLastIndex m + 1)) := by
      have hsym : s(P.vertex 0, P.vertex (polygonLastIndex m)) =
          s(P.vertex (polygonLastIndex m), P.vertex 0) :=
        Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)
      have hright : s(P.vertex 0, P.vertex (polygonLastIndex m)) =
          s(P.vertex (polygonLastIndex m), P.vertex (polygonLastIndex m + 1)) := by
        rw [polygonLastIndex_succ]
        exact hsym
      calc
        _ = _ := hEq'
        _ = _ := hright
    rw [Nat.cast_add] at hEdge
    exact (P.edge_ne hiNotLast) hEdge

end
end PottsContinuity.DualityExt
