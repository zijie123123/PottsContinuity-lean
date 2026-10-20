module

public import PottsContinuity.DualityExt.PositivePolygonLatticeCycle
public import PottsContinuity.DualityExt.PositiveP5aPolygonPDWalk

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.FKC
open SimpleGraph

noncomputable section

private theorem polygonCyclicList_chain_local {m : ℕ} (P : LatticePolygon m) :
    (polygonCyclicList P).IsChain FKC.squareLattice.Adj := by
  change (List.ofFn (fun i : Fin (m + 3) =>
    P.vertex (i.val : ZMod (m + 3)))).IsChain FKC.squareLattice.Adj
  rw [List.isChain_ofFn]
  intro i hi
  change FKC.squareLattice.Adj
    (P.vertex (i : ZMod (m + 3)))
    (P.vertex ((i + 1 : ℕ) : ZMod (m + 3)))
  rw [Nat.cast_add]
  exact P.adjacent (i : ZMod (m + 3))

private theorem polygonCyclicWalk_length_index {m : ℕ} (P : LatticePolygon m) :
    (polygonCyclicWalk P).length = m + 2 := by
  unfold polygonCyclicWalk
  rw [Walk.length_ofSupport]
  simp [polygonCyclicList]

private theorem polygonCyclicWalk_getVert_index {m : ℕ} (P : LatticePolygon m)
    (j : ℕ) (hj : j ≤ m + 2) :
    (polygonCyclicWalk P).getVert j = P.vertex (j : ZMod (m + 3)) := by
  unfold polygonCyclicWalk
  rw [Walk.getVert_eq_getD_support]
  rw [Walk.support_ofSupport (by simp [polygonCyclicList])
    (polygonCyclicList_chain_local P)]
  change (List.ofFn (fun k : Fin (m + 3) =>
    P.vertex (k.val : ZMod (m + 3)))).getD j _ = _
  have hlen : (List.ofFn (fun k : Fin (m + 3) =>
      P.vertex (k.val : ZMod (m + 3)))).length = m + 3 := by simp
  have hjlt : j < (List.ofFn (fun k : Fin (m + 3) =>
      P.vertex (k.val : ZMod (m + 3)))).length := by
    rw [hlen]
    omega
  rw [List.getD_eq_getElem _ _ hjlt, List.getElem_ofFn]

private theorem polygonLastIndex_succ_local (m : ℕ) :
    polygonLastIndex m + 1 = 0 := by
  change ((m + 2 : ℕ) : ZMod (m + 3)) + 1 = 0
  have hcast : ((m + 2 : ℕ) : ZMod (m + 3)) + 1 = (m + 3 : ℕ) := by
    push_cast
    ring
  rw [hcast]
  exact ZMod.natCast_self (m + 3)

private theorem polygonCyclicList_head_local {m : ℕ} (P : LatticePolygon m) :
    (polygonCyclicList P).head (by simp [polygonCyclicList]) = P.vertex 0 := by
  simp [polygonCyclicList]

private theorem polygonCyclicList_last_local {m : ℕ} (P : LatticePolygon m) :
    (polygonCyclicList P).getLast (by simp [polygonCyclicList]) =
      P.vertex (polygonLastIndex m) := by
  change (List.ofFn (fun i : Fin ((m + 2).succ) =>
    P.vertex (i.val : ZMod (m + 3)))).getLast _ = _
  rw [List.getLast_ofFn_succ]
  rfl

/-- Every edge in the polygon cycle joins two consecutive cyclic vertices. -/
theorem polygonCycle_edge_index {m : ℕ} (P : LatticePolygon m)
    {u v : FKC.LatticeVertex} (he : s(u, v) ∈ (polygonCycle P).edges) :
    ∃ i : ZMod (m + 3), s(u, v) = s(P.vertex i, P.vertex (i + 1)) := by
  have hparts : s(u, v) = s((polygonCyclicList P).head
      (by simp [polygonCyclicList]), (polygonCyclicList P).getLast
      (by simp [polygonCyclicList])) ∨
      s(u, v) ∈ (polygonCyclicWalk P).edges := by
    have he' := he
    unfold polygonCycle at he'
    rw [Walk.edges_cons, Walk.edges_reverse] at he'
    simp only [List.mem_cons, List.mem_reverse] at he'
    rcases he' with hclose | hpath
    · exact Or.inl hclose
    · exact Or.inr hpath
  rcases hparts with hclose | hpath
  · refine ⟨polygonLastIndex m, ?_⟩
    rw [polygonLastIndex_succ_local]
    calc
      s(u, v) = s(P.vertex 0, P.vertex (polygonLastIndex m)) := by
        simpa only [polygonCyclicList_head_local, polygonCyclicList_last_local] using hclose
      _ = s(P.vertex (polygonLastIndex m), P.vertex 0) :=
        Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)
  · obtain ⟨i, hi, hEq⟩ :=
      (Walk.mk_mem_edges_iff_exists (polygonCyclicWalk P)).mp hpath
    have hlen := polygonCyclicWalk_length_index P
    have hiNext : i + 1 ≤ m + 2 := by omega
    rw [polygonCyclicWalk_getVert_index P i (by omega),
      polygonCyclicWalk_getVert_index P (i + 1) hiNext] at hEq
    rw [Nat.cast_add] at hEq
    refine ⟨(i : ZMod (m + 3)), ?_⟩
    exact hEq.symm

/-- The dual face-base polygon walk uses exactly the indexed polygon edges. -/
theorem p5aPolygonCyclePD_edge_index {m : ℕ} (P : LatticePolygon m)
    {u v : PD.FK.LatticeVertex}
    (he : s(u, v) ∈ (p5aPolygonCyclePD P).edges) :
    ∃ i : ZMod (m + 3), s(u, v) = s(P.vertex i, P.vertex (i + 1)) := by
  unfold p5aPolygonCyclePD at he
  rw [Walk.edges_map] at he
  rcases List.mem_map.mp he with ⟨e', he', hmap⟩
  have heEq : e' = s(u, v) := by
    change Sym2.map id e' = s(u, v) at hmap
    simpa using hmap
  have he'' : s(u, v) ∈ (polygonCycle P).edges := by
    rw [← heEq]
    change e' ∈ (polygonCycle P).reverse.edges at he'
    rw [Walk.edges_reverse, List.mem_reverse] at he'
    exact he'
  exact polygonCycle_edge_index P he''

end

end PottsContinuity.DualityExt
