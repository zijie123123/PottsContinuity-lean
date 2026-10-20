module

public import PottsContinuity.Thm3.RSW.Lemma4SourceEvents
public import PottsContinuity.Thm3.RSW.PolygonRayCell
public import PottsContinuity.DualityExt.PositivePolygonCycleEdgeIndex
public import PottsContinuity.DualityExt.PositiveP5aPolygonPDWalk
public import PottsContinuity.Thm3.Easy.P5AnnulusCycleBridge

@[expose] public section

namespace PottsContinuity.OuterCircuit

open PottsContinuity.PD.FK
open PottsContinuity.FKC
open PottsContinuity.DualityExt

noncomputable section

/-- Reinterpret the lattice walk of a source polygon on the random-cluster
square-lattice carrier. -/
def sourcePolygonToPD : FKC.squareLattice →g PD.FK.squareLattice where
  toFun := id
  map_rel' := by
    intro u v h
    exact (PD.FK.squareLattice_adj_iff u v).2
      ((FKC.squareLattice_adj_iff u v).1 h)

/-- The source polygon boundary, oriented in its given vertex order. -/
def sourcePolygonWalk {m : ℕ} (P : FKC.LatticePolygon m) :=
  (polygonCycle P).reverse.map sourcePolygonToPD

theorem sourcePolygonWalk_eq_p5aPolygonCyclePD {m : ℕ}
    (P : FKC.LatticePolygon m) :
    sourcePolygonWalk P = p5aPolygonCyclePD P := by
  rfl

/-- The polygon boundary walk is simple on the random-cluster carrier. -/
theorem sourcePolygonWalk_isCycle {m : ℕ} (P : FKC.LatticePolygon m) :
    (sourcePolygonWalk P).IsCycle := by
  apply (SimpleGraph.Walk.isCycle_map_iff_of_injective
    (f := sourcePolygonToPD) (by intro a b h; exact h)).2
  exact (polygonCycle_isCycle P).reverse

/-- Every edge of the source polygon boundary walk is one of its indexed
cyclic boundary bonds. -/
theorem sourcePolygonWalk_edge_index {m : ℕ} (P : FKC.LatticePolygon m)
    {u v : PD.FK.LatticeVertex}
    (he : s(u, v) ∈ (sourcePolygonWalk P).edges) :
    ∃ i : ZMod (m + 3), s(u, v) = s(P.vertex i, P.vertex (i + 1)) := by
  change s(u, v) ∈ ((polygonCycle P).reverse.map sourcePolygonToPD).edges at he
  rw [SimpleGraph.Walk.edges_map] at he
  have he'' : s(u, v) ∈ ((polygonCycle P).reverse).edges := by
    simpa [sourcePolygonToPD, Sym2.map_id] using he
  have he''' : s(u, v) ∈ (polygonCycle P).edges := by
    simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using he''
  exact polygonCycle_edge_index P he'''

/-- Reconstructing a source polygon from its walk retains its actual Jordan
domain and ordered lattice vertices. -/
theorem sourcePolygonWalk_onFKC_isCycle {m : ℕ} (P : FKC.LatticePolygon m) :
    ((sourcePolygonWalk P).map RSW.polygonRayLatticeHom).IsCycle := by
  exact (sourcePolygonWalk P).isCycle_map_iff_of_injective
    (f := RSW.polygonRayLatticeHom) (by intro a b h; exact h) |>.2
    (sourcePolygonWalk_isCycle P)

private theorem polygonCyclicWalk_length {m : ℕ} (P : FKC.LatticePolygon m) :
    (polygonCyclicWalk P).length = m + 2 := by
  unfold polygonCyclicWalk
  rw [SimpleGraph.Walk.length_ofSupport]
  simp [polygonCyclicList]

 theorem sourcePolygonWalk_length_sub_three {m : ℕ}
    (P : FKC.LatticePolygon m) :
    ((sourcePolygonWalk P).map RSW.polygonRayLatticeHom).length - 3 = m := by
  simp only [sourcePolygonWalk, SimpleGraph.Walk.length_map,
    SimpleGraph.Walk.length_reverse]
  simp only [polygonCycle, SimpleGraph.Walk.length_cons,
    SimpleGraph.Walk.length_reverse]
  rw [polygonCyclicWalk_length]
  omega

theorem sourcePolygonWalk_onFKC_length {m : ℕ} (P : FKC.LatticePolygon m) :
    ((sourcePolygonWalk P).map RSW.polygonRayLatticeHom).length = m + 3 := by
  have hsub := sourcePolygonWalk_length_sub_three P
  have hcycle := (sourcePolygonWalk_onFKC_isCycle P).three_le_length
  omega

private theorem sourcePolygonCyclicWalk_getVert {m : ℕ}
    (P : FKC.LatticePolygon m) (j : ℕ) (hj : j ≤ m + 2) :
    (polygonCyclicWalk P).getVert j = P.vertex (j : ZMod (m + 3)) := by
  have hnonempty : polygonCyclicList P ≠ [] := by simp [polygonCyclicList]
  have hchain : (polygonCyclicList P).IsChain FKC.squareLattice.Adj := by
    change (List.ofFn (fun i : Fin (m + 3) =>
      P.vertex (i.val : ZMod (m + 3)))).IsChain _
    rw [List.isChain_ofFn]
    intro i hi
    rw [Nat.cast_add]
    exact P.adjacent (i : ZMod (m + 3))
  change (SimpleGraph.Walk.ofSupport (polygonCyclicList P) hnonempty hchain).getVert j = _
  rw [SimpleGraph.Walk.getVert_eq_getD_support,
    SimpleGraph.Walk.support_ofSupport hnonempty hchain]
  change (List.ofFn (fun i : Fin (m + 3) =>
    P.vertex (i.val : ZMod (m + 3)))).getD j _ = _
  have hjlt : j < (List.ofFn (fun i : Fin (m + 3) =>
      P.vertex (i.val : ZMod (m + 3)))).length := by
    simp
    omega
  rw [List.getD_eq_getElem _ _ hjlt, List.getElem_ofFn]

private theorem sourcePolygonForwardWalk_getVert {m : ℕ}
    (P : FKC.LatticePolygon m) (j : ℕ) (hj : j ≤ m + 2) :
    ((polygonCycle P).reverse).getVert j = P.vertex (j : ZMod (m + 3)) := by
  have hlenC : (polygonCycle P).length = m + 3 := by
    simp [polygonCycle, polygonCyclicWalk_length]
  rw [SimpleGraph.Walk.getVert_reverse, hlenC]
  have hpos : m + 3 - j ≠ 0 := by omega
  unfold polygonCycle
  rw [SimpleGraph.Walk.getVert_cons _ _ hpos,
    SimpleGraph.Walk.getVert_reverse]
  have hidx : (polygonCyclicWalk P).length - ((m + 3) - j - 1) = j := by
    rw [polygonCyclicWalk_length]
    omega
  rw [hidx]
  exact sourcePolygonCyclicWalk_getVert P j hj

private theorem sourcePolygonWalk_getVert {m : ℕ}
    (P : FKC.LatticePolygon m) (j : ℕ) (hj : j ≤ m + 2) :
    ((sourcePolygonWalk P).map RSW.polygonRayLatticeHom).getVert j =
      P.vertex (j : ZMod (m + 3)) := by
  rw [sourcePolygonWalk, SimpleGraph.Walk.getVert_map,
    SimpleGraph.Walk.getVert_map]
  simp only [sourcePolygonToPD, RSW.polygonRayLatticeHom]
  exact sourcePolygonForwardWalk_getVert P j hj

private theorem source_latticePolygon_eq_of_vertex_eq {m : ℕ}
    {P Q : FKC.LatticePolygon m} (h : P.vertex = Q.vertex) : P = Q := by
  cases P with
  | mk vertex₁ injective₁ adjacent₁ =>
    cases Q with
    | mk vertex₂ injective₂ adjacent₂ =>
      change vertex₁ = vertex₂ at h
      cases h
      rfl

private theorem source_latticePolygonOfCycle_heq_of_getVert
    {m : ℕ} {z : FKC.LatticeVertex}
    (p : FKC.squareLattice.Walk z z) (hp : p.IsCycle)
    (hlen : p.length - 3 = m) (P : FKC.LatticePolygon m)
    (hvertex : ∀ i : ZMod (m + 3), p.getVert i.val = P.vertex i) :
    HEq (FKC.latticePolygonOfCycle hp) P := by
  revert hvertex P
  cases hlen
  intro P hvertex
  have hv : (FKC.latticePolygonOfCycle hp).vertex = P.vertex := by
    funext i
    calc
      (FKC.latticePolygonOfCycle hp).vertex i = p.getVert i.val := rfl
      _ = P.vertex i := hvertex i
  exact heq_of_eq (source_latticePolygon_eq_of_vertex_eq hv)

private theorem source_cast_latticePolygon_heq {a b : ℕ} (h : a = b)
    (P : FKC.LatticePolygon a) : HEq (h ▸ P) P := by
  cases h
  rfl

/-- Reconstructing a polygon from its walk retains its vertex order. -/
noncomputable def sourcePolygonWalkPolygon {m : ℕ} (P : FKC.LatticePolygon m) :
    FKC.LatticePolygon m :=
  sourcePolygonWalk_length_sub_three P ▸
    FKC.latticePolygonOfCycle (sourcePolygonWalk_onFKC_isCycle P)

/-- The walk reconstruction is the original polygon, including its ordered
boundary vertices. -/
theorem sourcePolygonWalk_recovered_polygon_eq {m : ℕ}
    (P : FKC.LatticePolygon m) : sourcePolygonWalkPolygon P = P := by
  unfold sourcePolygonWalkPolygon
  let p := (sourcePolygonWalk P).map RSW.polygonRayLatticeHom
  have hp : p.IsCycle := sourcePolygonWalk_onFKC_isCycle P
  have hlen := sourcePolygonWalk_length_sub_three P
  have hlenExact : p.length = m + 3 := by
    dsimp [p]
    exact sourcePolygonWalk_onFKC_length P
  have hvertex : ∀ i : ZMod (m + 3), p.getVert i.val = P.vertex i := by
    intro i
    dsimp [p]
    simpa using sourcePolygonWalk_getVert P i.val (by have hi := i.val_lt; omega)
  have hpoly : HEq (FKC.latticePolygonOfCycle hp) P :=
    source_latticePolygonOfCycle_heq_of_getVert p hp hlen P hvertex
  exact eq_of_heq ((source_cast_latticePolygon_heq hlen
    (FKC.latticePolygonOfCycle hp)).trans hpoly)

/-- The source walk visits each indexed polygon vertex in its cyclic order. -/
theorem sourcePolygonWalk_indexed_vertex {m : ℕ}
    (P : FKC.LatticePolygon m) (j : Fin (m + 3)) :
    (sourcePolygonWalk P).getVert j.val = P.vertex (j.val : ZMod (m + 3)) := by
  have h := sourcePolygonWalk_getVert P j.val (by have hj := j.isLt; omega)
  rw [SimpleGraph.Walk.getVert_map] at h
  simpa [RSW.polygonRayLatticeHom] using h

end
end PottsContinuity.OuterCircuit
