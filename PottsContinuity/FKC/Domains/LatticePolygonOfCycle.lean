-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticePolygonOfCycle.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.LatticePolygon
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.FKC

open SimpleGraph

/-- The ordered vertices of a square-lattice simple cycle define the
corresponding cyclic lattice polygon. -/
noncomputable def latticePolygonOfCycle {v : LatticeVertex} {p : squareLattice.Walk v v}
    (h : p.IsCycle) : LatticePolygon (p.length - 3) := by
  let m := p.length - 3
  have hlen : m + 3 = p.length := by
    have h3 := h.three_le_length
    dsimp [m]
    omega
  refine {
    vertex := fun i => p.getVert i.val
    vertex_injective := ?_
    adjacent := ?_ }
  · intro i j hij
    apply ZMod.val_injective
    apply h.getVert_injOn'
    · rw [Set.mem_ofPred_eq]
      have hi : i.val < p.length := calc
        i.val < m + 3 := i.val_lt
        _ = p.length := hlen
      omega
    · rw [Set.mem_ofPred_eq]
      have hj : j.val < p.length := calc
        j.val < m + 3 := j.val_lt
        _ = p.length := hlen
      omega
    exact hij
  · intro i
    have hpos : 0 < p.length := by omega
    let : NeZero (m + 3) := ⟨by omega⟩
    let : Fact (1 < m + 3) := ⟨by omega⟩
    change squareLattice.Adj (p.getVert i.val) (p.getVert (i + 1).val)
    by_cases hnext : i.val + 1 < p.length
    · have hval : (i + 1).val = i.val + 1 := by
        have hsmall : i.val + (1 : ℕ) < m + 3 := by
          have hi := i.val_lt
          omega
        rw [ZMod.val_add_of_lt hsmall]
        rw [ZMod.val_one]
      rw [hval]
      exact p.adj_getVert_succ (by omega)
    · have hlast : i.val + 1 = p.length := by
        have hi : i.val < p.length := calc
          i.val < m + 3 := i.val_lt
          _ = p.length := hlen
        omega
      have hval : (i + 1).val = 0 := by
        have hle : m + 3 ≤ i.val + (1 : ℕ) := by
          have hi := i.val_lt
          omega
        rw [ZMod.val_add_of_le hle]
        rw [ZMod.val_one]
        omega
      rw [hval]
      have hadj := p.adj_getVert_succ (by omega : i.val < p.length)
      rw [hlast] at hadj
      simpa using hadj

/-- Successive polygon vertices are the corresponding consecutive vertices
of the original walk, including the closing edge. -/
theorem latticePolygonOfCycle_vertex_succ {v : LatticeVertex}
    {p : squareLattice.Walk v v} (h : p.IsCycle)
    (i : ZMod (p.length - 3 + 3)) :
    (latticePolygonOfCycle h).vertex (i + 1) = p.getVert (i.val + 1) := by
  have hlen : p.length - 3 + 3 = p.length := by
    have h3 := h.three_le_length
    omega
  let : Fact (1 < p.length - 3 + 3) := ⟨by rw [hlen]; omega⟩
  change p.getVert (i + 1).val = p.getVert (i.val + 1)
  by_cases hnext : i.val + 1 < p.length
  · have hsmall : i.val + (1 : ℕ) < p.length - 3 + 3 := by omega
    rw [ZMod.val_add_of_lt hsmall, ZMod.val_one]
  · have hlast : i.val + 1 = p.length := by
      have hi : i.val < p.length := by
        calc
          i.val < p.length - 3 + 3 := i.val_lt
          _ = p.length := hlen
      omega
    have hwrap : (i + 1).val = 0 := by
      have hle : p.length - 3 + 3 ≤ i.val + (1 : ℕ) := by
        have hi := i.val_lt
        omega
      rw [ZMod.val_add_of_le hle, ZMod.val_one]
      omega
    rw [hwrap]
    rw [hlast, p.getVert_length]
    simp

/-- The set of polygon vertices is exactly the set of vertices visited by
the original closed walk. -/
theorem latticePolygonOfCycle_vertex_range {v : LatticeVertex}
    {p : squareLattice.Walk v v} (h : p.IsCycle) :
    Set.range (latticePolygonOfCycle h).vertex = Set.range p.getVert := by
  have hlen : p.length - 3 + 3 = p.length := by
    have h3 := h.three_le_length
    omega
  let : Fact (1 < p.length - 3 + 3) := ⟨by rw [hlen]; omega⟩
  change Set.range (fun i : ZMod (p.length - 3 + 3) => p.getVert i.val) = _
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, rfl⟩
  · rintro ⟨n, rfl⟩
    by_cases hn : n < p.length
    · let i : ZMod (p.length - 3 + 3) := n
      have hi : i.val = n := by
        simp [i, ZMod.val_natCast, Nat.mod_eq_of_lt hn, hlen]
      exact ⟨i, by simp [hi]⟩
    · have hv : p.getVert n = v := p.getVert_of_length_le (Nat.le_of_not_gt hn)
      refine ⟨0, ?_⟩
      simp [hv]

/-- The polygon vertex range is the exact support range of the original
walk, preserving its traversal-derived support. -/
theorem latticePolygonOfCycle_vertex_support {v : LatticeVertex}
    {p : squareLattice.Walk v v} (h : p.IsCycle) :
    Set.range (latticePolygonOfCycle h).vertex = Set.range p.support.get := by
  rw [latticePolygonOfCycle_vertex_range h, p.range_getVert_eq_range_support_getElem]

/-- The unoriented edges of the ordered polygon are exactly the edges
traversed by the original cycle. -/
theorem latticePolygonOfCycle_edge_iff {v : LatticeVertex}
    {p : squareLattice.Walk v v} (h : p.IsCycle)
    (e : Sym2 LatticeVertex) :
    e ∈ p.edges ↔
      ∃ i : ZMod (p.length - 3 + 3),
        e = s((latticePolygonOfCycle h).vertex i,
          (latticePolygonOfCycle h).vertex (i + 1)) := by
  have hlen : p.length - 3 + 3 = p.length := by
    have h3 := h.three_le_length
    omega
  let : Fact (1 < p.length - 3 + 3) := ⟨by rw [hlen]; omega⟩
  induction e using Sym2.ind with
  | h a b =>
    change s(a, b) ∈ p.edges ↔
      ∃ i : ZMod (p.length - 3 + 3),
        s(a, b) = s((latticePolygonOfCycle h).vertex i,
          (latticePolygonOfCycle h).vertex (i + 1))
    rw [p.mk_mem_edges_iff_exists]
    constructor
    · rintro ⟨k, hk, he⟩
      let i : ZMod (p.length - 3 + 3) := k
      have hi : i.val = k := by
        have hkmod : k < p.length - 3 + 3 := by omega
        simp [i, ZMod.val_natCast, Nat.mod_eq_of_lt hkmod]
      refine ⟨i, ?_⟩
      rw [latticePolygonOfCycle_vertex_succ h i]
      change s(a, b) = s(p.getVert i.val, p.getVert (i.val + 1))
      rw [hi]
      exact he.symm
    · rintro ⟨i, he⟩
      refine ⟨i.val, ?_, ?_⟩
      · calc
          i.val < p.length - 3 + 3 := i.val_lt
          _ = p.length := hlen
      · rw [latticePolygonOfCycle_vertex_succ h i] at he
        change s(a, b) = s(p.getVert i.val, p.getVert (i.val + 1)) at he
        exact he.symm

end PottsContinuity.FKC
