module

public import PottsContinuity.BD12.RectangleOpenGraphs
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Contracting the dangling side ports of the true rectangle dual

The projection clamps the horizontal coordinate to the strip between the
bottom/top ports. Every true-dual edge is either unchanged or contracted.
-/

@[expose] public section

namespace PottsContinuity.BD12

open PD.FK PD.FK.Medial PD.Duality PD.RCInfinite

/-- Horizontal nearest-point projection onto the dual crossing strip. -/
def dualStripClamp (a : LatticeVertex) (n : ℕ) (z : LatticeVertex) : LatticeVertex :=
  (max a.1 (min (a.1 + (n : ℤ)) z.1), z.2)

theorem dualStripClamp_eq (a : LatticeVertex) (n : ℕ) (z : LatticeVertex)
    (hz : a.1 ≤ z.1 ∧ z.1 ≤ a.1 + (n : ℤ)) : dualStripClamp a n z = z := by
  apply Prod.ext
  · simp only [dualStripClamp, min_eq_right hz.2, max_eq_right hz.1]
  · rfl

theorem dualStripClamp_bond (a : LatticeVertex) (n h : ℕ) (b : LatticeBond)
    (hb : b.source ∈ latticeRectangle a (n + 1) h ∧
      b.target ∈ latticeRectangle a (n + 1) h) :
    dualStripClamp a n (dualBondOfPrimal b).source =
        dualStripClamp a n (dualBondOfPrimal b).target ∨
      (dualStripClamp a n (dualBondOfPrimal b).source = (dualBondOfPrimal b).source ∧
       dualStripClamp a n (dualBondOfPrimal b).target = (dualBondOfPrimal b).target) := by
  rcases b with ⟨⟨x, y⟩, ax⟩
  cases ax
  · right
    simp only [LatticeBond.source, LatticeBond.target, mem_latticeRectangle] at hb
    constructor <;> apply dualStripClamp_eq <;>
      simp only [dualBondOfPrimal, LatticeBond.source, LatticeBond.target] <;> omega
  · simp only [LatticeBond.source, LatticeBond.target, mem_latticeRectangle] at hb
    by_cases hx : x ≤ a.1
    · left
      apply Prod.ext
      · simp only [dualStripClamp, dualBondOfPrimal, LatticeBond.source, LatticeBond.target]
        omega
      · rfl
    · by_cases hx' : a.1 + (n : ℤ) < x
      · left
        apply Prod.ext
        · simp only [dualStripClamp, dualBondOfPrimal, LatticeBond.source, LatticeBond.target]
          omega
        · rfl
      · right
        constructor <;> apply dualStripClamp_eq <;>
          simp only [dualBondOfPrimal, LatticeBond.source, LatticeBond.target] <;> omega

/-- Projection of every expanded dual vertex into the ordinary crossing strip. -/
def dualStripProjection (a : LatticeVertex) (n h : ℕ)
    (z : RectangleDualVertex a (n + 1) h) :
    RectangleVertex (a.1, a.2 - 1) n (h + 1) := by
  refine ⟨dualStripClamp a n z.val, ?_⟩
  have hz := z.property
  simp only [rectangleDualExpanded, mem_latticeRectangle, Nat.cast_add, Nat.cast_one] at hz
  simp only [mem_latticeRectangle, dualStripClamp, Nat.cast_add, Nat.cast_one]
  omega

theorem dualStripProjection_edge (a : LatticeVertex) (n h : ℕ)
    {u v : RectangleDualVertex a (n + 1) h}
    (huv : (rectangleDualGraph a (n + 1) h).Adj u v) :
    dualStripProjection a n h u = dualStripProjection a n h v ∨
      ((dualStripProjection a n h u).val = u.val ∧
       (dualStripProjection a n h v).val = v.val) := by
  obtain ⟨e, he⟩ := (rectangleDualGraph_adj_iff a (n + 1) h u v).mp huv
  have hp := (rectanglePrimalEdgeBondEquiv a (n + 1) h e.primalEdge).property
  have hc := dualStripClamp_bond a n h (rectanglePrimalEdgeBond a (n + 1) h e.primalEdge) hp
  have he' : s(u.val, v.val) = s(e.crossingBond.source, e.crossingBond.target) := by
    simpa only [rectangleDualCarrierPair, Sym2.map_mk, rectangleDualEdgeSource_val,
      rectangleDualEdgeTarget_val] using congrArg (Sym2.map Subtype.val) he
  rw [← rectangleCrossingDualBond, ← e.crossingBond_eq] at hc
  rcases Sym2.eq_iff.mp he' with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rcases hc with hc | ⟨hs, ht⟩
    · left
      apply Subtype.ext
      change dualStripClamp a n u.val = dualStripClamp a n v.val
      simpa only [hu, hv] using hc
    · right
      change dualStripClamp a n u.val = u.val ∧ dualStripClamp a n v.val = v.val
      simpa only [hu, hv] using And.intro hs ht
  · rcases hc with hc | ⟨hs, ht⟩
    · left
      apply Subtype.ext
      change dualStripClamp a n u.val = dualStripClamp a n v.val
      simpa only [hu, hv] using hc.symm
    · right
      change dualStripClamp a n u.val = u.val ∧ dualStripClamp a n v.val = v.val
      simpa only [hu, hv] using And.intro ht hs

end PottsContinuity.BD12
