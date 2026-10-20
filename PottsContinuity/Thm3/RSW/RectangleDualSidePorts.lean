module

public import PottsContinuity.PD.Duality.RectangleDualAmbient
public import PottsContinuity.PD.Duality.RectangleFlowDimension
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Int.Star

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial

/-- A genuine vertical dual edge has its horizontal face coordinate in the
internal interval. Expanded side-port vertices have no vertical edges. -/
theorem rectangleDual_vertical_edge_horizontal_inside
    (a : LatticeVertex) (w h : ℕ) (u v : RectangleDualVertex a w h)
    (hadj : (rectangleDualGraph a w h).Adj u v) (hx : u.val.1 = v.val.1) :
    a.1 ≤ u.val.1 ∧ u.val.1 < a.1+(w:ℤ) := by
  obtain ⟨e,he⟩ := (rectangleDualGraph_adj_iff a w h u v).mp hadj
  have hpair := congrArg (Sym2.map (fun z : RectangleDualVertex a w h => z.val)) he
  have hs := rectanglePrimalEdgeBond_endpoints_mem_public a w h e.primalEdge
  have hp : s(u.val,v.val) =
      s((dualBondOfPrimal (rectanglePrimalEdgeBond a w h e.primalEdge)).source,
        (dualBondOfPrimal (rectanglePrimalEdgeBond a w h e.primalEdge)).target) := by
    simpa [rectangleDualCarrierPair,rectangleDualEdgeSource_val,
      rectangleDualEdgeTarget_val,e.crossingBond_eq,rectangleCrossingDualBond] using hpair
  generalize hb : rectanglePrimalEdgeBond a w h e.primalEdge = b at hp hs
  rcases b with ⟨⟨x,y⟩,axis⟩
  cases axis <;>
    simp only [dualBondOfPrimal,LatticeBond.source,LatticeBond.target] at hp hs
  all_goals
    rw [mem_latticeRectangle,mem_latticeRectangle] at hs
    rcases Sym2.eq_iff.mp hp with ⟨hu,hv⟩ | ⟨hu,hv⟩
    all_goals
      have hux := congrArg Prod.fst hu
      have hvx := congrArg Prod.fst hv
      dsimp at hux hvx
      omega

/-- Clamping the horizontal face coordinate only collapses side-port edges;
any edge whose endpoints remain distinct keeps both original vertices. -/
theorem rectangleDual_horizontal_clamp_edge
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w)
    (u v : RectangleDualVertex a w h) (hadj : (rectangleDualGraph a w h).Adj u v) :
    (max a.1 (min (a.1+(w:ℤ)-1) u.val.1),u.val.2) =
      (max a.1 (min (a.1+(w:ℤ)-1) v.val.1),v.val.2) ∨
    ((max a.1 (min (a.1+(w:ℤ)-1) u.val.1),u.val.2) = u.val ∧
      (max a.1 (min (a.1+(w:ℤ)-1) v.val.1),v.val.2) = v.val) := by
  have hu : u.val ∈ rectangleDualExpanded a w h := u.property
  have hv : v.val ∈ rectangleDualExpanded a w h := v.property
  change u.val ∈ PD.FK.latticeRectangle (a.1-1,a.2-1) (w+1) (h+1) at hu
  change v.val ∈ PD.FK.latticeRectangle (a.1-1,a.2-1) (w+1) (h+1) at hv
  rw [mem_latticeRectangle] at hu hv
  have hs := rectangleDualGraph_le_ambient a w h hadj
  change |u.val.1-v.val.1|+|u.val.2-v.val.2|=1 at hs
  have hw' : 1 ≤ (w:ℤ) := by exact_mod_cast hw
  have hstep : |u.val.1-v.val.1| ≤ 1 := by
    have hypos := abs_nonneg (u.val.2-v.val.2)
    linarith only [hs,hypos]
  have hstep' := abs_le.mp hstep
  by_cases hy : u.val.2 = v.val.2
  · by_cases hc : max a.1 (min (a.1+(w:ℤ)-1) u.val.1) =
        max a.1 (min (a.1+(w:ℤ)-1) v.val.1)
    · exact Or.inl (Prod.ext hc hy)
    · right
      have hu' : max a.1 (min (a.1+(w:ℤ)-1) u.val.1) = u.val.1 := by
        simp only [max_def,min_def] at hc ⊢
        split_ifs at hc ⊢ <;> omega
      have hv' : max a.1 (min (a.1+(w:ℤ)-1) v.val.1) = v.val.1 := by
        simp only [max_def,min_def] at hc ⊢
        split_ifs at hc ⊢ <;> omega
      exact ⟨Prod.ext hu' rfl,Prod.ext hv' rfl⟩
  · have hypos : 1 ≤ |u.val.2-v.val.2| := by
      have hh := abs_pos.mpr (sub_ne_zero.mpr hy)
      omega
    have hxzero : |u.val.1-v.val.1| = 0 := by
      have hnonneg := abs_nonneg (u.val.1-v.val.1)
      linarith only [hs,hypos,hnonneg]
    have hx : u.val.1 = v.val.1 := sub_eq_zero.mp (abs_eq_zero.mp hxzero)
    have hi := rectangleDual_vertical_edge_horizontal_inside a w h u v hadj hx
    right
    have hu' : max a.1 (min (a.1+(w:ℤ)-1) u.val.1) = u.val.1 := by
      rw [min_eq_right (by omega),max_eq_right hi.1]
    have hv' : max a.1 (min (a.1+(w:ℤ)-1) v.val.1) = v.val.1 := by
      rw [← hx]
      exact hu'
    exact ⟨Prod.ext hu' rfl,Prod.ext hv' rfl⟩

end PottsContinuity.RSW
