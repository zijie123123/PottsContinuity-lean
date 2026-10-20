module

public import PottsContinuity.PlanarTopology.SampledDualScreenSeparation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial
noncomputable section

/-- Closure of a genuine original sampled bond, including its actual domain
membership. Unsampled bonds do not satisfy this predicate. -/
def rectangleSampledBondClosed (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (b : LatticeBond) : Prop :=
  ∃ c : RectanglePrimalBond a w h, c.val = b ∧ rectanglePrimalBondToEdge a w h c ∉ A

/-- Each closed original cut row supplies its genuine vertical dual edge. -/
theorem sampled_closed_horizontal_row_dual_adj (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (k y : ℤ)
    (hc : rectangleSampledBondClosed a w h A ⟨(k,y),.horizontal⟩) :
    (rectangleSampledClosedDualGraph a w h A).Adj (k,y-1) (k,y) := by
  obtain ⟨b,hb,hclosed⟩ := hc
  have he := rectangleSampledClosedDualGraph_adj_of_closed_bond a w h A b hclosed
  simpa only [hb,dualBondOfPrimal,LatticeBond.source,LatticeBond.target,Int.sub_add_cancel] using he

/-- Each closed original vertical bond supplies its genuine horizontal dual edge. -/
theorem sampled_closed_vertical_column_dual_adj (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (x y : ℤ)
    (hc : rectangleSampledBondClosed a w h A ⟨(x,y),.vertical⟩) :
    (rectangleSampledClosedDualGraph a w h A).Adj (x-1,y) (x,y) := by
  obtain ⟨b,hb,hclosed⟩ := hc
  have he := rectangleSampledClosedDualGraph_adj_of_closed_bond a w h A b hclosed
  simpa only [hb,dualBondOfPrimal,LatticeBond.source,LatticeBond.target,Int.sub_add_cancel] using he

-- Adapted from Thm3.Prop4.ClosedRowsDual: retain sampled-bond membership at every step.
private theorem sampled_closed_rows_nat (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (k lo : ℤ) (m : ℕ)
    (hc : ∀ y : ℤ, lo ≤ y → y ≤ lo+(m : ℤ) →
      rectangleSampledBondClosed a w h A ⟨(k,y),.horizontal⟩) :
    (rectangleSampledClosedDualGraph a w h A).Reachable (k,lo-1) (k,lo+(m : ℤ)) := by
  induction m with
  | zero =>
    simpa only [Nat.cast_zero,add_zero] using
      (sampled_closed_horizontal_row_dual_adj a w h A k lo (hc lo le_rfl (by simp))).reachable
  | succ m ih =>
    have hleft := ih (fun y hy0 hy1 => hc y hy0 (by omega))
    have hstep : (rectangleSampledClosedDualGraph a w h A).Adj
        (k,lo+(m : ℤ)) (k,lo+((m+1 : ℕ) : ℤ)) := by
      have he := sampled_closed_horizontal_row_dual_adj a w h A k (lo+((m+1 : ℕ) : ℤ))
        (hc _ (by omega) le_rfl)
      convert he using 1; congr 1; omega
    exact hleft.trans hstep.reachable

/-- A literal consecutive sampled closed cut supplies its dual connector,
including both original outside half-cell endpoint labels. -/
theorem sampled_closed_rows_dual_reachable (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (k lo hi : ℤ) (hlohi : lo ≤ hi)
    (hc : ∀ y ∈ Finset.Icc lo hi,
      rectangleSampledBondClosed a w h A ⟨(k,y),.horizontal⟩) :
    (rectangleSampledClosedDualGraph a w h A).Reachable (k,lo-1) (k,hi) := by
  let m := (hi-lo).toNat
  have hm : lo+(m : ℤ) = hi := by dsimp [m]; rw [Int.toNat_of_nonneg (by omega)]; omega
  have he := sampled_closed_rows_nat a w h A k lo m
    (fun y hy0 hy1 => hc y (Finset.mem_Icc.mpr ⟨hy0,by omega⟩))
  rwa [hm] at he

/-- Full complementary-arc separation by two sampled dual arms plus the
literal closed cut, all in the SAME modified sampled configuration. -/
theorem rectangle_disconnected_of_sampled_closed_cut_and_dual_arms
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    (u v : RectangleVertex a w h) (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (k lo hi : ℤ) (hlohi : lo ≤ hi)
    (hc : ∀ y ∈ Finset.Icc lo hi,
      rectangleSampledBondClosed a w h A ⟨(k,y),.horizontal⟩)
    (s t : LatticeVertex)
    (hs : s ∈ rectangleLowerDualArc a w h u.val v.val)
    (ht : t ∈ rectangleUpperDualArc a w h u.val v.val)
    (minus : (rectangleSampledClosedDualGraph a w h A).Walk s (k,lo-1))
    (plus : (rectangleSampledClosedDualGraph a w h A).Walk (k,hi) t) :
    ¬ ActualConnected (rectangleGraph a w h) A u v := by
  obtain ⟨center⟩ := sampled_closed_rows_dual_reachable a w h A k lo hi hlohi hc
  exact rectangle_disconnected_of_sampled_dual_arms_and_connector a w h A u v hu hv
    s (k,lo-1) (k,hi) t hs ht minus center plus

end
end PottsContinuity.PlanarTopology
