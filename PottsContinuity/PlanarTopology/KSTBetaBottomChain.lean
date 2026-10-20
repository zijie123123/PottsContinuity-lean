module

public import PottsContinuity.PlanarTopology.BottomSpanThrough
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks
public import Mathlib.Data.Int.Star

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- The 96 consecutive target gaps cover the complete long interval without
rounding gaps. The right endpoint is strict, as required for span saturation. -/
theorem kst_beta_bottom_grid_covers (a : ℕ) (ha : 1 ≤ a) (x : ℤ)
    (hx : -96*(a : ℤ) ≤ x ∧ x < 96*(a : ℤ)) :
    ∃ i : Fin 96, (2*(i.val : ℤ)-96)*(a : ℤ) ≤ x ∧
      x < (2*(i.val : ℤ)-94)*(a : ℤ) := by
  have hd : 0 < 2*(a : ℤ) := by omega
  let j := (x+96*(a : ℤ))/(2*(a : ℤ))
  have hj0 : 0 ≤ j := Int.ediv_nonneg (by omega) hd.le
  have hj512 : j < 96 := (Int.ediv_lt_iff_lt_mul hd).mpr (by nlinarith [hx.2])
  let i : Fin 96 := ⟨j.toNat,by omega⟩
  have hi : (i.val : ℤ) = j := by dsimp [i]; omega
  have hlo := Int.ediv_mul_le (x+96*(a : ℤ)) (ne_of_gt hd)
  have hhi := Int.lt_ediv_add_one_mul_self (x+96*(a : ℤ)) hd
  refine ⟨i,?_,?_⟩ <;> rw [hi] <;> dsimp [j] at * <;> nlinarith

/-- The deterministic beta beta-target version of the bottom-arc gluing in KST Section 3. Each supplied
connection straddles its own gap, but different connections may be nested or
have repeated vertices. A maximal bottom span through zero handles both cases. -/
theorem kst_96_beta_bottom_connections_glue (a : ℕ) (ha : 1 ≤ a)
    (ω : LatticeConfiguration)
    (hF : ∀ i : Fin 96, ∃ u v, ∃ p : PD.squareLattice.Walk u v,
      kstPathOpen ω p ∧ u.2 = -12*(a : ℤ) ∧ v.2 = -12*(a : ℤ) ∧
      u.1 ≤ (2*(i.val : ℤ)-96)*(a : ℤ) ∧
      (2*(i.val : ℤ)-94)*(a : ℤ) ≤ v.1 ∧
      kstPathIn p (-108*(a : ℤ)) (108*(a : ℤ)) (-12*(a : ℤ)) (12*(a : ℤ))) :
    ω ∈ horizontalRectangle (-96*(a : ℤ),-12*(a : ℤ)) (192*a) (24*a) := by
  obtain ⟨x,y,q,hq,hx,hy,hxl,hyr,hqB⟩ := hF ⟨48,by decide⟩
  have hxc : x.1 ≤ 0 := by norm_num at hxl; omega
  have hcy : 0 ≤ y.1 := by norm_num at hyr; omega
  have hwidth : -108*(a : ℤ)+(216*a : ℕ) = 108*(a : ℤ) := by push_cast; ring
  have hheight : -12*(a : ℤ)+(24*a : ℕ) = 12*(a : ℤ) := by push_cast; ring
  have hqB' : kstPathIn q (-108*(a : ℤ))
      (-108*(a : ℤ)+(216*a : ℕ)) (-12*(a : ℤ)) (-12*(a : ℤ)+(24*a : ℕ)) := by
    rwa [hwidth,hheight]
  obtain ⟨u,v,p,hp,hpB,hu,hv,huc,hcv,hmax⟩ := exists_kst_maximal_bottom_span_through
    (-108*(a : ℤ),-12*(a : ℤ)) (216*a) (24*a) 0 ω q hq hqB' hx hy hxc hcy
  simp only [hwidth,hheight] at hpB hmax
  have hright : 96*(a : ℤ) ≤ v.1 := by
    by_contra hvsmall
    obtain ⟨i,hil,hir⟩ := kst_beta_bottom_grid_covers a ha v.1 (by omega)
    obtain ⟨s,t,Q,hQ,hs,ht,hsl,htr,hQB⟩ := hF i
    exact kst_maximal_bottom_span_through_no_right_straddle
      _ _ _ _ 0 ω p Q hp hQ hpB hQB hu hv hs ht huc hcv hmax
      (hsl.trans hil) (hir.trans_le htr)
  have hleft : u.1 ≤ -96*(a : ℤ) := by
    by_contra hularge
    obtain ⟨i,hil,hir⟩ := kst_beta_bottom_grid_covers a ha (u.1-1) (by omega)
    obtain ⟨s,t,Q,hQ,hs,ht,hsl,htr,hQB⟩ := hF i
    exact kst_maximal_bottom_span_through_no_left_straddle
      _ _ _ _ 0 ω p Q hp hQ hpB hQB hu hv hs ht huc hcv hmax
      (by omega) (by omega)
  have hstep : ∀ x y, PD.squareLattice.Adj x y → |x.1-y.1| ≤ 1 := by
    intro x y h
    change |x.1-y.1|+|x.2-y.2| = 1 at h
    have := abs_nonneg (x.2-y.2)
    omega
  obtain ⟨s,t,Q,hQ,hs,ht,hQB⟩ := walk_subwalk_between_levels
    (fun z : LatticeVertex => z.1) hstep p (by omega) hleft hright
  apply horizontalRectangle_of_kst_open_walk _ _ _ ω Q
    (kstPathOpen_of_subwalk hQ hp) hs
  · change t.1 = -96*(a : ℤ)+(192*a : ℕ)
    push_cast
    nlinarith [ht]
  · intro z hz
    have hb := hpB z (hQ.support_subset hz)
    have hh := hQB z hz
    change -96*(a : ℤ) ≤ z.1 ∧ z.1 ≤ -96*(a : ℤ)+(192*a : ℕ) ∧
      -12*(a : ℤ) ≤ z.2 ∧ z.2 ≤ -12*(a : ℤ)+(24*a : ℕ)
    push_cast
    exact ⟨hh.1,by nlinarith [hh.2],hb.2.2.1,by nlinarith [hb.2.2.2]⟩

end
end PottsContinuity.PlanarTopology
