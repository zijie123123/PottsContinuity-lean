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

/-- The 512 odd-width target gaps cover the complete long interval without
rounding gaps in the contracted dual box. The right endpoint is strict, as required for span saturation. -/
theorem alpha_core_bottom_grid_covers (a : ℕ) (ha : 1 ≤ a) (x : ℤ)
    (hx : -512*(a : ℤ)-1 ≤ x ∧ x < 512*(a : ℤ)) :
    ∃ i : Fin 512, (-512*(a : ℤ)-1+(i.val : ℤ)*(2*(a : ℤ)+1)) ≤ x ∧
      x < (-510*(a : ℤ)+(i.val : ℤ)*(2*(a : ℤ)+1)) := by
  have hd : 0 < 2*(a : ℤ)+1 := by omega
  let j := (x+512*(a : ℤ)+1)/(2*(a : ℤ)+1)
  have hj0 : 0 ≤ j := Int.ediv_nonneg (by omega) hd.le
  have hj512 : j < 512 := (Int.ediv_lt_iff_lt_mul hd).mpr (by nlinarith [hx.2])
  let i : Fin 512 := ⟨j.toNat,by omega⟩
  have hi : (i.val : ℤ) = j := by dsimp [i]; omega
  have hlo := Int.ediv_mul_le (x+512*(a : ℤ)+1) (ne_of_gt hd)
  have hhi := Int.lt_ediv_add_one_mul_self (x+512*(a : ℤ)+1) hd
  refine ⟨i,?_,?_⟩ <;> rw [hi] <;> dsimp [j] at * <;> nlinarith

/-- The deterministic bottom-arc gluing in KST Section 3. Each supplied
connection straddles its own gap, but different connections may be nested or
have repeated vertices. A maximal bottom span through zero handles both cases. -/
theorem alpha_core_512_bottom_connections_glue (a : ℕ) (ha : 1 ≤ a)
    (ω : LatticeConfiguration)
    (hF : ∀ i : Fin 512, ∃ u v, ∃ p : PD.squareLattice.Walk u v,
      kstPathOpen ω p ∧ u.2 = -64*(a : ℤ) ∧ v.2 = -64*(a : ℤ) ∧
      u.1 ≤ (-512*(a : ℤ)-1+(i.val : ℤ)*(2*(a : ℤ)+1)) ∧
      (-510*(a : ℤ)+(i.val : ℤ)*(2*(a : ℤ)+1)) ≤ v.1 ∧
      kstPathIn p (-576*(a : ℤ)) (576*(a : ℤ)+511) (-64*(a : ℤ)) (64*(a : ℤ)-1)) :
    ω ∈ horizontalRectangle (-512*(a : ℤ)-1,-64*(a : ℤ)) (1024*a+1) (128*a-1) := by
  obtain ⟨j,hjl,hjr⟩ := alpha_core_bottom_grid_covers a ha 0 (by omega)
  obtain ⟨x,y,q,hq,hx,hy,hxl,hyr,hqB⟩ := hF j
  have hxc : x.1 ≤ 0 := hxl.trans hjl
  have hcy : 0 ≤ y.1 := by omega
  have hwidth : -576*(a : ℤ)+(1152*a+511 : ℕ) = 576*(a : ℤ)+511 := by omega
  have hheight : -64*(a : ℤ)+(128*a-1 : ℕ) = 64*(a : ℤ)-1 := by omega
  have hqB' : kstPathIn q (-576*(a : ℤ))
      (-576*(a : ℤ)+(1152*a+511 : ℕ)) (-64*(a : ℤ)) (-64*(a : ℤ)+(128*a-1 : ℕ)) := by
    rwa [hwidth,hheight]
  obtain ⟨u,v,p,hp,hpB,hu,hv,huc,hcv,hmax⟩ := exists_kst_maximal_bottom_span_through
    (-576*(a : ℤ),-64*(a : ℤ)) (1152*a+511) (128*a-1) 0 ω q hq hqB' hx hy hxc hcy
  simp only [hwidth,hheight] at hpB hmax
  have hright : 512*(a : ℤ) ≤ v.1 := by
    by_contra hvsmall
    obtain ⟨i,hil,hir⟩ := alpha_core_bottom_grid_covers a ha v.1 (by omega)
    obtain ⟨s,t,Q,hQ,hs,ht,hsl,htr,hQB⟩ := hF i
    exact kst_maximal_bottom_span_through_no_right_straddle
      _ _ _ _ 0 ω p Q hp hQ hpB hQB hu hv hs ht huc hcv hmax
      (hsl.trans hil) (hir.trans_le htr)
  have hleft : u.1 ≤ -512*(a : ℤ)-1 := by
    by_contra hularge
    obtain ⟨i,hil,hir⟩ := alpha_core_bottom_grid_covers a ha (u.1-1) (by omega)
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
    (fun z : LatticeVertex => z.1) hstep p (a := -512*(a : ℤ)-1) (b := 512*(a : ℤ)) (by omega) hleft hright
  apply horizontalRectangle_of_kst_open_walk _ _ _ ω Q
    (kstPathOpen_of_subwalk hQ hp) hs
  · change t.1 = -512*(a : ℤ)-1+(1024*a+1 : ℕ)
    push_cast
    nlinarith [ht]
  · intro z hz
    have hb := hpB z (hQ.support_subset hz)
    have hh := hQB z hz
    change -512*(a : ℤ)-1 ≤ z.1 ∧ z.1 ≤ -512*(a : ℤ)-1+(1024*a+1 : ℕ) ∧
      -64*(a : ℤ) ≤ z.2 ∧ z.2 ≤ -64*(a : ℤ)+(128*a-1 : ℕ)
    push_cast
    exact ⟨hh.1,by nlinarith [hh.2],hb.2.2.1,by nlinarith [hb.2.2.2]⟩

end
end PottsContinuity.PlanarTopology
