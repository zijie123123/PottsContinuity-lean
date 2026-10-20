module

public import PottsContinuity.PlanarTopology.BottomSpan
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Maximize among bottom connections whose horizontal interval contains a
specified coordinate. The input is an actual open connection, not an existence
assumption for a separating path. -/
theorem exists_kst_maximal_bottom_span_through (a : LatticeVertex) (w h : ℕ)
    (c : ℤ) (ω : LatticeConfiguration) {x y : LatticeVertex}
    (q : PD.squareLattice.Walk x y) (hq : kstPathOpen ω q)
    (hqB : kstPathIn q a.1 (a.1+(w : ℤ)) a.2 (a.2+(h : ℤ)))
    (hx : x.2 = a.2) (hy : y.2 = a.2) (hxc : x.1 ≤ c) (hcy : c ≤ y.1) :
    ∃ u v, ∃ p : PD.squareLattice.Walk u v,
      kstPathOpen ω p ∧ kstPathIn p a.1 (a.1+(w : ℤ)) a.2 (a.2+(h : ℤ)) ∧
      u.2 = a.2 ∧ v.2 = a.2 ∧ u.1 ≤ c ∧ c ≤ v.1 ∧
      ∀ {x y : LatticeVertex} (q : PD.squareLattice.Walk x y),
        kstPathOpen ω q → kstPathIn q a.1 (a.1+(w : ℤ)) a.2 (a.2+(h : ℤ)) →
        x.2 = a.2 → y.2 = a.2 → x.1 ≤ c → c ≤ y.1 → y.1-x.1 ≤ v.1-u.1 := by
  classical
  let S := latticeRectangle a w h
  let T := (S.product S).filter (fun xy => xy.1.2 = a.2 ∧ xy.2.2 = a.2 ∧
    xy.1.1 ≤ c ∧ c ≤ xy.2.1 ∧ ∃ p : PD.squareLattice.Walk xy.1 xy.2,
      kstPathOpen ω p ∧ kstPathIn p a.1 (a.1+(w : ℤ)) a.2 (a.2+(h : ℤ)))
  have memS {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
      (hB : kstPathIn p a.1 (a.1+(w : ℤ)) a.2 (a.2+(h : ℤ))) : u ∈ S ∧ v ∈ S := by
    have hu := hB u p.start_mem_support
    have hv := hB v p.end_mem_support
    exact ⟨(mem_latticeRectangle a u w h).mpr ⟨⟨hu.1,hu.2.1⟩,hu.2.2⟩,
      (mem_latticeRectangle a v w h).mpr ⟨⟨hv.1,hv.2.1⟩,hv.2.2⟩⟩
  have hseed : (x,y) ∈ T := Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr (memS q hqB),hx,hy,hxc,hcy,q,hq,hqB⟩
  obtain ⟨uv,huv,hmax⟩ := Finset.exists_max_image T (fun xy => xy.2.1-xy.1.1) ⟨_,hseed⟩
  obtain ⟨huy,hvy,huc,hcv,p,hp,hbox⟩ := (Finset.mem_filter.mp huv).2
  refine ⟨uv.1,uv.2,p,hp,hbox,huy,hvy,huc,hcv,?_⟩
  intro x y q hq hqB hx hy hxc hcy
  exact hmax (x,y) (Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr (memS q hqB),hx,hy,hxc,hcy,q,hq,hqB⟩)

/-- No confined open bottom connection straddles the right endpoint of a
maximal span through c. A containing connection also contains c. -/
theorem kst_maximal_bottom_span_through_no_right_straddle
    (left right bottom top c : ℤ) (ω : LatticeConfiguration)
    {u v x y : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (q : PD.squareLattice.Walk x y)
    (hp : kstPathOpen ω p) (hq : kstPathOpen ω q)
    (hpB : kstPathIn p left right bottom top) (hqB : kstPathIn q left right bottom top)
    (hu : u.2 = bottom) (hv : v.2 = bottom) (hx : x.2 = bottom) (hy : y.2 = bottom)
    (huc : u.1 ≤ c) (hcv : c ≤ v.1)
    (hmax : ∀ {a b : LatticeVertex} (W : PD.squareLattice.Walk a b),
      kstPathOpen ω W → kstPathIn W left right bottom top →
      a.2 = bottom → b.2 = bottom → a.1 ≤ c → c ≤ b.1 → b.1-a.1 ≤ v.1-u.1)
    (hxv : x.1 ≤ v.1) (hvy : v.1 < y.1) : False := by
  by_cases hux : u.1 ≤ x.1
  · obtain ⟨z,hzp,hzq⟩ := band_interlaced_walks_intersect bottom p q hu hv hx hy
      hux hxv hvy.le (fun z hz => (hpB z hz).2.2.1) (fun z hz => (hqB z hz).2.2.1)
    let P := p.takeUntil z hzp
    let Q := q.dropUntil z hzq
    have hP := p.isSubwalk_takeUntil hzp
    have hQ := q.isSubwalk_dropUntil hzq
    have hW := kstPathOpen_append P Q (kstPathOpen_of_subwalk hP hp)
      (kstPathOpen_of_subwalk hQ hq)
    have hWB : kstPathIn (P.append Q) left right bottom top := by
      intro z hz
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · exact hpB z (hP.support_subset hz)
      · exact hqB z (hQ.support_subset hz)
    have := hmax (P.append Q) hW hWB hu hy huc (by omega)
    omega
  · have := hmax q hq hqB hx hy (by omega) (by omega)
    omega

/-- The symmetric left-endpoint saturation uses the same actual walks, with
chronology reversed. -/
theorem kst_maximal_bottom_span_through_no_left_straddle
    (left right bottom top c : ℤ) (ω : LatticeConfiguration)
    {u v x y : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (q : PD.squareLattice.Walk x y)
    (hp : kstPathOpen ω p) (hq : kstPathOpen ω q)
    (hpB : kstPathIn p left right bottom top) (hqB : kstPathIn q left right bottom top)
    (hu : u.2 = bottom) (hv : v.2 = bottom) (hx : x.2 = bottom) (hy : y.2 = bottom)
    (huc : u.1 ≤ c) (hcv : c ≤ v.1)
    (hmax : ∀ {a b : LatticeVertex} (W : PD.squareLattice.Walk a b),
      kstPathOpen ω W → kstPathIn W left right bottom top →
      a.2 = bottom → b.2 = bottom → a.1 ≤ c → c ≤ b.1 → b.1-a.1 ≤ v.1-u.1)
    (hxu : x.1 < u.1) (huy : u.1 ≤ y.1) : False := by
  by_cases hyv : y.1 ≤ v.1
  · obtain ⟨z,hzq,hzp⟩ := band_interlaced_walks_intersect bottom q p hx hy hu hv
      hxu.le huy hyv (fun z hz => (hqB z hz).2.2.1) (fun z hz => (hpB z hz).2.2.1)
    let Q := q.takeUntil z hzq
    let P := p.dropUntil z hzp
    have hQ := q.isSubwalk_takeUntil hzq
    have hP := p.isSubwalk_dropUntil hzp
    have hW := kstPathOpen_append Q P (kstPathOpen_of_subwalk hQ hq)
      (kstPathOpen_of_subwalk hP hp)
    have hWB : kstPathIn (Q.append P) left right bottom top := by
      intro z hz
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · exact hqB z (hQ.support_subset hz)
      · exact hpB z (hP.support_subset hz)
    have := hmax (Q.append P) hW hWB hx hv (by omega) hcv
    omega
  · have := hmax q hq hqB hx hy (by omega) (by omega)
    omega

end
end PottsContinuity.PlanarTopology
