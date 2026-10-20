module

public import PottsContinuity.PlanarTopology.KSTRectangleRealization
public import PottsContinuity.PlanarTopology.RectangleIntersection
public import PottsContinuity.PlanarTopology.SubpathExtraction
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Data.Int.Star

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Two open band crossings spanning an overlap interval are connected by an
open vertical crossing of that overlap. The resulting original walk stays in
the band, even if either horizontal walk wanders arbitrarily far sideways. -/
theorem kst_band_walks_glue (left right bottom top : ℤ)
    (hlr : left ≤ right) (hbt : bottom ≤ top) (ω : LatticeConfiguration)
    {u v x y a b : LatticeVertex}
    (p : PD.squareLattice.Walk u v) (q : PD.squareLattice.Walk x y)
    (V : PD.squareLattice.Walk a b)
    (hpO : kstPathOpen ω p) (hqO : kstPathOpen ω q) (hVO : kstPathOpen ω V)
    (hu : u.1 ≤ left) (hv : right ≤ v.1) (hx : x.1 ≤ left) (hy : right ≤ y.1)
    (hp : ∀ z ∈ p.support, bottom ≤ z.2 ∧ z.2 ≤ top)
    (hq : ∀ z ∈ q.support, bottom ≤ z.2 ∧ z.2 ≤ top)
    (hV : kstPathIn V left right bottom top) (ha : a.2 = bottom) (hb : b.2 = top) :
    ∃ W : PD.squareLattice.Walk u y, kstPathOpen ω W ∧
      ∀ z ∈ W.support, bottom ≤ z.2 ∧ z.2 ≤ top := by
  have hstep : ∀ x y, PD.squareLattice.Adj x y → |x.1-y.1| ≤ 1 := by
    intro x y h
    change |x.1-y.1|+|x.2-y.2| = 1 at h
    have := abs_nonneg (x.2-y.2)
    omega
  obtain ⟨pu,pv,P,hP,hPu,hPv,hPB⟩ := walk_subwalk_between_levels
    (fun z : LatticeVertex => z.1) hstep p hlr hu hv
  obtain ⟨qu,qv,Q,hQ,hQu,hQv,hQB⟩ := walk_subwalk_between_levels
    (fun z : LatticeVertex => z.1) hstep q hlr hx hy
  obtain ⟨z,hzP,hzV⟩ := rectangle_walks_common_vertex P V hlr hbt
    (fun z hz => ⟨(hPB z hz).1,(hPB z hz).2,hp z (hP.support_subset hz)⟩)
    hV hPu hPv ha hb
  obtain ⟨w,hwQ,hwV⟩ := rectangle_walks_common_vertex Q V hlr hbt
    (fun z hz => ⟨(hQB z hz).1,(hQB z hz).2,hq z (hQ.support_subset hz)⟩)
    hV hQu hQv ha hb
  let A := p.takeUntil z (hP.support_subset hzP)
  let B := V.takeUntil z hzV
  let C := V.takeUntil w hwV
  let D := q.dropUntil w (hQ.support_subset hwQ)
  have hA := p.isSubwalk_takeUntil (hP.support_subset hzP)
  have hB := V.isSubwalk_takeUntil hzV
  have hC := V.isSubwalk_takeUntil hwV
  have hD := q.isSubwalk_dropUntil (hQ.support_subset hwQ)
  refine ⟨A.append (B.reverse.append (C.append D)),?_,?_⟩
  · apply kstPathOpen_append A _ (kstPathOpen_of_subwalk hA hpO)
    apply kstPathOpen_append B.reverse _
      ((kstPathOpen_reverse_iff ω B).mpr (kstPathOpen_of_subwalk hB hVO))
    exact kstPathOpen_append C D (kstPathOpen_of_subwalk hC hVO)
      (kstPathOpen_of_subwalk hD hqO)
  · intro z hz
    simp only [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse,List.mem_reverse] at hz
    rcases hz with hz | hz | hz | hz
    · exact hp z (hA.support_subset hz)
    · exact (hV z (hB.support_subset hz)).2.2
    · exact (hV z (hC.support_subset hz)).2.2
    · exact hq z (hD.support_subset hz)

/-- A finite chain of overlapping open horizontal crossings, with vertical
crossings in consecutive overlaps, yields an original open band walk spanning
all stages. No lateral-confinement assumption is made on the accumulated walk. -/
theorem kst_band_horizontal_chain (stages : ℕ) (hstages : 1 ≤ stages)
    (base step bottom top : ℤ) (hstep : 0 ≤ step) (hbt : bottom ≤ top)
    (ω : LatticeConfiguration)
    (hH : ∀ i : ℕ, i < stages → ∃ u v, ∃ p : PD.squareLattice.Walk u v,
      kstPathOpen ω p ∧ u.1 = base+(i : ℤ)*step ∧ v.1 = base+((i : ℤ)+2)*step ∧
      ∀ z ∈ p.support, bottom ≤ z.2 ∧ z.2 ≤ top)
    (hV : ∀ i : ℕ, i+1 < stages → ∃ u v, ∃ p : PD.squareLattice.Walk u v,
      kstPathOpen ω p ∧ u.2 = bottom ∧ v.2 = top ∧
      kstPathIn p (base+((i : ℤ)+1)*step) (base+((i : ℤ)+2)*step) bottom top) :
    ∃ u v, ∃ p : PD.squareLattice.Walk u v,
      kstPathOpen ω p ∧ u.1 = base ∧ v.1 = base+((stages : ℤ)+1)*step ∧
      ∀ z ∈ p.support, bottom ≤ z.2 ∧ z.2 ≤ top := by
  induction stages with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst k
      obtain ⟨u,v,p,hp,hu,hv,hband⟩ := hH 0 (by omega)
      refine ⟨u,v,p,hp,?_,?_,hband⟩
      · simpa using hu
      · simpa using hv
    · obtain ⟨u,v,p,hp,hu,hv,hband⟩ := ih (by omega)
        (fun i hi => hH i (by omega)) (fun i hi => hV i (by omega))
      obtain ⟨x,y,q,hq,hx,hy,hbandq⟩ := hH k (by omega)
      obtain ⟨a,b,V,hVO,ha,hb,hVB⟩ := hV (k-1) (by omega)
      have hkcast : ((k-1 : ℕ) : ℤ) = (k : ℤ)-1 := by omega
      have hVB' : kstPathIn V (base+(k : ℤ)*step) (base+((k : ℤ)+1)*step) bottom top := by
        intro z hz
        have hh := hVB z hz
        rw [hkcast] at hh
        exact ⟨by nlinarith [hh.1],by nlinarith [hh.2.1],hh.2.2⟩
      obtain ⟨W,hWO,hWB⟩ := kst_band_walks_glue
        (base+(k : ℤ)*step) (base+((k : ℤ)+1)*step) bottom top
        (by nlinarith) hbt ω p q V hp hq hVO
        (by rw [hu]; nlinarith [mul_nonneg (Int.natCast_nonneg k) hstep])
        (by rw [hv]) (by rw [hx]) (by rw [hy]; nlinarith)
        hband hbandq hVB' ha hb
      refine ⟨u,y,W,hWO,hu,?_,hWB⟩
      push_cast
      nlinarith [hy]

end
end PottsContinuity.PlanarTopology
