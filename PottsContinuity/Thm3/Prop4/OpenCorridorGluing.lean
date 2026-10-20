module

public import PottsContinuity.PlanarTopology.RectangleIntersection
public import PottsContinuity.PlanarTopology.SubpathExtraction
public import PottsContinuity.PlanarTopology.OpenWalkEmbedding
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-!
# Original open walks glued inside an arbitrary corridor

The planar intersection step comes from `PlanarTopology`. Prefixes of the three actual
open walks give the connector, preserving any common support restriction.
The construction follows `PlanarTopology.BandCrossingGluing` while retaining that
restriction instead of only a containing horizontal band.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

/-- A band walk spanning the overlap meets its actual vertical connector. -/
theorem original_open_walk_meets_vertical_rectangle (ω : LatticeConfiguration)
    (left right bottom top : ℤ) (hlr : left ≤ right) (hbt : bottom ≤ top)
    {u v a b : LatticeVertex} (p : (PD.rcInfiniteOpenGraph ω).Walk u v)
    (q : (PD.rcInfiniteOpenGraph ω).Walk a b)
    (hu : u.1 ≤ left) (hv : right ≤ v.1)
    (hp : ∀ z ∈ p.support, bottom ≤ z.2 ∧ z.2 ≤ top)
    (hq : ∀ z ∈ q.support, left ≤ z.1 ∧ z.1 ≤ right ∧ bottom ≤ z.2 ∧ z.2 ≤ top)
    (ha : a.2 = bottom) (hb : b.2 = top) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  have hle := PlanarTopology.rcOpenGraph_le_squareLattice ω
  have hstep : ∀ x y, (PD.rcInfiniteOpenGraph ω).Adj x y → |x.1-y.1| ≤ 1 := by
    intro x y hxy
    have h := hle hxy
    change |x.1-y.1|+|x.2-y.2|=1 at h
    have := abs_nonneg (x.2-y.2)
    omega
  obtain ⟨x,y,P,hP,hx,hy,hPB⟩ :=
    PlanarTopology.walk_subwalk_between_levels (fun z : LatticeVertex => z.1) hstep p hlr hu hv
  obtain ⟨z,hzP,hzQ⟩ := PlanarTopology.rectangle_walks_common_vertex (P.mapLe hle) (q.mapLe hle)
    hlr hbt (by
      intro z hz
      have hz' : z ∈ P.support := by simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hz
      exact ⟨(hPB z hz').1,(hPB z hz').2,hp z (hP.support_subset hz')⟩)
    (by simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hq) hx hy ha hb
  refine ⟨z,hP.support_subset ?_,?_⟩
  · simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hzP
  · simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hzQ

/-- Adjacent crossings join at their initial vertices inside their original common corridor. -/
theorem original_open_corridor_connector (ω : LatticeConfiguration) (D : Set LatticeVertex)
    (left right bottom top : ℤ) (hlr : left ≤ right) (hbt : bottom ≤ top)
    {u v x y a b : LatticeVertex}
    (p : (PD.rcInfiniteOpenGraph ω).Walk u v) (q : (PD.rcInfiniteOpenGraph ω).Walk x y)
    (V : (PD.rcInfiniteOpenGraph ω).Walk a b)
    (hu : u.1 ≤ left) (hv : right ≤ v.1) (hx : x.1 ≤ left) (hy : right ≤ y.1)
    (hp : ∀ z ∈ p.support, bottom ≤ z.2 ∧ z.2 ≤ top)
    (hq : ∀ z ∈ q.support, bottom ≤ z.2 ∧ z.2 ≤ top)
    (hV : ∀ z ∈ V.support, left ≤ z.1 ∧ z.1 ≤ right ∧ bottom ≤ z.2 ∧ z.2 ≤ top)
    (ha : a.2 = bottom) (hb : b.2 = top)
    (hpD : ∀ z ∈ p.support, z ∈ D) (hqD : ∀ z ∈ q.support, z ∈ D)
    (hVD : ∀ z ∈ V.support, z ∈ D) :
    ∃ R : (PD.rcInfiniteOpenGraph ω).Walk u x, ∀ z ∈ R.support, z ∈ D := by
  classical
  obtain ⟨z,hzp,hzV⟩ := original_open_walk_meets_vertical_rectangle ω
    left right bottom top hlr hbt p V hu hv hp hV ha hb
  obtain ⟨w,hwq,hwV⟩ := original_open_walk_meets_vertical_rectangle ω
    left right bottom top hlr hbt q V hx hy hq hV ha hb
  let A := p.takeUntil z hzp
  let B := V.takeUntil z hzV
  let C := V.takeUntil w hwV
  let E := q.takeUntil w hwq
  refine ⟨A.append (B.reverse.append (C.append E.reverse)),?_⟩
  intro t ht
  simp only [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_reverse,List.mem_reverse] at ht
  rcases ht with ht | ht | ht | ht
  · exact hpD t ((p.isSubwalk_takeUntil hzp).support_subset ht)
  · exact hVD t ((V.isSubwalk_takeUntil hzV).support_subset ht)
  · exact hVD t ((V.isSubwalk_takeUntil hwV).support_subset ht)
  · exact hqD t ((q.isSubwalk_takeUntil hwq).support_subset ht)

end
end PottsContinuity.Thm3.Prop4
