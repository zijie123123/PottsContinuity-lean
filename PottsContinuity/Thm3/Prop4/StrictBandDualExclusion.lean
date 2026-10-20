module

public import PottsContinuity.PlanarTopology.RectangleCurveExclusion
public import PottsContinuity.PlanarTopology.AffineWalkBounds
public import PottsContinuity.PlanarTopology.AffinePathIntersection
public import PottsContinuity.PlanarTopology.RectangleSampledClosedDual
public import Mathlib.Tactic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial PD.FK.Curves PlanarTopology
noncomputable section

/-- A genuine sampled dual bridge whose clamped endpoints span a strict
reference band cannot coexist with an original open left-right band walk. -/
theorem strict_affine_band_excludes_sampled_dual_bridge
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    {u v : RectangleVertex a w h}
    (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (p : (openGraph (rectangleGraph a w h) A).Walk u v)
    (t b H : ℝ)
    (hp : ∀ z ∈ p.support, |(z.val.2 : ℝ)-(t*z.val.1+b)| < H)
    (s r : LatticeVertex) (hsr : s ≠ r)
    (q : (rectangleSampledClosedDualGraph a w h A).Walk s r)
    (hs : (rectangleClamp a w h (dualFaceCenter unitLatticeMesh s)).im-
      (t*(rectangleClamp a w h (dualFaceCenter unitLatticeMesh s)).re+b) ≤ -H)
    (hr : H ≤ (rectangleClamp a w h (dualFaceCenter unitLatticeMesh r)).im-
      (t*(rectangleClamp a w h (dualFaceCenter unitLatticeMesh r)).re+b)) : False := by
  have hm : s ∈ rectangleDualExpanded a w h ∧ r ∈ rectangleDualExpanded a w h := by
    constructor
    · cases q with
      | nil => exact (hsr rfl).elim
      | cons hadj _ => exact (rectangleSampledClosedDualGraph_adj_mem a w h A hadj).1
    · cases q.reverse with
      | nil => exact (hsr rfl).elim
      | cons hadj _ => exact (rectangleSampledClosedDualGraph_adj_mem a w h A hadj).1
  obtain ⟨q'⟩ := rectangleSampledClosedDualGraph_walk_finite a w h A q hm.1 hm.2
  have hpos : 0 < q'.length := by
    by_contra hn
    exact hsr (congrArg Subtype.val (SimpleGraph.Walk.eq_of_length_eq_zero (p := q') (by omega)))
  let P := p.map (rectangleOpenGraphToSquare a w h A)
  have hP : ∀ z ∈ P.support, (a.1 : ℝ) ≤ (z.1 : ℝ) ∧
      (z.1 : ℝ) ≤ (a.1 : ℝ)+w ∧ |(z.2 : ℝ)-(t*z.1+b)| < H := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    have hxR := (mem_latticeRectangle a x.val w h).mp x.property
    exact ⟨by exact_mod_cast hxR.1.1,by exact_mod_cast hxR.1.2,hp x hx⟩
  have hcross := affine_paths_intersect (latticeWalkPath unitLatticeMesh P)
    (clampedRectangleDualCurve a w h A q') (a.1 : ℝ) ((a.1 : ℝ)+w) t b H
    (by linarith [Nat.cast_nonneg (α := ℝ) w]) (latticeWalkPath_affine_band_bounds P _ _ _ _ _ hP)
    (fun θ => ⟨(clampedRectangleDualCurve_mem a w h A q' θ).1,
      (clampedRectangleDualCurve_mem a w h A q' θ).2.1⟩)
    (by simp only [latticeEmbed_re,unitLatticeMesh,one_mul]; change (u.val.1 : ℝ) = (a.1 : ℝ); exact_mod_cast hu)
    (by simp only [latticeEmbed_re,unitLatticeMesh,one_mul]; change (v.val.1 : ℝ) = (a.1 : ℝ)+w; exact_mod_cast hv) hs hr
  obtain ⟨θ,η,he⟩ := hcross
  exact Set.disjoint_left.mp (clamped_dualCurve_disjoint_of_trace_subset a w h A P
    (rectangle_open_walk_trace_subset a w h A p) q' hpos) ⟨θ,rfl⟩ ⟨η,he.symm⟩

end
end PottsContinuity.Thm3.Prop4
