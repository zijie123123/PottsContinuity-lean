module

public import PottsContinuity.PlanarTopology.RectangleBoundaryArcIntersection
public import PottsContinuity.PlanarTopology.RectangleDualBoundaryArcs
public import PottsContinuity.PlanarTopology.RectangleCurveExclusion
public import Mathlib.Tactic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.FK.Curves
noncomputable section

/-- A closed dual walk joining the two complementary exterior boundary arcs
of an actual sampled rectangle separates its left and right primal marks.
Every dual edge crosses an original sampled bond; no outside cap is used. -/
theorem rectangle_boundary_arc_dual_excludes_primal (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (u v : RectangleVertex a w h)
    (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (s t : RectangleDualVertex a w h)
    (hs : s.val ∈ rectangleLowerDualArc a w h u.val v.val)
    (ht : t.val ∈ rectangleUpperDualArc a w h u.val v.val)
    (q : (openGraph (rectangleDualGraph a w h) (rectangleDualConfiguration a w h A)).Walk s t) :
    ¬ ActualConnected (rectangleGraph a w h) A u v := by
  rintro ⟨p⟩
  let P := p.map (rectangleOpenGraphToSquare a w h A)
  let Q := clampedRectangleDualCurve a w h A q
  have hpos : 0 < q.length := by
    by_contra hn
    have he : s = t := SimpleGraph.Walk.eq_of_length_eq_zero (p := q) (by omega)
    have he' : s.val = t.val := congrArg Subtype.val he
    exact Set.disjoint_left.mp (rectangle_lower_upper_dual_arcs_disjoint a w h u.val v.val)
      hs (he'.symm ▸ ht)
  have hdis := latticePairCurve_disjoint P Q
    (clamped_dualCurve_disjoint_of_trace_subset a w h A P
      (rectangle_open_walk_trace_subset a w h A p) q hpos)
  have hP : ∀ z ∈ Set.range (latticePairCurve P),
      (a.1 : ℝ) ≤ z.1 ∧ z.1 ≤ (a.1 : ℝ)+w ∧
      (a.2 : ℝ) ≤ z.2 ∧ z.2 ≤ (a.2 : ℝ)+h := by
    apply latticePairCurve_bounds
    intro z hz
    obtain ⟨x,_,hxe⟩ := rectangleOpenWalk_mapped_support_preimage a w h A p hz
    have hx := (mem_latticeRectangle a x.val w h).mp x.property
    rw [← hxe]
    exact ⟨by exact_mod_cast hx.1.1,by exact_mod_cast hx.1.2,
      by exact_mod_cast hx.2.1,by exact_mod_cast hx.2.2⟩
  have hQ : ∀ z ∈ Set.range (Q.map continuous_complexCoordinates),
      (a.1 : ℝ) ≤ z.1 ∧ z.1 ≤ (a.1 : ℝ)+w ∧
      (a.2 : ℝ) ≤ z.2 ∧ z.2 ≤ (a.2 : ℝ)+h := by
    rintro z ⟨θ,rfl⟩
    exact clampedRectangleDualCurve_mem a w h A q θ
  have hlu := rectangle_lower_dual_arc_clamped a w h u.val v.val s.val hs
  have hut := rectangle_upper_dual_arc_clamped a w h u.val v.val t.val ht
  obtain ⟨z,hzP,hzQ⟩ := rectangle_boundary_arc_paths_intersect
    (a.1 : ℝ) ((a.1 : ℝ)+w) (a.2 : ℝ) ((a.2 : ℝ)+h)
    (latticePairCurve P) (Q.map continuous_complexCoordinates)
    (by have := Nat.cast_nonneg (α := ℝ) w; linarith) hP hQ
    (by change (u.val.1 : ℝ) = (a.1 : ℝ); exact_mod_cast hu)
    (by change (v.val.1 : ℝ) = (a.1 : ℝ)+w; exact_mod_cast hv) hlu hut
  exact Set.disjoint_left.mp hdis hzP hzQ

end
end PottsContinuity.PlanarTopology
