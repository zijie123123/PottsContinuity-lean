module

public import PottsContinuity.Thm3.Prop4.TraceEndpointConnector
public import PottsContinuity.Thm3.Prop4.PositiveLowerFaceAccess
public import PottsContinuity.PlanarTopology.RectangleBoundaryArcIntersection
public import PottsContinuity.PlanarTopology.SampledDualScreenSeparation
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.CompletePartialOrder

/-! # Lower dual access prevents top access avoiding the primal crossing -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial PD.FK.Curves PlanarTopology
noncomputable section

/-- A primal endpoint incident to the lower closed-dual region cannot reach
the top inside the rectangle while avoiding an actual open prescribed
crossing. The access through the queried bond uses its actual midpoint and
half primal edge; no lattice-width corridor assumption is made. -/
theorem lower_dual_reached_endpoint_no_top_avoiding_walk
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    (u v : RectangleVertex a w h) (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (p : PD.squareLattice.Walk u.val v.val)
    (hPB : ∀ z ∈ p.support, z ∈ latticeRectangle a w h)
    (htrace : rectangleTraceConfiguration a w h p ⊆ A)
    (e : RectangleDualEdgeCarrier a w h) (x : RectangleVertex a w h)
    (hxB : x.val = (rectanglePrimalEdgeBond a w h e.primalEdge).source ∨
      x.val = (rectanglePrimalEdgeBond a w h e.primalEdge).target)
    (hreach : (∃ s ∈ rectangleLowerDualArc a w h u.val v.val,
        (rectangleSampledClosedDualGraph a w h A).Reachable s e.crossingBond.source) ∨
      (∃ s ∈ rectangleLowerDualArc a w h u.val v.val,
        (rectangleSampledClosedDualGraph a w h A).Reachable s e.crossingBond.target))
    (t : LatticeVertex) (Q : PD.squareLattice.Walk x.val t)
    (hQB : ∀ z ∈ Q.support, z ∈ latticeRectangle a w h)
    (ht : t.2 = a.2+(h : ℤ)) (havoid : ∀ z ∈ Q.support, z ∉ p.support) : False := by
  classical
  have hInterval : IsPathConnected (Set.Icc (0 : ℝ) 1) :=
    (convex_Icc _ _).isPathConnected ⟨0,by norm_num⟩
  let lowerEndpointIntervalPathConnected : PathConnectedSpace unitInterval :=
    isPathConnected_iff_pathConnectedSpace.mp hInterval
  have hxP := havoid x.val Q.start_mem_support
  obtain ⟨K,hK,hKs,hKt,hKx,hKbounds,hKdis⟩ := sampled_bond_endpoint_connector a w h p e x.val hxB hxP
  have heP : e.primalEdge ∉ rectangleTraceConfiguration a w h p := by
    intro he
    have hedge := (mem_rectangleTraceConfiguration a w h p e.primalEdge).mp he
    have hbond := rectanglePrimalEdgeBond_toSym2_public a w h e.primalEdge
    rw [← hbond] at hedge
    rcases hxB with hxs | hxt
    · exact hxP (hxs.symm ▸ p.fst_mem_support_of_mem_edges hedge)
    · exact hxP (hxt.symm ▸ p.snd_mem_support_of_mem_edges hedge)
  obtain ⟨s,hs,f,hf,r,hr⟩ := positive_trace_complement_access_of_incident_reached_face
    a w h A p htrace (rectangleLowerDualArc a w h u.val v.val)
    (fun z hz => rectangle_dual_arc_mem_expanded a w h u.val v.val z (Or.inl hz)) e heP hreach
  let D := clampedRectangleDualCurve a w h (rectangleTraceConfiguration a w h p) r
  have hDdis : Disjoint (Set.range (latticeWalkPath unitLatticeMesh p)) (Set.range D) :=
    clamped_trace_dualCurve_disjoint a w h p r hr
  have hfK : rectangleClamp a w h (dualFaceCenter unitLatticeMesh f.val) ∈ K := by
    rcases hf with hf | hf
    · rw [hf]; exact hKs
    · rw [hf]; exact hKt
  let W := (Set.range D ∪ K) ∪ Set.range (latticeWalkPath unitLatticeMesh Q)
  have hDK : IsPathConnected (Set.range D ∪ K) :=
    (isPathConnected_range D.continuous).union hK ⟨_,D.target_mem_range,hfK⟩
  have hW : IsPathConnected W :=
    hDK.union (isPathConnected_range (latticeWalkPath unitLatticeMesh Q).continuous)
      ⟨_,Or.inr hKx,(latticeWalkPath unitLatticeMesh Q).source_mem_range⟩
  have hQdis : Disjoint (Set.range (latticeWalkPath unitLatticeMesh p))
      (Set.range (latticeWalkPath unitLatticeMesh Q)) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨i,hi⟩ ⟨j,hj⟩
    obtain ⟨z,hzP,hzQ⟩ := latticeWalkPaths_intersection_common_support unitLatticeMesh p Q (hi.trans hj.symm)
    exact havoid z hzQ hzP
  have hWdis : Disjoint (Set.range (latticeWalkPath unitLatticeMesh p)) W :=
    (hDdis.union_right hKdis).union_right hQdis
  have vertexBounds {c d : LatticeVertex} (T : PD.squareLattice.Walk c d)
      (hT : ∀ z ∈ T.support, z ∈ latticeRectangle a w h) :
      ∀ z ∈ T.support, (a.1 : ℝ) ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ (a.1 : ℝ)+w ∧
        (a.2 : ℝ) ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ (a.2 : ℝ)+h := by
    intro z hz
    have hh := (mem_latticeRectangle a z w h).mp (hT z hz)
    exact ⟨by exact_mod_cast hh.1.1,by exact_mod_cast hh.1.2,
      by exact_mod_cast hh.2.1,by exact_mod_cast hh.2.2⟩
  have hWbounds : ∀ z ∈ W, (a.1 : ℝ) ≤ z.re ∧ z.re ≤ (a.1 : ℝ)+w ∧
      (a.2 : ℝ) ≤ z.im ∧ z.im ≤ (a.2 : ℝ)+h := by
    intro z hz
    rcases hz with (⟨i,rfl⟩ | hz) | ⟨i,rfl⟩
    · exact clampedRectangleDualCurve_mem a w h _ r i
    · exact hKbounds z hz
    · exact latticeWalkPath_coordinate_bounds Q (vertexBounds Q hQB) i
  obtain ⟨C,hC⟩ := hW.joinedIn
    (rectangleClamp a w h (dualFaceCenter unitLatticeMesh s.val))
    (Or.inl (Or.inl D.source_mem_range))
    (latticeEmbed unitLatticeMesh t) (Or.inr (latticeWalkPath unitLatticeMesh Q).target_mem_range)
  have hCdis : Disjoint (Set.range (latticeWalkPath unitLatticeMesh p)) (Set.range C) :=
    hWdis.mono_right (by rintro z ⟨i,rfl⟩; exact hC i)
  have hCpair : ∀ z ∈ Set.range (C.map continuous_complexCoordinates),
      (a.1 : ℝ) ≤ z.1 ∧ z.1 ≤ (a.1 : ℝ)+w ∧
      (a.2 : ℝ) ≤ z.2 ∧ z.2 ≤ (a.2 : ℝ)+h := by
    rintro z ⟨i,rfl⟩
    exact hWbounds _ (hC i)
  obtain ⟨z,hzP,hzC⟩ := rectangle_boundary_arc_paths_intersect
    (a.1 : ℝ) ((a.1 : ℝ)+w) (a.2 : ℝ) ((a.2 : ℝ)+h)
    (latticePairCurve p) (C.map continuous_complexCoordinates)
    (by have := Nat.cast_nonneg (α := ℝ) w; linarith)
    (latticePairCurve_bounds p (vertexBounds p hPB)) hCpair
    (by change (u.val.1 : ℝ) = (a.1 : ℝ); exact_mod_cast hu)
    (by change (v.val.1 : ℝ) = (a.1 : ℝ)+w; exact_mod_cast hv)
    (rectangle_lower_dual_arc_clamped a w h u.val v.val s.val hs)
    (Or.inl (by change (latticeEmbed unitLatticeMesh t).im = (a.2 : ℝ)+h
                simp only [latticeEmbed_im,unitLatticeMesh,one_mul]
                exact_mod_cast ht))
  exact Set.disjoint_left.mp (latticePairCurve_disjoint p C hCdis) hzP hzC

end
end PottsContinuity.Thm3.Prop4
