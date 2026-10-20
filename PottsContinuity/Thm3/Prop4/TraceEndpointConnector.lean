module

public import PottsContinuity.Thm3.Prop4.PrimalHalfEdgeAvoidance
public import PottsContinuity.Thm3.Prop4.SampledBondAccessGeometry
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Order.CompletePartialOrder

/-! # A sampled crossing-bond connector to an unvisited primal endpoint -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial PD.FK.Curves PlanarTopology
noncomputable section

/-- The projected dual crossing segment together with the adjacent half
primal edge is path connected, stays in the original rectangle and avoids an
original walk whenever that endpoint is unvisited. Both incident face-center
projections and the endpoint itself belong to this connector. -/
theorem sampled_bond_endpoint_connector (a : LatticeVertex) (w h : ℕ)
    {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (e : RectangleDualEdgeCarrier a w h) (x : LatticeVertex)
    (hxB : x = (rectanglePrimalEdgeBond a w h e.primalEdge).source ∨
      x = (rectanglePrimalEdgeBond a w h e.primalEdge).target)
    (hxP : x ∉ p.support) :
    ∃ K : Set ℂ, IsPathConnected K ∧
      rectangleClamp a w h (dualFaceCenter unitLatticeMesh e.crossingBond.source) ∈ K ∧
      rectangleClamp a w h (dualFaceCenter unitLatticeMesh e.crossingBond.target) ∈ K ∧
      latticeEmbed unitLatticeMesh x ∈ K ∧
      (∀ z ∈ K, (a.1 : ℝ) ≤ z.re ∧ z.re ≤ (a.1 : ℝ)+w ∧
        (a.2 : ℝ) ≤ z.im ∧ z.im ≤ (a.2 : ℝ)+h) ∧
      Disjoint (Set.range (latticeWalkPath unitLatticeMesh p)) K := by
  classical
  have hInterval : IsPathConnected (Set.Icc (0 : ℝ) 1) :=
    (convex_Icc _ _).isPathConnected ⟨0,by norm_num⟩
  let endpointConnectorIntervalPathConnected : PathConnectedSpace unitInterval :=
    isPathConnected_iff_pathConnectedSpace.mp hInterval
  let b : RectanglePrimalBond a w h :=
    ⟨rectanglePrimalEdgeBond a w h e.primalEdge,rectanglePrimalEdgeBond_endpoints_mem_public a w h e.primalEdge⟩
  let m := b.val.midpoint unitLatticeMesh
  let D := rectangleClamp a w h '' dualBondSegment unitLatticeMesh e.crossingBond
  let I := segment ℝ m (latticeEmbed unitLatticeMesh x)
  have heP : e.primalEdge ∉ rectangleTraceConfiguration a w h p := by
    intro he
    have hedge := (mem_rectangleTraceConfiguration a w h p e.primalEdge).mp he
    have hbond := rectanglePrimalEdgeBond_toSym2_public a w h e.primalEdge
    rw [← hbond] at hedge
    rcases hxB with rfl | rfl
    · exact hxP (p.fst_mem_support_of_mem_edges hedge)
    · exact hxP (p.snd_mem_support_of_mem_edges hedge)
  have hD : IsPathConnected D := by
    have hsegment : IsPathConnected (dualBondSegment unitLatticeMesh e.crossingBond) := by
      rw [dualBondSegment,← Path.range_segment]
      exact isPathConnected_range (Path.segment _ _).continuous
    exact hsegment.image (continuous_rectangleClamp a w h)
  have hI : IsPathConnected I := by
    rw [show I = segment ℝ m (latticeEmbed unitLatticeMesh x) from rfl,← Path.range_segment]
    exact isPathConnected_range (Path.segment _ _).continuous
  have hmBounds := sampled_primal_bond_segment_bounds a w h b (b.val.midpoint_mem_segment unitLatticeMesh)
  have hmFixed := rectangleClamp_eq_self_of_bounds a w h m hmBounds
  have hmD : m ∈ D := ⟨m,sampled_bond_midpoint_mem_crossing_segment a w h e,hmFixed⟩
  have hmI : m ∈ I := left_mem_segment ℝ _ _
  have hID : Disjoint (Set.range (latticeWalkPath unitLatticeMesh p)) I :=
    primal_half_bond_segment_disjoint_walk unitLatticeMesh p b.val x hxB hxP
  have hDD : Disjoint (Set.range (latticeWalkPath unitLatticeMesh p)) D := by
    apply Set.disjoint_left.mpr
    rintro z hzP ⟨q,hq,rfl⟩
    exact Set.disjoint_left.mp (trace_closed_dualBond_disjoint_walk unitLatticeMesh a w h p e heP)
      hzP (rectangleClamp_dualBond_mem a w h e hq)
  refine ⟨D ∪ I,hD.union hI ⟨m,hmD,hmI⟩,?_,?_,?_,?_,hDD.union_right hID⟩
  · exact Or.inl ⟨_,left_mem_segment ℝ _ _,rfl⟩
  · exact Or.inl ⟨_,right_mem_segment ℝ _ _,rfl⟩
  · exact Or.inr (right_mem_segment ℝ _ _)
  · intro z hz
    rcases hz with ⟨q,_,rfl⟩ | hz
    · exact rectangleClamp_mem a w h q
    · apply sampled_primal_bond_segment_bounds a w h b
      apply (convex_segment _ _).segment_subset (b.val.midpoint_mem_segment unitLatticeMesh) _ hz
      rcases hxB with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _

end
end PottsContinuity.Thm3.Prop4
