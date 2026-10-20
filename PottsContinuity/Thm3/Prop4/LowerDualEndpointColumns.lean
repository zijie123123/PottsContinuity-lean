module

public import PottsContinuity.Thm3.Prop4.LowerDualEndpointSeparation
public import PottsContinuity.Thm3.Prop4.LowerTraceHull
public import PottsContinuity.PlanarTopology.BoxSampledDualScreen

/-! # Exact column witnesses for a lower-dual reached queried endpoint -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial PlanarTopology
noncomputable section

/-- In the centered box a lower-dual reached endpoint lies in the literal
filled lower trace hull of ANY actual prescribed open crossing walk. -/
theorem lower_dual_reached_endpoint_mem_lowerTraceHull (n : ℕ)
    (A : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)))
    (u v : RectangleVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ))
    (p : PD.squareLattice.Walk u.val v.val) (hPB : ∀ z ∈ p.support, z ∈ box n)
    (htrace : rectangleTraceConfiguration (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) p ⊆ A)
    (e : RectangleDualEdgeCarrier (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (x : RectangleVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (hx : x.val = (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e.primalEdge).source ∨
      x.val = (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e.primalEdge).target)
    (hreach : (∃ s ∈ rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val,
        (rectangleSampledClosedDualGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) A).Reachable s e.crossingBond.source) ∨
      (∃ s ∈ rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val,
        (rectangleSampledClosedDualGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) A).Reachable s e.crossingBond.target)) :
    x.val ∈ lowerTraceHull n p.support.toFinset := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨?_,?_⟩
  · have hxB := x.property
    simpa only [latticeRectangle_neg_eq_box,PD.box,PottsContinuity.box] using hxB
  · rintro ⟨t,ht,Q,hQ⟩
    apply lower_dual_reached_endpoint_no_top_avoiding_walk (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
      A u v hu (by dsimp; omega) p ?_ htrace e x hx hreach t Q ?_ (by dsimp; omega) ?_
    · intro z hz
      rw [latticeRectangle_neg_eq_box]
      exact hPB z hz
    · intro z hz
      rw [latticeRectangle_neg_eq_box]
      exact (hQ z hz).1
    · intro z hz hzp
      exact (hQ z hz).2 (List.mem_toFinset.mpr hzp)

/-- The exact original endpoint column witness follows from sampled dual
access, with no independent column or source-extremality assumption. -/
theorem lower_dual_reached_endpoint_column_witness (n : ℕ)
    (A : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)))
    (u v : RectangleVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ))
    (p : PD.squareLattice.Walk u.val v.val) (hPB : ∀ z ∈ p.support, z ∈ box n)
    (htrace : rectangleTraceConfiguration (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) p ⊆ A)
    (e : RectangleDualEdgeCarrier (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (x : RectangleVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (hx : x.val = (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e.primalEdge).source ∨
      x.val = (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e.primalEdge).target)
    (hreach : (∃ s ∈ rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val,
        (rectangleSampledClosedDualGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) A).Reachable s e.crossingBond.source) ∨
      (∃ s ∈ rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val,
        (rectangleSampledClosedDualGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) A).Reachable s e.crossingBond.target)) :
    ∃ z ∈ p.support.toFinset, x.val.1 = z.1 ∧ x.val.2 ≤ z.2 := by
  exact lowerTraceHull_column_witness n p.support.toFinset x.val
    (lower_dual_reached_endpoint_mem_lowerTraceHull n A u v hu hv p hPB htrace e x hx hreach)

end
end PottsContinuity.Thm3.Prop4
