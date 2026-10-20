module

public import PottsContinuity.Thm3.Prop4.MarkedLowerRevealHull
public import PottsContinuity.Thm3.Prop4.MarkedLowerExcursionTrace

/-! # Actual raw endpoints avoid top access to the concrete marked trace -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PlanarTopology
noncomputable section
local instance markedRectangleRawAccessEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- The literal endpoints of an actual original rectangle edge are precisely
its normalized bond endpoints, independently of their chosen orientation. -/
theorem rectangle_edge_vertex_normalized_endpoint (a : LatticeVertex) (w h : ℕ)
    (e : (rectangleGraph a w h).edgeSet) (x : RectangleVertex a w h) (hx : x ∈ e.val) :
    x.val = (rectanglePrimalEdgeBond a w h e).source ∨
      x.val = (rectanglePrimalEdgeBond a w h e).target := by
  have hh : x.val ∈ Sym2.map (fun z : RectangleVertex a w h => z.val) e.val :=
    Sym2.mem_map.mpr ⟨x,hx,rfl⟩
  erw [← rectanglePrimalEdgeBond_toSym2_public] at hh
  exact Sym2.mem_iff.mp hh

/-- For a nonempty actual connecting trace, every queried raw bond endpoint
is top-inaccessible while avoiding that SAME trace. -/
theorem markedLowerDualReveal_endpoint_no_top_access (n : ℕ)
    (u v : RectangleVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ))
    (A : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)))
    (hne : (markedLowerConnectingTrace (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v A).Nonempty)
    (e : (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet)
    (he : e ∈ markedLowerDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val A)
    (x : RectangleVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) (hx : x ∈ e.val) :
    ¬traceTopAccessible n
      (markedLowerConnectingTrace (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v A) x.val := by
  classical
  obtain ⟨p,hp⟩ := markedLowerConnectingTrace_recorded_walk_of_nonempty _ _ _ u v A hne
  let P := p.map (rectangleOpenGraphToSquare (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
    (A ∩ markedLowerDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val A))
  have hPB : ∀ z ∈ P.support, z ∈ box n := by
    intro z hz
    change z ∈ (p.map _).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hz
    change y.val ∈ box n
    simpa only [latticeRectangle_neg_eq_box,PD.box,PottsContinuity.box] using y.property
  have htrace : rectangleTraceConfiguration (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) P ⊆ A :=
    (rectangle_open_walk_trace_subset _ _ _ _ p).trans Finset.inter_subset_left
  have hPTrace : P.support.toFinset =
      markedLowerConnectingTrace (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v A := by
    change (p.map _).support.toFinset = _
    rw [SimpleGraph.Walk.support_map]
    exact hp.symm
  obtain ⟨hs,ht⟩ := markedLowerDualReveal_endpoints_mem_lowerTraceHull n A u v hu hv P hPB htrace e he
  have hxH : x.val ∈ lowerTraceHull n P.support.toFinset := by
    rcases rectangle_edge_vertex_normalized_endpoint _ _ _ e x hx with h | h
    · exact h.symm ▸ hs
    · exact h.symm ▸ ht
  have hno := (Finset.mem_filter.mp hxH).2
  rw [hPTrace] at hno
  exact hno

end
end PottsContinuity.Thm3.Prop4
