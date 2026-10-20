module

public import PottsContinuity.Thm3.Prop4.MarkedLowerExcursionTrace
public import PottsContinuity.Thm3.Prop4.MarkedLowerRevealMembers
public import PottsContinuity.Thm3.Prop4.RecordedExcursionWitnesses

/-!
# All excursion record fields for the actual marked lower dual reveal

The trace is the actual two-mark connecting frontier trace, including every
vertex in the connecting component. Stopping stability, observation,
recorded-open walks, revealed-endpoint columns and sampled lower arms are
proved on this carrier; no extremal-selector or column interface is assumed.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PlanarTopology
noncomputable section

/-- The concrete raw marked lower-dual reveal and its connecting trace satisfy
EVERY primitive recorded excursion field. No point-mark arc converse is
needed: an excursion vertex itself witnesses a connecting frontier trace. -/
theorem markedLowerConnectingTrace_has_recorded_excursion_witnesses
    {n : ℕ} (hn : 1 ≤ n) (ε : ℝ)
    (u v : RectangleVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ))
    (huB : u.val ∈ box n) (hvB : v.val ∈ box n) :
    HasRecordedExcursionWitnesses n ε u.val v.val huB hvB
      (markedLowerConnectingTrace (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v) := by
  classical
  let markedExcursionWitnessCurrentEdgeEq :
      DecidableEq (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet := Classical.decEq _
  refine ⟨markedLowerDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val,
    markedLowerDualReveal_stable _ _ _ _ _,
    markedLowerConnectingTrace_eq_of_same_observation _ _ _ u v,?_,?_,?_⟩
  · intro A hA
    obtain ⟨z,_,hz⟩ := hA
    exact markedLowerConnectingTrace_recorded_walk_of_nonempty _ _ _ u v A ⟨z,hz⟩
  · intro z _ A hA
    obtain ⟨p,hp⟩ := markedLowerConnectingTrace_recorded_walk_of_nonempty _ _ _ u v A ⟨z,hA.2.1⟩
    let P := p.map (rectangleOpenGraphToSquare (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
      (A ∩ markedLowerDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val A))
    have hPB : ∀ w ∈ P.support, w ∈ box n := by
      intro w hw
      change w ∈ (p.map _).support at hw
      rw [SimpleGraph.Walk.support_map] at hw
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hw
      change x.val ∈ box n
      have hxB := x.property
      simpa only [latticeRectangle_neg_eq_box,PD.box,PottsContinuity.box] using hxB
    have htrace : rectangleTraceConfiguration (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) P ⊆ A :=
      (rectangle_open_walk_trace_subset (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) _ p).trans Finset.inter_subset_left
    have hPTrace : P.support.toFinset = markedLowerConnectingTrace (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v A := by
      change (p.map _).support.toFinset = _
      rw [SimpleGraph.Walk.support_map]
      exact hp.symm
    intro e he
    have hcol := markedLowerDualReveal_bond_columns n A u v hu hv P hPB htrace e he
    have support_mem (w : LatticeVertex) (hw : w ∈ P.support) :
        w ∈ markedLowerConnectingTrace (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v A := by
      rw [← hPTrace]
      exact List.mem_toFinset.mpr hw
    obtain ⟨⟨w,hw,hws⟩,⟨w',hw',hwt⟩⟩ := hcol
    exact ⟨⟨w,support_mem w (List.mem_toFinset.mp hw),hws⟩,
      ⟨w',support_mem w' (List.mem_toFinset.mp hw'),hwt⟩⟩
  · intro z hz A hA
    have hne : z ≠ u.val := by
      intro he
      exact (Finset.mem_filter.mp hz).2.1
        (he.symm ▸ (inductionTube_endpoints hn ε u.val v.val huB hvB).1)
    exact markedLowerConnectingTrace_vertex_lower_arm (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v
      ⟨z,by rw [latticeRectangle_neg_eq_box]; exact (Finset.mem_filter.mp hz).1⟩ A hA.2.1 hne

end
end PottsContinuity.Thm3.Prop4
