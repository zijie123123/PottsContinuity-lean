module

public import PottsContinuity.Thm3.OuterCircuit.EnvelopeShell
public import PottsContinuity.Exploration.ConnectedCellSetCycleEnvelope

@[expose] public section

namespace PottsContinuity.OuterCircuit

open PottsContinuity.PD.FK
open PottsContinuity.PD.Duality
open PottsContinuity.FKC
open PottsContinuity.Exploration
open PottsContinuity.RSW

noncomputable section

theorem outerCircuitShapedCandidates_have_envelope {n : ℕ}
    (i j : OuterCircuitPolygonCode n)
    (hi : outerCircuitCandidateShape i)
    (hj : outerCircuitCandidateShape j) :
    ∃ z : PD.FK.LatticeVertex, ∃ c : PD.FK.squareLattice.Walk z z,
      ∃ hc : c.IsCycle,
        (outerCircuitEnvelopePolygon (sourcePolygonWalk (outerCircuitCodePolygon i))
          (sourcePolygonWalk_isCycle (outerCircuitCodePolygon i))).interiorCellBases
            ⟨1, zero_lt_one⟩ ∪
        (outerCircuitEnvelopePolygon (sourcePolygonWalk (outerCircuitCodePolygon j))
          (sourcePolygonWalk_isCycle (outerCircuitCodePolygon j))).interiorCellBases
            ⟨1, zero_lt_one⟩ ⊆
        (outerCircuitEnvelopePolygon c hc).interiorCellBases ⟨1, zero_lt_one⟩ ∧
        (∀ y, rayIndex y (sourcePolygonWalk (outerCircuitCodePolygon i)) ≠ 0 →
          rayIndex y c ≠ 0) ∧
        (∀ y, rayIndex y (sourcePolygonWalk (outerCircuitCodePolygon j)) ≠ 0 →
          rayIndex y c ≠ 0) ∧
        ∀ e ∈ c.edges,
          e ∈ (sourcePolygonWalk (outerCircuitCodePolygon i)).edges ∨
          e ∈ (sourcePolygonWalk (outerCircuitCodePolygon j)).edges := by
  let P := outerCircuitCodePolygon i
  let Q := outerCircuitCodePolygon j
  let p := sourcePolygonWalk P
  let q := sourcePolygonWalk Q
  have hp : p.IsCycle := sourcePolygonWalk_isCycle P
  have hq : q.IsCycle := sourcePolygonWalk_isCycle Q
  have hxP : rayIndex (PottsContinuity.Push.faceIndexMark (-1, -1)) p ≠ 0 := by
    simpa [P, p] using outerCircuitCandidateShape_origin_rayIndex_ne_zero i hi
  have hxQ : rayIndex (PottsContinuity.Push.faceIndexMark (-1, -1)) q ≠ 0 := by
    simpa [Q, q] using outerCircuitCandidateShape_origin_rayIndex_ne_zero j hj
  obtain ⟨z, c, hc, hfill, hrayP, hrayQ, hEdges⟩ :=
    two_cycle_union_has_boundary_cycle_envelope p q hp hq
      ⟨1, zero_lt_one⟩ (-1, -1) hxP hxQ
  refine ⟨z, c, hc, ?_, ?_, ?_, ?_⟩
  · simpa [P, Q, p, q, outerCircuitEnvelopePolygon] using hfill
  · exact hrayP
  · exact hrayQ
  · exact hEdges

end
end PottsContinuity.OuterCircuit
