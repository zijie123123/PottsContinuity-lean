/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/ParafermionicCoverContourBoundary.lean`.
Adaptation: namespace/import relocation, exact cover carrier.
-/
module

public import PottsContinuity.Thm4.FinitePorts
public import PottsContinuity.Thm4.Exploration
public import PottsContinuity.Thm4.CoverConfiguration
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
noncomputable section

local instance coverContourAmbientFintype (n : ℕ) :
    Fintype (ParafermionicAmbientVertex n) := Fintype.ofFinite _

/-- The port's original lifted edge has its other endpoint in the actual box. -/
def parafermionicCoverFinitePortOtherEndpointInBox (n : ℕ)
    (c : ParafermionicCoverFinitePort n) : Prop :=
  parafermionicCoverPortOtherVertex c.1 ∈ parafermionicCoverBoxVertices n

/-- Since the port itself is retained, checking its other endpoint is equivalent
to checking both endpoints of the literal lifted edge. -/
theorem parafermionicCoverFinitePortEdgeEndpointsInBox_iff (n : ℕ)
    (c : ParafermionicCoverFinitePort n) :
    (∀ v ∈ (parafermionicCoverPortEdge c.1).1,
      v ∈ parafermionicCoverBoxVertices n) ↔
        parafermionicCoverFinitePortOtherEndpointInBox n c := by
  rw [parafermionicCoverPortEdge_eq_incident_pair]
  constructor
  · intro h
    exact h _ (Sym2.mem_mk_right _ _)
  · intro h v hv
    rcases (Sym2.mem_iff').mp hv with hv | hv
    · simpa [hv] using c.2
    · change parafermionicCoverPortOtherVertex c.1 ∈
        parafermionicCoverBoxVertices n at h
      simpa [hv] using h

/-- Every lifted port joins its actual primal vertex to the other endpoint of
its normalized unit bond in the cover graph. -/
theorem parafermionicCoverPortVertex_otherEndpoint_adj
    (c : ParafermionicCoverPort) :
    parafermionicCoverGraph.Adj (parafermionicCoverPortVertex c)
      (parafermionicCoverPortOtherVertex c) := by
  rw [parafermionicCoverPortOtherVertex_eq_neighborLift]
  rcases c with ⟨⟨b, tip, side⟩, k⟩
  cases tip with
  | false =>
      change parafermionicCoverGraph.Adj (b.source, k)
        (parafermionicCoverNeighborLift (b.source, k) b.target)
      exact parafermionicCoverNeighborLift_adj _ _ b.adjacent
  | true =>
      change parafermionicCoverGraph.Adj (b.target, k)
        (parafermionicCoverNeighborLift (b.target, k) b.source)
      exact parafermionicCoverNeighborLift_adj _ _ b.adjacent.symm

/-- A corner occurrence oriented from an internal original-edge port to its
corner-paired port whose original edge exits the finite box. -/
def parafermionicCoverExposedCornerOccurrence (n : ℕ) :=
  {c : ParafermionicCoverFinitePort n //
    parafermionicCoverFinitePortOtherEndpointInBox n c ∧
      ¬ parafermionicCoverFinitePortOtherEndpointInBox n
        (parafermionicCoverFiniteCornerPairPerm n c)}

/-- The actual primal corner supporting an exposed occurrence. -/
def parafermionicCoverExposedCornerVertex (n : ℕ)
    (c : parafermionicCoverExposedCornerOccurrence n) : ParafermionicCoverVertex :=
  parafermionicCoverPortVertex c.1.1

theorem parafermionicCoverExposedCorner_vertex_mem_box (n : ℕ)
    (c : parafermionicCoverExposedCornerOccurrence n) :
    parafermionicCoverExposedCornerVertex n c ∈ parafermionicCoverBoxVertices n :=
  c.1.2

/-- Every exposed occurrence is at an actual cover vertex with an actual
nearest-neighbor outside the box. This includes the top and bottom sheets. -/
theorem parafermionicCoverExposedCorner_has_outside_neighbor (n : ℕ)
    (c : parafermionicCoverExposedCornerOccurrence n) :
    ∃ w : ParafermionicCoverVertex,
      parafermionicCoverGraph.Adj (parafermionicCoverExposedCornerVertex n c) w ∧
        w ∉ parafermionicCoverBoxVertices n := by
  refine ⟨parafermionicCoverPortOtherVertex
      (parafermionicCoverFiniteCornerPairPerm n c.1).1, ?_, c.2.2⟩
  change parafermionicCoverGraph.Adj (parafermionicCoverPortVertex c.1.1)
    (parafermionicCoverPortOtherVertex
      (parafermionicCoverCornerPair c.1.1))
  rw [← parafermionicCoverCornerPair_vertex]
  exact parafermionicCoverPortVertex_otherEndpoint_adj _

local instance parafermionicCoverExposedCornerFintype (n : ℕ) :
    Fintype (parafermionicCoverExposedCornerOccurrence n) :=
  Fintype.ofInjective (fun c : parafermionicCoverExposedCornerOccurrence n => c.1)
    (fun _ _ h => Subtype.ext h)

def parafermionicCoverExposedCorners (n : ℕ) :
    Finset (parafermionicCoverExposedCornerOccurrence n) := Finset.univ

end
end PottsContinuity.Thm4
