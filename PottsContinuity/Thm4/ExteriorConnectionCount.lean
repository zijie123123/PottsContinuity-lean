module

public import PottsContinuity.Thm4.ExteriorDirections

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (n : ℕ) : Fintype (ParafermionicAmbientVertex n) := Fintype.ofFinite _

/-- All retained cover vertices with an actual nearest neighbor outside the box. -/
def coverExteriorBoundary (n : ℕ) : Finset (ParafermionicAmbientVertex n) :=
  Finset.univ.filter fun v => ∃ w : ParafermionicCoverVertex,
    parafermionicCoverGraph.Adj v.1 w ∧ w ∉ parafermionicCoverBoxVertices n

/-- Boundary vertices actually connected to the origin in the given configuration. -/
def connectedExteriorVertices (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n)) :
    Finset (ParafermionicAmbientVertex n) :=
  (coverExteriorBoundary n).filter fun v =>
    ActualConnected (ParafermionicAmbientGraph n) A (parafermionicCoverBoxOrigin n) v

/-- A visited incoming exterior port has a connected primal vertex on the actual
exterior boundary; no virtual boundary wiring is used. -/
theorem exteriorIncomingVisit_vertex_mem (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) (c : ParafermionicCoverFinitePort n)
    (hc : c ∈ exteriorIncomingVisits n hn A) :
    parafermionicCoverFinitePortPrimalVertex n c ∈ connectedExteriorVertices n A := by
  obtain ⟨he, hf, hv⟩ := (Finset.mem_filter.mp hc).2
  apply Finset.mem_filter.mpr
  refine ⟨?_, ?_⟩
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, parafermionicCoverPortOtherVertex c.1,
      parafermionicCoverPortVertex_otherEndpoint_adj c.1, he⟩
  · exact parafermionicCoverOriginExplorationVisitEvent_subset_actualConnection n hn
      (c, false) hv

/-- Each connected boundary vertex accounts for at most three visited incoming
exterior ports, pointwise for every actual finite configuration. -/
theorem exteriorIncomingVisits_card_le_three_connected (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    (exteriorIncomingVisits n hn A).card ≤ 3 * (connectedExteriorVertices n A).card := by
  let S := exteriorIncomingVisits n hn A
  let T := connectedExteriorVertices n A
  have hmap : Set.MapsTo (parafermionicCoverFinitePortPrimalVertex n) (S : Set _) (T : Set _) :=
    fun c hc => exteriorIncomingVisit_vertex_mem n hn A c hc
  have hsum := Finset.card_eq_sum_card_fiberwise hmap
  change S.card ≤ 3 * T.card
  rw [hsum]
  calc
    _ ≤ ∑ v ∈ T, 3 := by
      apply Finset.sum_le_sum
      intro v hv
      apply le_trans (Finset.card_le_card ?_)
        (exterior_incoming_ports_at_vertex_card_le_three n hn v)
      intro c hc
      obtain ⟨hcS, hcv⟩ := Finset.mem_filter.mp hc
      obtain ⟨he, hf, _⟩ := (Finset.mem_filter.mp hcS).2
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, congrArg Subtype.val hcv, he, hf⟩
    _ = 3 * T.card := by simp [Nat.mul_comm]

end
end PottsContinuity.Thm4
