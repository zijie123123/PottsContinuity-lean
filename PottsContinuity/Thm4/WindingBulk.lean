module

public import PottsContinuity.Thm4.ModifiedObservableSum

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
noncomputable section

local instance windingBulkEdgeFintype (n : ℕ) :
    Fintype (ParafermionicAmbientGraph n).edgeSet := Fintype.ofFinite _
local instance windingBulkPortFintype (n : ℕ) :
    Fintype (ParafermionicCoverFinitePort n) := Fintype.ofFinite _

local instance windingBulkInternalDecidable (n : ℕ) :
    DecidablePred (parafermionicCoverFinitePortOtherEndpointInBox n) := Classical.decPred _

/-- The actual induced finite edge queried by an internal retained port. -/
def internalPortEdge (n : ℕ) (c : ParafermionicCoverFinitePort n)
    (hc : parafermionicCoverFinitePortOtherEndpointInBox n c) :
    (ParafermionicAmbientGraph n).edgeSet :=
  ⟨s((⟨parafermionicCoverPortVertex c.1, c.2⟩ : ParafermionicAmbientVertex n),
      (⟨parafermionicCoverPortOtherVertex c.1, hc⟩ : ParafermionicAmbientVertex n)),
    (ParafermionicAmbientGraph n).mem_edgeSet.mpr
      (parafermionicCoverPortVertex_otherEndpoint_adj c.1)⟩

@[simp] theorem internalPortEdge_projection (n : ℕ) (c : ParafermionicCoverFinitePort n)
    (hc : parafermionicCoverFinitePortOtherEndpointInBox n c) :
    Sym2.map Subtype.val (internalPortEdge n c hc).val = (parafermionicCoverPortEdge c.1).val := by
  rw [parafermionicCoverPortEdge_eq_incident_pair]
  rfl

/-- Every internal port belongs to exactly the fiber of its actual induced edge. -/
theorem windingEdgePorts_mem_iff_internal_edge (n : ℕ) (c : ParafermionicCoverFinitePort n)
    (hc : parafermionicCoverFinitePortOtherEndpointInBox n c)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    c ∈ windingEdgePorts n e ↔ e = internalPortEdge n c hc := by
  classical
  simp only [windingEdgePorts, Finset.mem_filter, Finset.mem_univ, true_and, hc]
  constructor
  · intro h
    apply Subtype.ext
    apply Sym2.map.injective (show Function.Injective
      (Subtype.val : ParafermionicAmbientVertex n → ParafermionicCoverVertex) from Subtype.val_injective)
    exact h.symm.trans (internalPortEdge_projection n c hc).symm
  · rintro rfl
    exact (internalPortEdge_projection n c hc).symm

/-- Partition the internal contour ports by their literal finite primal edge.
The edge is constructed from both actual endpoints, without any choice. -/
theorem sum_windingEdgePorts_eq_internal_sum (n : ℕ)
    (F : ParafermionicCoverFinitePort n → ℂ) :
    (∑ e : (ParafermionicAmbientGraph n).edgeSet, ∑ c ∈ windingEdgePorts n e, F c) =
      ∑ c ∈ Finset.univ.filter (parafermionicCoverFinitePortOtherEndpointInBox n), F c := by
  classical
  simp only [windingEdgePorts, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : parafermionicCoverFinitePortOtherEndpointInBox n c
  · have hfiber (e : (ParafermionicAmbientGraph n).edgeSet) :
        (parafermionicCoverPortEdge c.1).val = Sym2.map Subtype.val e.val ↔
          e = internalPortEdge n c hc := by
      have h := windingEdgePorts_mem_iff_internal_edge n c hc e
      simpa only [windingEdgePorts, Finset.mem_filter, Finset.mem_univ, true_and, hc] using h
    simp_rw [hc, true_and, hfiber]
    simp
  · simp only [hc, false_and, ↓reduceIte, Finset.sum_const_zero]

/-- The actual q=4 modified contour bulk vanishes under the free finite FK law. -/
theorem modifiedPathExpectation_four_bulk_zero (n : ℕ) (hn : 1 ≤ n) :
    (∑ c ∈ Finset.univ.filter (parafermionicCoverFinitePortOtherEndpointInBox n),
      (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℂ) else -1) *
        parafermionicCoverModifiedPathExpectation ⟨4, by norm_num⟩ n hn (c, true)) = 0 := by
  rw [← sum_windingEdgePorts_eq_internal_sum]
  exact Finset.sum_eq_zero (fun e _ => modifiedPathExpectation_four_edge_defect_zero n hn e)

end
end PottsContinuity.Thm4
