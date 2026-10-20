-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverFaceTransverseFillingStep.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceTransverseFilling
public import PottsContinuity.FKC.Medial.ParafermionicCoverCompass
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC

/-- The disagreement edge for any of the four actual neighboring retained-face
steps is the literal transverse edge at the selected common base. -/
theorem parafermionicCoverSimpleCycleFillingSet_adjacent_disagree_iff_rawMappedEdge
    {n : ℕ} (hn : 1 ≤ n) {u₀ : ParafermionicCoverBoxVertex n}
    (C : (parafermionicCoverBoxGraph n).Walk u₀ u₀) (hC : C.IsCycle)
    (i j : ParafermionicCoverFiniteFaceTopIndex n) (d : Fin 4)
    (h : j.1 = parafermionicCoverCompassNeighbor i.1 d) :
    let b := if d = 0 ∨ d = 1 then j.1 else i.1
    let t : Fin 4 := if d = 0 ∨ d = 2 then 1 else 0
    ¬ (i ∈ parafermionicCoverSimpleCycleFillingSet hn C hC ↔
       j ∈ parafermionicCoverSimpleCycleFillingSet hn C hC) ↔
      s(b, parafermionicCoverCompassNeighbor b t) ∈
        C.edges.map (Sym2.map Subtype.val) := by
  dsimp
  fin_cases d
  · simpa using
      parafermionicCoverSimpleCycleFillingSet_east_disagree_iff_rawMappedEdge
        hn C hC i j h
  · simpa [Sym2.eq_swap] using
      parafermionicCoverSimpleCycleFillingSet_north_disagree_iff_rawMappedEdge
        hn C hC i j h
  · have hrev : i.1 = parafermionicCoverCompassNeighbor j.1 0 := by
      rw [h]
      simpa using (parafermionicCoverCompassNeighbor_reverse i.1 2).symm
    have hEast :=
      parafermionicCoverSimpleCycleFillingSet_east_disagree_iff_rawMappedEdge
        hn C hC j i hrev
    simpa [iff_comm] using hEast
  · have hrev : i.1 = parafermionicCoverCompassNeighbor j.1 1 := by
      rw [h]
      simpa using (parafermionicCoverCompassNeighbor_reverse i.1 3).symm
    have hNorth :=
      parafermionicCoverSimpleCycleFillingSet_north_disagree_iff_rawMappedEdge
        hn C hC j i hrev
    simpa [iff_comm, Sym2.eq_swap] using hNorth

end PottsContinuity.FKC.Medial
