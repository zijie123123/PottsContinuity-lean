module

public import PottsContinuity.Thm3.RSW.FiniteDualClosure

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.RCInfinite

/-- Opening original sampled bonds can only delete edges from the actual
closed-dual graph, with all original face labels retained. -/
theorem finite_closedDualGraph_antitone (V : Finset LatticeVertex) :
    Antitone (fun A : Configuration (squareLattice.induce (V : Set LatticeVertex)) =>
      wholePlaneClosedDualGraph (finiteSubgraphConfiguration V 0 A)) := by
  intro A B hAB u v huv
  obtain ⟨b,hb,hends⟩ := huv
  refine ⟨b,?_,hends⟩
  change decide (latticeBondEdge b ∈ A.map (frozenEdgeEmbedding V)) = false
  change decide (latticeBondEdge b ∈ B.map (frozenEdgeEmbedding V)) = false at hb
  rw [decide_eq_false_iff_not] at hb ⊢
  exact fun ha => hb ((Finset.map_subset_map.mpr hAB) ha)

end PottsContinuity.RSW
