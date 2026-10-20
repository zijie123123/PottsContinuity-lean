module

public import PottsContinuity.Thm3.RSW.Lemma4MiddleBandDisjoint
public import PottsContinuity.Thm3.RSW.FiniteDualRectangleLocality

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.RCInfinite
noncomputable section

/-- Adding sampled bonds that do not contain this original bond leaves its
literal closed-extension state unchanged. -/
theorem finiteSubgraphConfiguration_union_bondState_of_not_mem_image
    (V : Finset LatticeVertex)
    (A K : Configuration (finiteLatticeGraph V))
    (c : LatticeBond) (hK : latticeBondEdge c ∉ K.map (frozenEdgeEmbedding V)) :
    latticeConfigurationBondState (finiteSubgraphConfiguration V 0 (A ∪ K)) c =
      latticeConfigurationBondState (finiteSubgraphConfiguration V 0 A) c := by
  simp only [latticeConfigurationBondState,finiteSubgraphConfiguration,dite_true]
  congr 1
  apply propext
  rw [Finset.map_union,Finset.mem_union]
  exact or_iff_left hK

/-- Restoring ANY observed middle configuration preserves each exact source
dual band event. This discharges dependence on the frozen middle open states. -/
theorem lemma4DualBandEvent_union_middle_iff (n : ℕ) (i : Fin 2)
    (A K : Configuration (lemma4AmbientGraph n)) (hK : K ⊆ lemma4MiddleReveal n) :
    A ∪ K ∈ lemma4DualBandEvent n i ↔ A ∈ lemma4DualBandEvent n i := by
  have hstate (c : LatticeBond)
      (hc : latticeBondEdge c ∉ (lemma4MiddleReveal n).map (frozenEdgeEmbedding (box (56*n)))) :
      latticeConfigurationBondState (finiteSubgraphConfiguration (box (56*n)) 0 (A ∪ K)) c =
        latticeConfigurationBondState (finiteSubgraphConfiguration (box (56*n)) 0 A) c :=
    finiteSubgraphConfiguration_union_bondState_of_not_mem_image _ A K c
      (fun hm => hc ((Finset.map_subset_map.mpr hK) hm))
  refine Fin.cases ?_ (fun j => ?_) i
  · apply finiteClosedDualHorizontalRectangle_iff_of_bondStates
    intro c hf ht
    exact hstate c (lemma4MiddleReveal_excludes_upper_dualBond n c hf.2.2.1 ht.2.2.1)
  · apply finiteClosedDualHorizontalRectangle_iff_of_bondStates
    intro c hf ht
    exact hstate c (lemma4MiddleReveal_excludes_lower_dualBond n c hf.2.2.2 ht.2.2.2)

end
end PottsContinuity.RSW
