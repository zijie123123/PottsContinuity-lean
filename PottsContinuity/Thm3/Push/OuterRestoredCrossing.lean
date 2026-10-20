module

public import PottsContinuity.Thm3.Push.OuterWitnessComparison
public import PottsContinuity.Thm3.Push.EmbeddedRestrictionStates
public import PottsContinuity.Thm3.Push.ActiveRestrictionRetention
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance outerRestoredEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- An actual reference witness retained in the OUTER remaining graph forces
the shorter target crossing when the actual outer record is restored. The
reference rectangle need not contain the whole outer domain or its boundary. -/
theorem outer_restored_crossing_of_active_reference_witness {V : Type*} [Finite V]
    (a : LatticeVertex) (w h n : ℕ) (hn : n ≤ h) (G : SimpleGraph V)
    (f : RectangleVertex a w h ↪ V) (hRG : (rectangleGraph a w h).map f ≤ G)
    (A : Configuration G)
    (hA : embeddedConfigurationRestriction _ _ f hRG A ∈ rectangleHorizontalCrossingEvent a w h)
    (C : Configuration (edgeRestriction G (embeddedFilledTopReveal a w h G f hRG A)))
    (hC : embeddedConfigurationRestriction _ _ ((Function.Embedding.subtype _).trans f)
        (activeUnexaminedGraph_map_le_outer_remaining (rectangleGraph a w h) G f hRG
          (rectangleFilledTopReveal a w h (embeddedConfigurationRestriction _ _ f hRG A))) C ∈
      upwardEmbeddedEvent _ _ (Function.Embedding.subtype _) (activeUnexaminedGraph_map_le _ _)
        (DualityExt.rectangleInnerHorizontalCrossingEvent (rectangle_height_subset a w n h hn))) :
    DualityExt.rectangleConfigurationRestriction (rectangle_height_subset a w n h hn)
      (embeddedConfigurationRestriction _ _ f hRG
        (restoreRemainingConfiguration _ _
          ⟨A ∩ embeddedFilledTopReveal a w h G f hRG A,Finset.inter_subset_right⟩ C)) ∈
      rectangleHorizontalCrossingEvent a w n := by
  let D := embeddedConfigurationRestriction _ _ f hRG A
  let R := rectangleFilledTopReveal a w h D
  let Rout := embeddedFilledTopReveal a w h G f hRG A
  let F : RemovedConfiguration G Rout := ⟨A ∩ Rout,Finset.inter_subset_right⟩
  let restored := restoreRemainingConfiguration G Rout F C
  let D' := embeddedConfigurationRestriction _ _ f hRG restored
  let J := activeUnexaminedGraph (rectangleGraph a w h) R
  let j : unexaminedVertices (rectangleGraph a w h) R ↪ V := (Function.Embedding.subtype _).trans f
  have hrecordOuter : restored ∩ Rout=A ∩ Rout := restoreRemainingConfiguration_inter _ _ _ C
  have hrecord : D' ∩ R=D ∩ R :=
    embedded_record_agreement_restrict _ _ f hRG R A restored hrecordOuter
  have hstates : embeddedConfigurationRestriction J (rectangleGraph a w h)
      (Function.Embedding.subtype _) (activeUnexaminedGraph_map_le _ _) D' =
      embeddedConfigurationRestriction J (edgeRestriction G Rout) j
        (activeUnexaminedGraph_map_le_outer_remaining (rectangleGraph a w h) G f hRG R) C := by
    change embeddedConfigurationRestriction J (rectangleGraph a w h)
      (Function.Embedding.subtype _) (activeUnexaminedGraph_map_le _ _)
        (embeddedConfigurationRestriction _ _ f hRG restored) = _
    rw [← embeddedConfigurationRestriction_comp]
    exact embedded_restriction_restore_remaining J G Rout j
      (activeUnexaminedGraph_map_le_outer_remaining (rectangleGraph a w h) G f hRG R) F C
  obtain ⟨B,hB,hsub⟩ := hC
  apply nested_crossing_of_active_restriction_domination a w n h hn D D' B hA hrecord ?_ hB
  rw [hstates]
  exact hsub

end
end PottsContinuity.Push
