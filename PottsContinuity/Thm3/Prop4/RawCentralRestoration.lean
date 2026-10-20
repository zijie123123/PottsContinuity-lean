module

public import PottsContinuity.Thm3.Prop4.EmbeddedFreshRestriction

/-! # Literal fresh-edge restriction and restoration on the marked union -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK Push Exploration
noncomputable section
local instance rawCentralRestorationEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- The retained union keeps whole fresh edge components attached to the
actual recorded marked class. There is no vertex-access truncation. -/
def sourceMarkedRawCentralGraph (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h)) :=
  (sourceMarkedRawDomain a w h u v A).induce (sourceMarkedRawCentralVertices a w h u v A)

/-- The retained graph uses only actual original fresh bonds. -/
theorem sourceMarkedRawCentralGraph_map_le_original (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h)) :
    (sourceMarkedRawCentralGraph a w h u v A).map (pocketInclusion (sourceMarkedRawCentralVertices a w h u v A)) ≤
      rectangleGraph a w h :=
  (pocketInduced_map_le _ _).trans (edgeRestriction_le _ _)

/-- Read exactly the marked union's fresh original bonds from the reference. -/
def sourceMarkedRawCentralRestriction (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h)) :=
  embeddedConfigurationRestriction (sourceMarkedRawCentralGraph a w h u v A) (rectangleGraph a w h)
    (pocketInclusion (sourceMarkedRawCentralVertices a w h u v A))
    (sourceMarkedRawCentralGraph_map_le_original a w h u v A)

/-- Direct original restriction agrees with the actual remaining-edge
projection in the proved stopped central law. -/
theorem sourceMarkedRawCentralRestriction_eq_remaining (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A B : Configuration (rectangleGraph a w h)) :
    sourceMarkedRawCentralRestriction a w h u v A B =
      embeddedConfigurationRestriction (sourceMarkedRawCentralGraph a w h u v A)
        (sourceMarkedRawDomain a w h u v A) (pocketInclusion (sourceMarkedRawCentralVertices a w h u v A))
        (pocketInduced_map_le _ _) (sourceMarkedRawRemainingConfiguration a w h u v A B) := by
  exact embeddedFreshRestriction_eq_remaining (rectangleGraph a w h) (sourceMarkedRawReveal a w h u v A)
    (sourceMarkedRawCentralGraph a w h u v A) (pocketInclusion (sourceMarkedRawCentralVertices a w h u v A))
    (pocketInduced_map_le _ _) B

/-- Restore exactly the actual raw recorded open bonds and the supplied
fresh union bonds. Other fresh components are marginalized, never queried. -/
def sourceMarkedRawCentralRestoration (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h))
    (K : Configuration (sourceMarkedRawCentralGraph a w h u v A)) : Configuration (rectangleGraph a w h) :=
  (revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A).val ∪
    embeddedConfigurationEmbedding (sourceMarkedRawCentralGraph a w h u v A) (rectangleGraph a w h)
      (pocketInclusion (sourceMarkedRawCentralVertices a w h u v A))
      (sourceMarkedRawCentralGraph_map_le_original a w h u v A) K

/-- The corrected union restoration preserves the original bond order. -/
theorem sourceMarkedRawCentralRestoration_mono (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h)) :
    Monotone (sourceMarkedRawCentralRestoration a w h u v A) := by
  intro K L hKL
  unfold sourceMarkedRawCentralRestoration
  rw [embeddedConfigurationEmbedding_eq_map,embeddedConfigurationEmbedding_eq_map]
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact Finset.mem_union_left _ he
  · obtain ⟨d,hd,rfl⟩ := Finset.mem_map.mp he
    exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨d,hKL hd,rfl⟩)

/-- On the same raw observation, restoring the sample's union restriction
only deletes original open bonds. -/
theorem sourceMarkedRawCentralRestoration_restriction_subset (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A B : Configuration (rectangleGraph a w h))
    (hB : B ∈ revealRecordEvent (sourceMarkedRawReveal a w h u v) A) :
    sourceMarkedRawCentralRestoration a w h u v A (sourceMarkedRawCentralRestriction a w h u v A B) ⊆ B := by
  apply Finset.union_subset
  · have hb : B ∩ sourceMarkedRawReveal a w h u v A = A ∩ sourceMarkedRawReveal a w h u v A := hB.2
    change A ∩ sourceMarkedRawReveal a w h u v A ⊆ B
    rw [← hb]
    exact Finset.inter_subset_left
  · exact embeddedConfigurationEmbedding_restriction_subset _ _ _ _ B

end
end PottsContinuity.Thm3.Prop4
