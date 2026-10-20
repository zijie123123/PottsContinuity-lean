-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverFaceSetPivots.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceSetEdgeCount
public import PottsContinuity.FKC.Medial.ParafermionicCoverFacePivotGeometry
public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceBoundaryGraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC

/-- The distinct actual top-pivot edges attached to a selected set of actual
retained lifted faces. -/
noncomputable def parafermionicCoverFiniteFaceSetPivots {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    Finset (Sym2 (ParafermionicCoverBoxVertex n)) :=
  S.image (parafermionicCoverFiniteFaceTopPivot n)

theorem parafermionicCoverFiniteFaceSetPivots_card {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    (parafermionicCoverFiniteFaceSetPivots S).card = S.card := by
  classical
  unfold parafermionicCoverFiniteFaceSetPivots
  exact Finset.card_image_of_injective _ (parafermionicCoverFiniteFaceTopPivot_injective n)

theorem parafermionicCoverFiniteFaceSetPivots_subset_edgeSupport {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    parafermionicCoverFiniteFaceSetPivots S ⊆
      parafermionicCoverFiniteFaceSetEdgeSupport S := by
  classical
  intro e he
  rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
  have htop := parafermionicCoverFiniteFaceTopEdgeBox_mem_boundaryGraph i.1 i.2
  have heq : parafermionicCoverFiniteFaceTopEdgeBox i.1 i.2 =
      parafermionicCoverFiniteFaceTopPivot n i := by
    simp [parafermionicCoverFiniteFaceTopEdgeBox,
      parafermionicCoverFiniteFaceTopPivot]
  have hmem : parafermionicCoverFiniteFaceTopPivot n i ∈
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet := by
    simpa [heq] using htop
  have hinc : i ∈ parafermionicCoverFiniteFaceIncidentFaces
      (parafermionicCoverFiniteFaceTopPivot n i) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
  have hselected : i ∈ parafermionicCoverFiniteFaceSelectedIncidentFaces S
      (parafermionicCoverFiniteFaceTopPivot n i) := by
    exact Finset.mem_filter.mpr ⟨hinc, hi⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, ⟨i, hselected⟩⟩

theorem parafermionicCoverFiniteFaceSetEdgeSupport_sdiff_pivots_card {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    (parafermionicCoverFiniteFaceSetEdgeSupport S \ parafermionicCoverFiniteFaceSetPivots S).card +
      S.card = (parafermionicCoverFiniteFaceSetEdgeSupport S).card := by
  have hsubset := parafermionicCoverFiniteFaceSetPivots_subset_edgeSupport S
  calc
    _ = (parafermionicCoverFiniteFaceSetEdgeSupport S \ parafermionicCoverFiniteFaceSetPivots S).card +
        (parafermionicCoverFiniteFaceSetPivots S).card := by
          rw [parafermionicCoverFiniteFaceSetPivots_card]
    _ = (parafermionicCoverFiniteFaceSetEdgeSupport S).card :=
      Finset.card_sdiff_add_card_eq_card hsubset

end PottsContinuity.FKC.Medial
