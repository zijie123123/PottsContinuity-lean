-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverFaceSetPivotRemoval.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceSetPivots
public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceUnionConnectivity
public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceChainUniqueness
public import PottsContinuity.FKC.Medial.ParafermionicCoverFacePivotBypass
public import PottsContinuity.FKC.Medial.FiniteTriangularPivotReachability
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC
open SimpleGraph

/-- The actual selected-face union graph after deleting precisely its selected
top-pivot edges, on the same original box-vertex carrier. -/
noncomputable def parafermionicCoverFiniteFaceSetWithoutPivotsGraph {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    SimpleGraph (ParafermionicCoverBoxVertex n) :=
  (parafermionicCoverFiniteFaceUnionGraph S).deleteEdges
    (parafermionicCoverFiniteFaceSetPivots S : Set _)

theorem parafermionicCoverFiniteFaceSetWithoutPivotsGraph_reachable_eq
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    (parafermionicCoverFiniteFaceSetWithoutPivotsGraph S).Reachable =
      (parafermionicCoverFiniteFaceUnionGraph S).Reachable := by
  classical
  let I := {i : ParafermionicCoverFiniteFaceTopIndex n // i ∈ S}
  let U := parafermionicCoverFiniteFaceUnionGraph S
  let F : I → SimpleGraph (ParafermionicCoverBoxVertex n) :=
    fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1.1 i.1.2
  let p : I → Sym2 (ParafermionicCoverBoxVertex n) :=
    fun i => parafermionicCoverFiniteFaceTopPivot n i.1
  let rank : I → ℕ := fun i => parafermionicCoverFiniteFaceTopRank n i.1
  have hsub : ∀ i, F i ≤ U := by
    intro i v w hadj
    exact ⟨i.1, i.2, hadj⟩
  have htri : ∀ i j, p j ∈ (F i).edgeSet → j = i ∨ rank j < rank i := by
    intro i j hj
    have hclass := parafermionicCoverFiniteFacePivot_boundary_classification
      i.1 j.1 (by simpa [F, p] using hj)
    rcases hclass with hEq | hlt
    · exact Or.inl (Subtype.ext hEq)
    · exact Or.inr (by simpa [rank] using hlt)
  have halt : ∀ i,
      ((F i).deleteEdges {p i}).Reachable (p i).out.1 (p i).out.2 := by
    intro i
    simpa [F, p] using parafermionicCoverFiniteFaceTopPivot_bypass i.1
  have hrange : Set.range p =
      (parafermionicCoverFiniteFaceSetPivots S : Set (Sym2 (ParafermionicCoverBoxVertex n))) := by
    ext e
    simp only [Set.mem_range, Finset.mem_coe, parafermionicCoverFiniteFaceSetPivots,
      Finset.mem_image]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨i, hi, he⟩
      exact ⟨⟨i, hi⟩, he⟩
  have hreach := finiteTriangularPivotReachability U F p rank hsub htri halt
  simpa [parafermionicCoverFiniteFaceSetWithoutPivotsGraph, U, hrange] using hreach

end PottsContinuity.FKC.Medial
