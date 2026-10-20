-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxLeastCandidateStability.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.FiniteEnvelopeRevealConsistency
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateEdgeSupport
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateFillingInjective
public import PottsContinuity.FKC.FiniteFK.SlitBoxOpenEnvelope
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- An actual least open candidate remains open and least after a configuration
change agreeing on its actual filling's incident-edge cut. No openness is
assumed for the competing candidates in the new configuration. -/
theorem slitBoxLeastOpenCandidate_stable_under_reveal_agreement
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u)
    (A B : Configuration (slitBoxGraph n))
    (hpA : slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ A)
    (hleastA : ∀ q : SlitBoxFirstHitBaseCandidates n u,
      slitBoxCandidateOriginalPathEdgeSupport n u q ⊆ A →
      (slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ ⊆
        (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ)
    (hagree : B ∩ slitBoxCellIncidentEdges n
        ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ) =
      A ∩ slitBoxCellIncidentEdges n
        ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ)) :
    slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ B ∧
      (∀ q : SlitBoxFirstHitBaseCandidates n u,
        slitBoxCandidateOriginalPathEdgeSupport n u q ⊆ B →
        (slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ ⊆
          (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ) ∧
      (∀ q : SlitBoxFirstHitBaseCandidates n u,
        slitBoxCandidateOriginalPathEdgeSupport n u q ⊆ B →
        (∀ r : SlitBoxFirstHitBaseCandidates n u,
          slitBoxCandidateOriginalPathEdgeSupport n u r ⊆ B →
          (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ ⊆
            (slitBoxFirstHitCandidatePolygon n hn u huY huX r).interiorCellBases δ) →
        q = p) := by
  classical
  let fill : SlitBoxFirstHitBaseCandidates n u → Finset LatticeVertex :=
    slitBoxFirstHitCandidateInteriorCells n hn u huY huX δ
  let supp : SlitBoxFirstHitBaseCandidates n u → Configuration (slitBoxGraph n) :=
    slitBoxCandidateOriginalPathEdgeSupport n u
  let cut : SlitBoxFirstHitBaseCandidates n u → Configuration (slitBoxGraph n) :=
    fun q => slitBoxCellIncidentEdges n (fill q)
  have hcovered : ∀ r q, fill r ⊆ fill q → supp r ⊆ cut q := by
    intro r q hrq
    change (slitBoxFirstHitCandidatePolygon n hn u huY huX r).interiorCellBases δ ⊆
      (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ at hrq
    exact slitBoxCandidateOriginalPathEdgeSupport_subset_cellIncidentEdges_of_filling_subset
      n hn u huY huX δ q r hrq
  have hcommon : ∀ C : Configuration (slitBoxGraph n),
      ∀ q r, supp q ⊆ C → supp r ⊆ C →
        ∃ t, supp t ⊆ C ∧ fill t ⊆ fill q ∩ fill r := by
    intro C q r hq hr
    obtain ⟨t, htFill, htSupport, htOpen⟩ :=
      slitBoxFirstHitCandidate_exists_open_envelope
        n hn u huY huX δ q r C (by simpa [supp] using hq) (by simpa [supp] using hr)
    exact ⟨t, by simpa [supp] using htOpen,
      by simpa [fill, slitBoxFirstHitCandidateInteriorCells] using htFill⟩
  have hagree' : B ∩ cut p = A ∩ cut p := by
    simpa [cut, fill, slitBoxFirstHitCandidateInteriorCells] using hagree
  have hpA' : supp p ⊆ A := by simpa [supp] using hpA
  have hleastA' : ∀ q, supp q ⊆ A → fill p ⊆ fill q := by
    intro q hq
    exact hleastA q (by simpa [supp] using hq)
  have hstable := fill_least_stable_under_reveal_agreement
    fill supp cut hcovered hcommon A B p hpA' hleastA' hagree'
  have hinj : Function.Injective fill := by
    intro q r hqr
    exact slitBoxFirstHitCandidateInteriorCells_injective n hn u huY huX δ
      (by simpa [fill] using hqr)
  refine ⟨by simpa [supp] using hstable.1, ?_, ?_⟩
  · intro q hqB
    exact hstable.2 q (by simpa [supp] using hqB)
  · intro q hqB hqLeast
    apply hinj
    apply Finset.Subset.antisymm
    · exact hqLeast p (by simpa [supp] using hstable.1)
    · exact hstable.2 q (by simpa [supp] using hqB)

end PottsContinuity.FKC.FiniteFK

