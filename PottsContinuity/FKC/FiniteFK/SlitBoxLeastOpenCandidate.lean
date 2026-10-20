-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxLeastOpenCandidate.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.FiniteEnvelopeLeast
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateFillingInjective
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateEdgeSupport
public import PottsContinuity.FKC.FiniteFK.SlitBoxOpenCandidateExistence
public import PottsContinuity.FKC.FiniteFK.SlitBoxOpenEnvelope
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- On the actual wired-arc connection event, there is a unique open
first-hit candidate whose actual polygon filling is inclusion-least among
all open first-hit candidates. -/
theorem slitBoxWiredArcConnectionEvent_existsUnique_least_open_candidate
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (A : Configuration (slitBoxGraph n))
    (hconn : A ∈ slitBoxWiredArcConnectionEvent n u) :
    ∃! p : SlitBoxFirstHitBaseCandidates n u,
      slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ A ∧
      ∀ q : SlitBoxFirstHitBaseCandidates n u,
        slitBoxCandidateOriginalPathEdgeSupport n u q ⊆ A →
        (slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ ⊆
          (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ := by
  classical
  let : Fintype (SlitBoxVertex n) := Fintype.ofFinite _
  let : DecidableEq (SlitBoxVertex n) := Classical.decEq _
  let : DecidableRel (slitBoxGraph n).Adj := Classical.decRel _
  let : Fintype (FirstHitSimplePathCarrier (slitBoxGraph n) u
      (slitBoxWiredArc n : Set (SlitBoxVertex n))) :=
    firstHitSimplePathCarrier_fintype u _
  let : Fintype (SlitBoxFirstHitBaseCandidates n u) := inferInstance
  let : DecidableEq (SlitBoxFirstHitBaseCandidates n u) := Classical.decEq _
  let S : Set (SlitBoxFirstHitBaseCandidates n u) :=
    {p | slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ A}
  have hS : S.Nonempty := by
    change ∃ t ∈ slitBoxWiredArc n,
      ActualConnected (slitBoxGraph n) A u t at hconn
    obtain ⟨t, ht, hactual⟩ := hconn
    obtain ⟨p, hp⟩ :=
      (slitBoxFirstHitCandidate_exists_open_iff_actualConnected n u A).2
        ⟨t, ht, hactual⟩
    exact ⟨p, hp⟩
  have hinj : Function.Injective
      (slitBoxFirstHitCandidateInteriorCells n hn u huY huX δ) :=
    slitBoxFirstHitCandidateInteriorCells_injective n hn u huY huX δ
  have hcommon : ∀ p, p ∈ S → ∀ q, q ∈ S →
      ∃ r, r ∈ S ∧
        slitBoxFirstHitCandidateInteriorCells n hn u huY huX δ r ⊆
          slitBoxFirstHitCandidateInteriorCells n hn u huY huX δ p ∩
            slitBoxFirstHitCandidateInteriorCells n hn u huY huX δ q := by
    intro p hp q hq
    obtain ⟨r, hrFill, hrSupport, hrOpen⟩ :=
      slitBoxFirstHitCandidate_exists_open_envelope
        n hn u huY huX δ p q A hp hq
    refine ⟨r, hrOpen, ?_⟩
    simpa [slitBoxFirstHitCandidateInteriorCells] using hrFill
  have hleast := existsUnique_least_fill_of_pairwise_common_subfill
    (slitBoxFirstHitCandidateInteriorCells n hn u huY huX δ) hinj S hS hcommon
  simpa [S, slitBoxFirstHitCandidateInteriorCells,
    slitBoxFirstHitCandidatePolygon] using hleast

end PottsContinuity.FKC.FiniteFK

