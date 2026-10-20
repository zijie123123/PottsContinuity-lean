-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxLeastCandidateReveal.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxLeastOpenCandidate
public import PottsContinuity.FKC.FiniteFK.SlitBoxLeastCandidateStability
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateEdgeSupport
public import PottsContinuity.FKC.FiniteFK.SlitBoxOpenCandidateExistence
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- The unique least open candidate, defined only when the actual wired-arc
connection event holds. -/
noncomputable def slitBoxLeastOpenCandidateOnEvent
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (A : Configuration (slitBoxGraph n))
    (hconn : A ∈ slitBoxWiredArcConnectionEvent n u) :
    SlitBoxFirstHitBaseCandidates n u :=
  Classical.choose
    (slitBoxWiredArcConnectionEvent_existsUnique_least_open_candidate
      n hn u huY huX δ A hconn).exists

/-- The named full characterization of the selected actual candidate. -/
theorem slitBoxLeastOpenCandidateOnEvent_characterization
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (A : Configuration (slitBoxGraph n))
    (hconn : A ∈ slitBoxWiredArcConnectionEvent n u) :
    slitBoxCandidateOriginalPathEdgeSupport n u
        (slitBoxLeastOpenCandidateOnEvent n hn u huY huX δ A hconn) ⊆ A ∧
      (∀ q : SlitBoxFirstHitBaseCandidates n u,
        slitBoxCandidateOriginalPathEdgeSupport n u q ⊆ A →
        (slitBoxFirstHitCandidatePolygon n hn u huY huX
          (slitBoxLeastOpenCandidateOnEvent n hn u huY huX δ A hconn)).interiorCellBases δ ⊆
          (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ) ∧
      (∀ q : SlitBoxFirstHitBaseCandidates n u,
        slitBoxCandidateOriginalPathEdgeSupport n u q ⊆ A →
        (∀ r : SlitBoxFirstHitBaseCandidates n u,
          slitBoxCandidateOriginalPathEdgeSupport n u r ⊆ A →
          (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ ⊆
            (slitBoxFirstHitCandidatePolygon n hn u huY huX r).interiorCellBases δ) →
        q = slitBoxLeastOpenCandidateOnEvent n hn u huY huX δ A hconn) := by
  have hex := slitBoxWiredArcConnectionEvent_existsUnique_least_open_candidate
    n hn u huY huX δ A hconn
  have hspec := Classical.choose_spec hex.exists
  refine ⟨hspec.1, hspec.2, ?_⟩
  intro q hq hleast
  exact hex.unique ⟨hq, hleast⟩ hspec

/-- The actual edge cut revealed by the selected least candidate on the hit
branch. -/
noncomputable def slitBoxLeastCandidateActualRevealCut
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (A : Configuration (slitBoxGraph n))
    (hconn : A ∈ slitBoxWiredArcConnectionEvent n u) :
    Configuration (slitBoxGraph n) :=
  slitBoxCellIncidentEdges n
    ((slitBoxFirstHitCandidatePolygon n hn u huY huX
      (slitBoxLeastOpenCandidateOnEvent n hn u huY huX δ A hconn)).interiorCellBases δ)

/-- Total finite reveal map: on actual connection it reveals precisely the
selected candidate's incident-cell cut, and otherwise it reveals every
original slit-graph edge. -/
noncomputable def slitBoxLeastCandidateReveal
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (A : Configuration (slitBoxGraph n)) :
    Configuration (slitBoxGraph n) := by
  classical
  letI : Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _
  exact if hconn : A ∈ slitBoxWiredArcConnectionEvent n u then
    slitBoxLeastCandidateActualRevealCut n hn u huY huX δ A hconn
  else Finset.univ

theorem slitBoxLeastCandidateReveal_eq_actual_cut_of_hit
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (A : Configuration (slitBoxGraph n))
    (hconn : A ∈ slitBoxWiredArcConnectionEvent n u) :
    slitBoxLeastCandidateReveal n hn u huY huX δ A =
      slitBoxLeastCandidateActualRevealCut n hn u huY huX δ A hconn := by
  simp [slitBoxLeastCandidateReveal, hconn]

/-- On failure, the reveal set is exactly the full finite carrier of original
slit-graph edges. -/
theorem slitBoxLeastCandidateReveal_eq_univ_of_no_hit
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (A : Configuration (slitBoxGraph n))
    (hno : A ∉ slitBoxWiredArcConnectionEvent n u) :
    slitBoxLeastCandidateReveal n hn u huY huX δ A = (by
      classical
      letI : Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _
      exact (Finset.univ : Configuration (slitBoxGraph n))) := by
  classical
  let : Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _
  simp [slitBoxLeastCandidateReveal, hno]

/-- On the hit branch, the selected actual original path is contained in the
edge cut that is revealed. -/
theorem slitBoxLeastCandidateReveal_support_subset_of_hit
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (A : Configuration (slitBoxGraph n))
    (hconn : A ∈ slitBoxWiredArcConnectionEvent n u) :
    slitBoxCandidateOriginalPathEdgeSupport n u
      (slitBoxLeastOpenCandidateOnEvent n hn u huY huX δ A hconn) ⊆
    slitBoxLeastCandidateReveal n hn u huY huX δ A := by
  rw [slitBoxLeastCandidateReveal_eq_actual_cut_of_hit n hn u huY huX δ A hconn]
  exact slitBoxCandidateOriginalPathEdgeSupport_subset_selfCellIncidentEdges
    n hn u huY huX δ (slitBoxLeastOpenCandidateOnEvent n hn u huY huX δ A hconn)

/-- Agreement on the revealed states makes the complete total reveal map
constant between the two actual configurations. -/
theorem slitBoxLeastCandidateReveal_stopping_consistency
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (A B : Configuration (slitBoxGraph n))
    (hagree : B ∩ slitBoxLeastCandidateReveal n hn u huY huX δ A =
      A ∩ slitBoxLeastCandidateReveal n hn u huY huX δ A) :
    slitBoxLeastCandidateReveal n hn u huY huX δ B =
      slitBoxLeastCandidateReveal n hn u huY huX δ A := by
  classical
  by_cases hA : A ∈ slitBoxWiredArcConnectionEvent n u
  · let p := slitBoxLeastOpenCandidateOnEvent n hn u huY huX δ A hA
    have hpchar := slitBoxLeastOpenCandidateOnEvent_characterization
      n hn u huY huX δ A hA
    rw [slitBoxLeastCandidateReveal_eq_actual_cut_of_hit
      n hn u huY huX δ A hA] at hagree
    have hagreeCut : B ∩
        slitBoxCellIncidentEdges n
          ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ) =
      A ∩ slitBoxCellIncidentEdges n
          ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ) := by
      simpa [p, slitBoxLeastCandidateActualRevealCut] using hagree
    have hstable := slitBoxLeastOpenCandidate_stable_under_reveal_agreement
      n hn u huY huX δ p A B hpchar.1 hpchar.2.1 hagreeCut
    have hB : B ∈ slitBoxWiredArcConnectionEvent n u := by
      obtain ⟨t, ht, hconn⟩ :=
        (slitBoxFirstHitCandidate_exists_open_iff_actualConnected n u B).mp
          ⟨p, hstable.1⟩
      exact ⟨t, ht, hconn⟩
    let q := slitBoxLeastOpenCandidateOnEvent n hn u huY huX δ B hB
    have hqchar := slitBoxLeastOpenCandidateOnEvent_characterization
      n hn u huY huX δ B hB
    have hqp : q = p := hstable.2.2 q hqchar.1 hqchar.2.1
    have hcutEq :
        slitBoxCellIncidentEdges n
          ((slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ) =
        slitBoxCellIncidentEdges n
          ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ) := by
      rw [hqp]
    rw [slitBoxLeastCandidateReveal_eq_actual_cut_of_hit n hn u huY huX δ B hB,
      slitBoxLeastCandidateReveal_eq_actual_cut_of_hit n hn u huY huX δ A hA]
    exact hcutEq
  · have hAreveal := slitBoxLeastCandidateReveal_eq_univ_of_no_hit
      n hn u huY huX δ A hA
    rw [hAreveal] at hagree
    have hBA : B = A := by
      ext e
      have h := congrArg (fun C : Configuration (slitBoxGraph n) => e ∈ C) hagree
      simpa using h
    have hB : B ∉ slitBoxWiredArcConnectionEvent n u := by
      simpa [hBA] using hA
    rw [slitBoxLeastCandidateReveal_eq_univ_of_no_hit n hn u huY huX δ B hB,
      slitBoxLeastCandidateReveal_eq_univ_of_no_hit n hn u huY huX δ A hA]

end PottsContinuity.FKC.FiniteFK

