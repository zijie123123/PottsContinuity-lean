-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCandidateRemainingComponent.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateOffPathStar
public import PottsContinuity.FKC.FiniteFK.SlitBoxBottomCenterUnrevealed
public import PottsContinuity.FKC.FiniteFK.EdgeRestrictionReachableComponent
public import PottsContinuity.FKC.FiniteFK.SlitBoxReferenceRectangle
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open PottsContinuity.FKC.Medial

/-- The actual incident-edge cut revealed by one candidate's genuine polygon
filling. -/
noncomputable def slitBoxCandidateRemainingReveal
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u) :
    Configuration (slitBoxGraph n) :=
  slitBoxCellIncidentEdges n
    ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ)

/-- Vertices protected from the off-path, off-arc star argument: the retained
candidate path and the wired arc. -/
def slitBoxCandidatePathArcException
    (n : ℕ) (u : SlitBoxVertex n) (p : SlitBoxFirstHitBaseCandidates n u) :
    Set (SlitBoxVertex n) :=
  {v | v ∈ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support ∨
    v ∈ slitBoxWiredArc n}

/-- The actual filling reveal status is uniform on every slit-graph star
outside the candidate path and wired arc. -/
theorem slitBoxCandidateRemainingReveal_incident_status_uniform
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u)
    {v : SlitBoxVertex n} (hv : v ∉ slitBoxCandidatePathArcException n u p)
    (e f : (slitBoxGraph n).edgeSet)
    (he : v ∈ e.val) (hf : v ∈ f.val) :
    (e ∈ slitBoxCandidateRemainingReveal n hn u huY huX δ p) ↔
      (f ∈ slitBoxCandidateRemainingReveal n hn u huY huX δ p) := by
  have hv' : v ∉ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support ∧
      v ∉ slitBoxWiredArc n := by
    simpa [slitBoxCandidatePathArcException] using hv
  exact slitBoxCellIncidentEdges_all_or_none_at_candidate_off_path_arc
    n hn u huY huX δ p v hv'.1 hv'.2 e f he hf

/-- The bottom-center origin has an actual retained edge for the remaining
component when the candidate path avoids it. -/
theorem slitBoxCandidateRemainingReveal_origin_seed
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 < u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u)
    (hcenterPath : slitBoxBottomCenterVertex n ∉
      (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support) :
    ∃ e : (slitBoxGraph n).edgeSet,
      slitBoxBottomCenterVertex n ∈ e.val ∧
      e ∉ slitBoxCandidateRemainingReveal n hn u huY (le_of_lt huX) δ p := by
  simpa [slitBoxCandidateRemainingReveal] using
    slitBoxBottomCenter_has_unrevealed_upward_edge n hn u huY huX δ p hcenterPath

end PottsContinuity.FKC.FiniteFK
