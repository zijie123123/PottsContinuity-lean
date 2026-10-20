-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCandidateEdgeSupport.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCellIncidentEdges
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

/-- The finite configuration support of a candidate's original retained
slit-graph path. Canonical-return edges are not included. -/
noncomputable def slitBoxCandidateOriginalPathEdgeSupport
    (n : ℕ) (u : SlitBoxVertex n) (p : SlitBoxFirstHitBaseCandidates n u) :
    Configuration (slitBoxGraph n) := by
  classical
  exact (Finset.univ.filter fun e : (slitBoxGraph n).edgeSet =>
    e.val ∈ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).edges)

/-- Membership in the actual support means precisely that the underlying
slit-graph edge is traversed by the retained original candidate path. -/
theorem mem_slitBoxCandidateOriginalPathEdgeSupport_iff
    (n : ℕ) (u : SlitBoxVertex n) (p : SlitBoxFirstHitBaseCandidates n u)
    (e : (slitBoxGraph n).edgeSet) :
    e ∈ slitBoxCandidateOriginalPathEdgeSupport n u p ↔
      e.val ∈ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).edges := by
  classical
  simp [slitBoxCandidateOriginalPathEdgeSupport]

/-- The candidate's support is open in a configuration exactly when every
actual edge of its original ordered path belongs to that configuration. -/
theorem slitBoxCandidateOriginalPathEdgeSupport_subset_iff
    (n : ℕ) (u : SlitBoxVertex n) (p : SlitBoxFirstHitBaseCandidates n u)
    (A : Configuration (slitBoxGraph n)) :
    slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ A ↔
      ∀ e : (slitBoxGraph n).edgeSet,
        e.val ∈ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).edges → e ∈ A := by
  constructor
  · intro h e he
    exact h ((mem_slitBoxCandidateOriginalPathEdgeSupport_iff n u p e).2 he)
  · intro h e he
    exact h e ((mem_slitBoxCandidateOriginalPathEdgeSupport_iff n u p e).mp he)

/-- If candidate `r`'s actual polygon filling is contained in candidate `p`'s,
then every original path edge of `r` touches a cell in `p`'s filling. -/
theorem slitBoxCandidateOriginalPathEdgeSupport_subset_cellIncidentEdges_of_filling_subset
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p r : SlitBoxFirstHitBaseCandidates n u)
    (hfill : (slitBoxFirstHitCandidatePolygon n hn u huY huX r).interiorCellBases δ ⊆
      (slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ) :
    slitBoxCandidateOriginalPathEdgeSupport n u r ⊆
      slitBoxCellIncidentEdges n
        ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ) := by
  intro e he
  have hePath := (mem_slitBoxCandidateOriginalPathEdgeSupport_iff n u r e).mp he
  exact slitBoxCandidatePathEdges_subset_cellIncidentEdges_of_filling_subset
    n hn u huY huX δ r
    ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ)
    hfill e hePath

/-- In particular, every candidate's own original path support is revealed by
the incident-edge set of its own actual filling. -/
theorem slitBoxCandidateOriginalPathEdgeSupport_subset_selfCellIncidentEdges
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u) :
    slitBoxCandidateOriginalPathEdgeSupport n u p ⊆
      slitBoxCellIncidentEdges n
        ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ) := by
  exact slitBoxCandidateOriginalPathEdgeSupport_subset_cellIncidentEdges_of_filling_subset
    n hn u huY huX δ p p Finset.Subset.rfl

end PottsContinuity.FKC.FiniteFK
