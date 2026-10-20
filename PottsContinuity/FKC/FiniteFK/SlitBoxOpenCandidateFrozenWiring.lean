-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxOpenCandidateFrozenWiring.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxOpenCandidateVertexConnection
public import PottsContinuity.FKC.FiniteFK.DomainMarkov
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- The two retained path supports together with the wired arc. -/
def slitBoxCandidateWiredSupportSet
    (n : ℕ) (u : SlitBoxVertex n) (p : SlitBoxFirstHitBaseCandidates n u)
    (v : SlitBoxVertex n) (q : SlitBoxFirstHitBaseCandidates n v) :
    Set (SlitBoxVertex n) :=
  {x | x ∈ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support} ∪
    ({x | x ∈ (q.val.2 : (slitBoxGraph n).Walk v q.val.1).support} ∪
      (slitBoxWiredArc n : Set (SlitBoxVertex n)))

/-- In the actual frozen boundary partition, every vertex on a candidate's
original path or wired arc is connected to that candidate's actual endpoint.
Path vertices use actual open-edge connectivity in the frozen configuration;
arc vertices use only the boundary wiring. -/
theorem slitBoxOpenCandidate_vertex_frozenConnected_to_endpoint
    (n : ℕ) (u : SlitBoxVertex n) (p : SlitBoxFirstHitBaseCandidates n u)
    (K : Configuration (slitBoxGraph n))
    (hopen : slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ K)
    (x : SlitBoxVertex n)
    (hx : x ∈ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support ∨
      x ∈ slitBoxWiredArc n) :
    (frozenBoundary (slitBoxBoundary n) K).partition.r x p.val.1 := by
  rcases hx with hxPath | hxArc
  · have hconn := slitBoxCandidate_vertex_actualConnected_to_endpoint_of_open
      n u p K hopen x hxPath
    change (componentSetoid (slitBoxGraph n) (slitBoxBoundary n) K).r x p.val.1
    exact actualConnected_component (slitBoxGraph n) (slitBoxBoundary n) K hconn
  · change (componentSetoid (slitBoxGraph n) (slitBoxBoundary n) K).r x p.val.1
    apply boundary_component (slitBoxGraph n) (slitBoxBoundary n) K
    change (BoundaryCondition.wired (slitBoxWiredArc n : Set (SlitBoxVertex n))).partition.r
      x p.val.1
    exact (BoundaryCondition.wired_rel _ _ _).2
      (Or.inr ⟨hxArc, p.property.1⟩)

/-- The frozen actual partition dominates wiring of the two actual candidate
path supports together with their common wired arc. The candidates may start
at different vertices. -/
theorem slitBoxOpenCandidates_frozen_partition_dominates_wired_supports
    (n : ℕ) (u v : SlitBoxVertex n)
    (p : SlitBoxFirstHitBaseCandidates n u)
    (q : SlitBoxFirstHitBaseCandidates n v)
    (K : Configuration (slitBoxGraph n))
    (hpOpen : slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ K)
    (hqOpen : slitBoxCandidateOriginalPathEdgeSupport n v q ⊆ K) :
    (BoundaryCondition.wired (slitBoxCandidateWiredSupportSet n u p v q)).partition ≤
      (frozenBoundary (slitBoxBoundary n) K).partition := by
  let D : Setoid (SlitBoxVertex n) :=
    (frozenBoundary (slitBoxBoundary n) K).partition
  intro x y hxy
  have hwire := (BoundaryCondition.wired_rel _ _ _).mp hxy
  rcases hwire with hxy | ⟨hx, hy⟩
  · subst y
    exact D.iseqv.refl x
  · have hxToP : D.r x p.val.1 := by
      rcases hx with hxP | hxRest
      · exact slitBoxOpenCandidate_vertex_frozenConnected_to_endpoint
          n u p K hpOpen x (Or.inl hxP)
      · rcases hxRest with hxQ | hxArc
        · have hxToQ := slitBoxOpenCandidate_vertex_frozenConnected_to_endpoint
            n v q K hqOpen x (Or.inl hxQ)
          have hqToP : D.r q.val.1 p.val.1 := by
            change (componentSetoid (slitBoxGraph n) (slitBoxBoundary n) K).r
              q.val.1 p.val.1
            apply boundary_component (slitBoxGraph n) (slitBoxBoundary n) K
            change (BoundaryCondition.wired
              (slitBoxWiredArc n : Set (SlitBoxVertex n))).partition.r q.val.1 p.val.1
            exact (BoundaryCondition.wired_rel _ _ _).2
              (Or.inr ⟨q.property.1, p.property.1⟩)
          exact D.iseqv.trans hxToQ hqToP
        · change (componentSetoid (slitBoxGraph n) (slitBoxBoundary n) K).r
            x p.val.1
          apply boundary_component (slitBoxGraph n) (slitBoxBoundary n) K
          change (BoundaryCondition.wired
            (slitBoxWiredArc n : Set (SlitBoxVertex n))).partition.r x p.val.1
          exact (BoundaryCondition.wired_rel _ _ _).2
            (Or.inr ⟨hxArc, p.property.1⟩)
    have hyToP : D.r y p.val.1 := by
      rcases hy with hyP | hyRest
      · exact slitBoxOpenCandidate_vertex_frozenConnected_to_endpoint
          n u p K hpOpen y (Or.inl hyP)
      · rcases hyRest with hyQ | hyArc
        · have hyToQ := slitBoxOpenCandidate_vertex_frozenConnected_to_endpoint
            n v q K hqOpen y (Or.inl hyQ)
          have hqToP : D.r q.val.1 p.val.1 := by
            change (componentSetoid (slitBoxGraph n) (slitBoxBoundary n) K).r
              q.val.1 p.val.1
            apply boundary_component (slitBoxGraph n) (slitBoxBoundary n) K
            change (BoundaryCondition.wired
              (slitBoxWiredArc n : Set (SlitBoxVertex n))).partition.r q.val.1 p.val.1
            exact (BoundaryCondition.wired_rel _ _ _).2
              (Or.inr ⟨q.property.1, p.property.1⟩)
          exact D.iseqv.trans hyToQ hqToP
        · change (componentSetoid (slitBoxGraph n) (slitBoxBoundary n) K).r
            y p.val.1
          apply boundary_component (slitBoxGraph n) (slitBoxBoundary n) K
          change (BoundaryCondition.wired
            (slitBoxWiredArc n : Set (SlitBoxVertex n))).partition.r y p.val.1
          exact (BoundaryCondition.wired_rel _ _ _).2
            (Or.inr ⟨hyArc, p.property.1⟩)
    exact D.iseqv.trans hxToP (D.iseqv.symm hyToP)

end PottsContinuity.FKC.FiniteFK
