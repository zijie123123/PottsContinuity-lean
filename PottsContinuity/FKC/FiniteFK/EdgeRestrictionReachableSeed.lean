-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/EdgeRestrictionReachableSeed.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.EdgeRestriction
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

/-- A vertex reachable from an origin in the actual edge-restricted graph has
an incident original edge outside the revealed configuration, provided the
origin has such a seed edge. The non-origin case uses the last edge of an
actual reachable walk. -/
theorem edgeRestriction_reachable_has_unrevealed_incident_edge
    {V : Type*} (G : SimpleGraph V) (R : Configuration G) (o v : V)
    (hreach : (edgeRestriction G R).Reachable o v)
    (horigin : ∃ e : G.edgeSet, o ∈ e.val ∧ e ∉ R) :
    ∃ e : G.edgeSet, v ∈ e.val ∧ e ∉ R := by
  classical
  by_cases hvo : v = o
  · subst v
    exact horigin
  · obtain ⟨path⟩ := hreach
    have hnonil : ¬ path.Nil := SimpleGraph.Walk.not_nil_of_ne (by
      intro heq
      exact hvo heq.symm)
    let eH : (edgeRestriction G R).edgeSet :=
      ⟨s(path.penultimate, v),
        (edgeRestriction G R).mem_edgeSet.mpr (path.adj_penultimate hnonil)⟩
    have heHmem : eH.val ∈ (edgeRestriction G R).edgeSet := eH.property
    have heNotOpen : eH.val ∉ openEdges G R := by
      have hsets := congrArg (fun E : Set (Sym2 V) => eH.val ∈ E)
        (edgeRestriction_edgeSet G R)
      have hmem : eH.val ∈ G.edgeSet \ openEdges G R := hsets.mp heHmem
      exact hmem.2
    let eG : G.edgeSet :=
      ⟨eH.val, edgeRestriction_le G R (path.adj_penultimate hnonil)⟩
    have heGnot : eG ∉ R := by
      intro hR
      exact heNotOpen ((coe_mem_openEdges_iff G R eG).mpr hR)
    refine ⟨eG, ?_, heGnot⟩
    have heqVal : eG.val = eH.val := rfl
    rw [heqVal]
    exact (Sym2.mem_iff').2 (Or.inr rfl)

end PottsContinuity.FKC.FiniteFK
