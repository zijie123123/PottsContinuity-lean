-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedPrimalRayPath.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPrimalEdgeIntersections
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph

def parafermionicCoverRayProgress (d : Fin 4)
    (z : ParafermionicCoverVertex) : ℤ :=
  if d.val = 0 then z.1.1 else if d.val = 1 then z.1.2
  else if d.val = 2 then -z.1.1 else -z.1.2

private theorem parafermionicCoverRayProgress_neighbor
    (u : ParafermionicCoverVertex) (d : Fin 4) :
    parafermionicCoverRayProgress d (parafermionicCoverCompassNeighbor u d) =
      parafermionicCoverRayProgress d u + 1 := by
  fin_cases d <;> rcases u with ⟨⟨x,y⟩,k⟩ <;>
    simp [parafermionicCoverRayProgress, parafermionicCoverCompassNeighbor,
      parafermionicCoverCompassBaseNeighbor, parafermionicCoverNeighborLift,
      parafermionicCoverSheetShift] <;> omega

private theorem parafermionicCoverCompassWalk_progress_lower_bound
    {u v : ParafermionicCoverVertex}
    (p : parafermionicCoverGraph.Walk u v) (d : Fin 4)
    (hdir : parafermionicCoverWalkCompassDirections p = List.replicate p.length d)
    {z : ParafermionicCoverVertex} (hz : z ∈ p.support) :
    parafermionicCoverRayProgress d u ≤ parafermionicCoverRayProgress d z := by
  induction p with
  | nil =>
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst z
      exact le_rfl
  | @cons a b c hab tail ih =>
      simp only [parafermionicCoverWalkCompassDirections_cons,
        SimpleGraph.Walk.length_cons, List.replicate_succ] at hdir
      obtain ⟨hhead, htail⟩ := List.cons.inj hdir
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact le_rfl
      · have hnext := parafermionicCoverCompassDirection_neighbor a b hab
        rw [hhead] at hnext
        have hstep : parafermionicCoverRayProgress d b =
            parafermionicCoverRayProgress d a + 1 := by
          rw [← hnext]
          exact parafermionicCoverRayProgress_neighbor a d
        have htaille := ih htail hz
        omega

private theorem parafermionicCoverCompassWalk_support_nodup
    {u v : ParafermionicCoverVertex}
    (p : parafermionicCoverGraph.Walk u v) (d : Fin 4)
    (hdir : parafermionicCoverWalkCompassDirections p = List.replicate p.length d) :
    p.support.Nodup := by
  induction p with
  | nil => simp
  | @cons a b c hab tail ih =>
      simp only [parafermionicCoverWalkCompassDirections_cons,
        SimpleGraph.Walk.length_cons, List.replicate_succ] at hdir
      obtain ⟨hhead, htail⟩ := List.cons.inj hdir
      have hnext := parafermionicCoverCompassDirection_neighbor a b hab
      rw [hhead] at hnext
      have hstep : parafermionicCoverRayProgress d b =
          parafermionicCoverRayProgress d a + 1 := by
        rw [← hnext]
        exact parafermionicCoverRayProgress_neighbor a d
      have hnot : a ∉ tail.support := by
        intro ha
        have hle := parafermionicCoverCompassWalk_progress_lower_bound tail d htail ha
        omega
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons]
      exact ⟨hnot, ih htail⟩

/-- The actual nine-step refined primal edge walk has no repeated vertices. -/
theorem parafermionicCoverRefinedPrimalEdgeWalk_isPath
    (u : ParafermionicCoverVertex) (d : Fin 4) :
    (parafermionicCoverRefinedPrimalEdgeWalk u d).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  have hlen := parafermionicCoverRefinedPrimalEdgeWalk_length u d
  have hdir := parafermionicCoverRefinedPrimalEdgeWalk_compassDirections u d
  have hdir' : parafermionicCoverWalkCompassDirections
      (parafermionicCoverRefinedPrimalEdgeWalk u d) =
        List.replicate (parafermionicCoverRefinedPrimalEdgeWalk u d).length d := by
    rw [hlen]
    exact hdir
  exact parafermionicCoverCompassWalk_support_nodup
    (parafermionicCoverRefinedPrimalEdgeWalk u d) d hdir'

end PottsContinuity.FKC.Medial
