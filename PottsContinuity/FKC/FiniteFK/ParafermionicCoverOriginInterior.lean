-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverOriginInterior.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverExtremalSheets
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverSideBoundary
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC

/-- The actual neighbors of the cover-box origin are the four base neighbors on sheet zero. -/
theorem parafermionicCoverBoxOrigin_neighbor_cases (n : ℕ)
    {w : ParafermionicCoverVertex}
    (hadj : parafermionicCoverGraph.Adj (FiniteFK.parafermionicCoverBoxOrigin n).1 w) :
    w = ((0,1),0) ∨ w = ((0,-1),0) ∨ w = ((1,0),0) ∨ w = ((-1,0),0) := by
  have hbase : parafermionicCoverGraph.Adj ((0,0),0) w := by
    simpa using hadj
  rcases (parafermionicCoverGraph_adj_iff_cases ((0,0),0) w).mp hbase with
    h | h | h | h | h | h | h | h
  all_goals rcases w with ⟨⟨x,y⟩,k⟩
  all_goals simp_all <;> omega

/-- For positive box radius, every actual whole-cover neighbor of the origin is retained. -/
theorem parafermionicCoverBoxOrigin_neighbor_mem_box (n : ℕ) (hn : 1 ≤ n)
    {w : ParafermionicCoverVertex}
    (hadj : parafermionicCoverGraph.Adj (FiniteFK.parafermionicCoverBoxOrigin n).1 w) :
    w ∈ parafermionicCoverBoxVertices n := by
  rcases parafermionicCoverBoxOrigin_neighbor_cases n hadj with h | h | h | h
  all_goals rw [parafermionicCoverBoxVertices_mem]
  all_goals rw [h]
  all_goals norm_num
  have hnZ : 1 ≤ (n : ℤ) := by exact_mod_cast hn
  all_goals omega

end PottsContinuity.FKC
