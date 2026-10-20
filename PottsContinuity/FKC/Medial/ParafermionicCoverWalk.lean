-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverWalk.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverGraph
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

@[expose] public section

namespace PottsContinuity.FKC

 theorem parafermionicCover_adj_sheet_abs_le_one {u v : ParafermionicCoverVertex}
    (h : parafermionicCoverGraph.Adj u v) : |v.2 - u.2| ≤ 1 := by
  rw [parafermionicCover_sheetShift_of_adj h]
  unfold parafermionicCoverSheetShift
  split_ifs <;> norm_num

 theorem parafermionicCoverWalk_intermediate_sheet {u v : ParafermionicCoverVertex}
    (w : parafermionicCoverGraph.Walk u v) (m : ℤ)
    (hm : (u.2 ≤ m ∧ m ≤ v.2) ∨ (v.2 ≤ m ∧ m ≤ u.2)) :
    ∃ z ∈ w.support, z.2 = m := by
  induction w generalizing m with
  | nil =>
      rename_i x
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton]
      exact ⟨x, rfl, by rcases hm with h | h <;> omega⟩
  | @cons u v w h p ih =>
      rw [SimpleGraph.Walk.support_cons]
      by_cases htail : (v.2 ≤ m ∧ m ≤ w.2) ∨ (w.2 ≤ m ∧ m ≤ v.2)
      · obtain ⟨z, hz, hzm⟩ := ih m htail
        exact ⟨z, List.mem_cons_of_mem _ hz, hzm⟩
      · have hstep := parafermionicCover_adj_sheet_abs_le_one h
        rw [abs_le] at hstep
        have hmuv : (u.2 ≤ m ∧ m ≤ v.2) ∨ (v.2 ≤ m ∧ m ≤ u.2) := by omega
        rcases hmuv with huv | hvu
        · have heq : m = u.2 ∨ m = v.2 := by omega
          rcases heq with heq | heq
          · exact ⟨u, List.mem_cons_self, heq.symm⟩
          · exact ⟨v, List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support p), heq.symm⟩
        · have heq : m = u.2 ∨ m = v.2 := by omega
          rcases heq with heq | heq
          · exact ⟨u, List.mem_cons_self, heq.symm⟩
          · exact ⟨v, List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support p), heq.symm⟩

/-- The literal vertex inclusion from the induced finite box graph into the cover graph. -/
def parafermionicCoverBoxInclusionHom (n : ℕ) :
    parafermionicCoverBoxGraph n →g parafermionicCoverGraph where
  toFun := Subtype.val
  map_rel' := by
    intro u v h
    exact h

end PottsContinuity.FKC
