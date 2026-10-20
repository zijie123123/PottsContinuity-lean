module

public import PottsContinuity.FKC.FiniteFK.FirstClosedBlockScan
public import Mathlib.Data.List.Sort

/-! # Tested edges precede the actual first successful cut -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open FKC.FiniteFK

variable {E : Type*} [DecidableEq E]

/-- Literal membership in the union of the listed edge blocks. -/
theorem mem_firstClosedBlockUnion (D : ℕ → Finset E) (js : List ℕ) (e : E) :
    e ∈ firstClosedBlockUnion D js ↔ ∃ j ∈ js, e ∈ D j := by
  induction js with
  | nil => simp [firstClosedBlockUnion]
  | cons j js ih => simp [firstClosedBlockUnion,ih]

/-- A successful increasing-index scan tests only cuts up to its first hit.
This follows from the proved algorithm, without an extra selector premise. -/
theorem firstClosedBlockScan_tested_index_le (D : ℕ → Finset E) (A : Finset E)
    (K i : ℕ) (hi : (firstClosedBlockScan D A (List.range K)).2 = some i)
    (e : E) (he : e ∈ (firstClosedBlockScan D A (List.range K)).1) :
    ∃ j : ℕ, j ≤ i ∧ e ∈ D j := by
  obtain ⟨pre,post,hlist,_,_,htested⟩ := firstClosedBlockScan_hit_prefix D A (List.range K) i hi
  rw [htested] at he
  obtain ⟨j,hj,heD⟩ := (mem_firstClosedBlockUnion D _ e).mp he
  have hsort : (List.range K).Pairwise (fun a b => a < b) := List.pairwise_lt_range
  rw [hlist] at hsort
  have hcross := (List.pairwise_append.mp hsort).2.2
  refine ⟨j,?_,heD⟩
  simp only [List.mem_append,List.mem_singleton] at hj
  rcases hj with hj | rfl
  · exact (hcross j hj i (List.mem_cons_self)).le
  · exact le_rfl

end PottsContinuity.Thm3.Prop4
