-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxSplitCoverEnclosure.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxSplitCoverDomain
public import PottsContinuity.FKC.Medial.ParafermionicCoverGraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

noncomputable section

private theorem slitBoxSplitCover_base_bounds (n : ℕ) (v : SlitBoxVertex n) :
    -(n : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ (n : ℤ) ∧
      -(n : ℤ) ≤ v.val.2 ∧ v.val.2 ≤ (n : ℤ) := by
  have hv := v.property
  rw [mem_latticeRectangle] at hv
  omega

theorem slitBoxSplitCoverMap_mem_coverBox (n : ℕ) (hn : 1 ≤ n)
    (v : SlitBoxSplitCoverVertex n) :
    slitBoxSplitCoverMap n v ∈ parafermionicCoverBoxVertices n := by
  rw [parafermionicCoverBoxVertices_mem]
  cases v with
  | inl u =>
      have hb := slitBoxSplitCover_base_bounds n u.1
      have hn5 : 1 ≤ (n ^ 5 : ℤ) := by
        exact_mod_cast (Nat.one_le_pow 5 n (by omega))
      simp only [slitBoxSplitCoverMap]
      have hsheet : -((n ^ 5 : ℕ) : ℤ) ≤ (slitBoxInteriorCoverLift n u).2 ∧
          (slitBoxInteriorCoverLift n u).2 ≤ (n ^ 5 : ℤ) := by
        simp [slitBoxInteriorCoverLift]
        split_ifs <;> norm_num; omega
      exact ⟨by simpa [slitBoxInteriorCoverLift] using hb.1,
        by simpa [slitBoxInteriorCoverLift] using hb.2.1,
        by simpa [slitBoxInteriorCoverLift] using hb.2.2.1,
        by simpa [slitBoxInteriorCoverLift] using hb.2.2.2,
        by simpa [Nat.cast_pow] using hsheet.1,
        by simpa [Nat.cast_pow] using hsheet.2⟩
  | inr a =>
      have hb := slitBoxSplitCover_base_bounds n a.1.1
      have hn5 : 1 ≤ (n ^ 5 : ℤ) := by
        exact_mod_cast (Nat.one_le_pow 5 n (by omega))
      have hsheet : -((n ^ 5 : ℕ) : ℤ) ≤ (if a.2 then (1 : ℤ) else 0) ∧
          (if a.2 then (1 : ℤ) else 0) ≤ (n ^ 5 : ℤ) := by
        cases a.2
        · simp
        · simp
          omega
      simp only [slitBoxSplitCoverMap]
      exact ⟨by simpa using hb.1, by simpa using hb.2.1,
        by simpa using hb.2.2.1, by simpa using hb.2.2.2,
        by simpa [Nat.cast_pow] using hsheet.1,
        by simpa [Nat.cast_pow] using hsheet.2⟩

/-- The finite split carrier embeds into the vertex set of the actual cover
box, with no truncation of any represented vertex. -/
def slitBoxSplitCoverEmbedding (n : ℕ) (hn : 1 ≤ n) :
    SlitBoxSplitCoverVertex n ↪ ParafermionicCoverBoxVertex n where
  toFun v := ⟨slitBoxSplitCoverMap n v, slitBoxSplitCoverMap_mem_coverBox n hn v⟩
  inj' := by
    intro u v h
    apply slitBoxSplitCoverMap_injective n
    exact congrArg Subtype.val h

@[simp] theorem slitBoxSplitCoverEmbedding_val (n : ℕ) (hn : 1 ≤ n)
    (v : SlitBoxSplitCoverVertex n) :
    (slitBoxSplitCoverEmbedding n hn v).val = slitBoxSplitCoverMap n v := rfl

/-- A cover-box neighbor of an interior lift whose base lies off the wired arc
is itself the unique interior lift of its projected slit-box vertex. -/
theorem slitBoxSplitCover_interior_neighbor_enclosed
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxSplitInterior n)
    (v : ParafermionicCoverBoxVertex n)
    (hadj : (parafermionicCoverBoxGraph n).Adj
      (slitBoxSplitCoverEmbedding n hn (Sum.inl u)) v)
    (hbase : ¬ (v.val.1.1 = 0 ∧ 0 ≤ v.val.1.2 ∧ v.val.1.2 ≤ n)) :
    ∃ w : SlitBoxSplitInterior n,
      slitBoxSplitCoverEmbedding n hn (Sum.inl w) = v := by
  have hvbox : v.val.1 ∈
      latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n) := by
    have hv := (parafermionicCoverBoxVertices_mem n v.val).mp v.property
    rw [mem_latticeRectangle]
    constructor <;> constructor <;> omega
  have hvout : ¬ (v.val.1.1 = 0 ∧ 0 ≤ v.val.1.2 ∧ v.val.1.2 ≤ n) := by
    exact hbase
  have hcover : parafermionicCoverGraph.Adj
      (slitBoxInteriorCoverLift n u) v.val := by
    have h := hadj
    rw [parafermionicCoverBoxGraph, SimpleGraph.induce_adj] at h
    simpa [slitBoxSplitCoverEmbedding, slitBoxSplitCoverMap] using h
  have hclosed := slitBoxInteriorCoverLift_neighbor_closed n u v.val hvbox hvout hcover
  let w : SlitBoxSplitInterior n :=
    ⟨⟨v.val.1, hvbox⟩,
      fun hmem => hbase ((mem_slitBoxWiredArc_iff n ⟨v.val.1, hvbox⟩).mp hmem)⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  change slitBoxInteriorCoverLift n w = v.val
  exact hclosed.symm

end
end PottsContinuity.FKC.FiniteFK
