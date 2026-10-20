-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxSplitShiftedEmbedding.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxSplitCoverInteriorClosed
public import PottsContinuity.FKC.Medial.ParafermionicCoverGraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

noncomputable section

private theorem slitBoxInteriorCoverLift_neighbor_sheet_range
    (n : ℕ) (u : SlitBoxSplitInterior n) (z : ParafermionicCoverVertex)
    (hadj : parafermionicCoverGraph.Adj (slitBoxInteriorCoverLift n u) z) :
    z.2 = 0 ∨ z.2 = 1 := by
  have hcases := (parafermionicCoverGraph_adj_iff_cases _ _).mp hadj
  unfold parafermionicCoverAdjCases at hcases
  rcases hcases with h | h | h | h | h | h | h | h
  all_goals simp only [slitBoxInteriorCoverLift] at h
  all_goals split_ifs at h <;> omega

private theorem slitBoxSplitShiftedVertex_mem_coverBox
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ) (hlo : -((n ^ 5 : ℕ) : ℤ) ≤ k)
    (hhi : k + 1 ≤ ((n ^ 5 : ℕ) : ℤ)) (z : ParafermionicCoverVertex)
    (hbase : -(n : ℤ) ≤ z.1.1 ∧ z.1.1 ≤ n ∧
      -(n : ℤ) ≤ z.1.2 ∧ z.1.2 ≤ n)
    (hs : z.2 = 0 ∨ z.2 = 1) :
    parafermionicCoverSheetTranslate k z ∈ parafermionicCoverBoxVertices n := by
  rw [parafermionicCoverBoxVertices_mem]
  rcases hbase with ⟨hxl, hxu, hyl, hyu⟩
  rcases hs with hs | hs
  · simp only [parafermionicCoverSheetTranslate, hs]
    exact ⟨hxl, hxu, hyl, hyu, by omega, by omega⟩
  · have hn5 : 1 ≤ (n ^ 5 : ℤ) := by
      exact_mod_cast (Nat.one_le_pow 5 n (by omega))
    simp only [parafermionicCoverSheetTranslate, hs]
    exact ⟨hxl, hxu, hyl, hyu, by omega, by omega⟩

/-- The canonical split graph shifted by k sheets, embedded into the original
finite cover box whenever both canonical sheets k and k+1 fit. -/
def slitBoxSplitShiftedEmbedding (n : ℕ) (hn : 1 ≤ n) (k : ℤ)
    (hlo : -((n ^ 5 : ℕ) : ℤ) ≤ k)
    (hhi : k + 1 ≤ ((n ^ 5 : ℕ) : ℤ)) :
    SlitBoxSplitCoverVertex n ↪ ParafermionicCoverBoxVertex n where
  toFun v :=
    ⟨parafermionicCoverSheetTranslate k (slitBoxSplitCoverMap n v), by
      change parafermionicCoverSheetTranslate k (slitBoxSplitCoverMap n v) ∈
        parafermionicCoverBoxVertices n
      have hbase := (parafermionicCoverBoxVertices_mem n
        (slitBoxSplitCoverMap n v)).mp
        (slitBoxSplitCoverMap_mem_coverBox n hn v)
      cases v with
      | inl u =>
          apply slitBoxSplitShiftedVertex_mem_coverBox n hn k hlo hhi
          · exact ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2.1⟩
          · simp [slitBoxSplitCoverMap, slitBoxInteriorCoverLift]
            omega
      | inr a =>
          apply slitBoxSplitShiftedVertex_mem_coverBox n hn k hlo hhi
          · exact ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2.1⟩
          · cases a.2 <;> simp [slitBoxSplitCoverMap]
    ⟩
  inj' := by
    intro u v huv
    apply slitBoxSplitCoverMap_injective n
    have hval := congrArg Subtype.val huv
    apply Prod.ext
    · simpa [parafermionicCoverSheetTranslate] using congrArg Prod.fst hval
    · have := congrArg Prod.snd hval
      dsimp [parafermionicCoverSheetTranslate] at this
      omega

@[simp] theorem slitBoxSplitShiftedEmbedding_val
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ)
    (hlo : -((n ^ 5 : ℕ) : ℤ) ≤ k)
    (hhi : k + 1 ≤ ((n ^ 5 : ℕ) : ℤ))
    (v : SlitBoxSplitCoverVertex n) :
    (slitBoxSplitShiftedEmbedding n hn k hlo hhi v).val =
      parafermionicCoverSheetTranslate k (slitBoxSplitCoverMap n v) := rfl

theorem slitBoxSplitShiftedGraph_map_le_coverBox
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ)
    (hlo : -((n ^ 5 : ℕ) : ℤ) ≤ k)
    (hhi : k + 1 ≤ ((n ^ 5 : ℕ) : ℤ)) :
    (slitBoxSplitCoverGraph n).map
        (slitBoxSplitShiftedEmbedding n hn k hlo hhi) ≤
      parafermionicCoverBoxGraph n := by
  rw [SimpleGraph.map_le_iff_le_comap]
  intro u v huv
  change (parafermionicCoverBoxGraph n).Adj
    (slitBoxSplitShiftedEmbedding n hn k hlo hhi u)
    (slitBoxSplitShiftedEmbedding n hn k hlo hhi v)
  rw [parafermionicCoverBoxGraph, SimpleGraph.induce_adj]
  have hcover : parafermionicCoverGraph.Adj
      (slitBoxSplitCoverMap n u) (slitBoxSplitCoverMap n v) := huv.1
  have hshift := (parafermionicCoverSheetTranslationIso k).map_rel_iff.mpr hcover
  have hshift' : parafermionicCoverGraph.Adj
      ((slitBoxSplitShiftedEmbedding n hn k hlo hhi u).val)
      ((slitBoxSplitShiftedEmbedding n hn k hlo hhi v).val) := by
    simpa [slitBoxSplitShiftedEmbedding, parafermionicCoverSheetTranslationIso,
      parafermionicCoverSheetTranslate] using hshift
  exact hshift'

theorem slitBoxSplitShiftedEmbedding_interior_neighbor_closed
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ)
    (hlo : -((n ^ 5 : ℕ) : ℤ) ≤ k)
    (hhi : k + 1 ≤ ((n ^ 5 : ℕ) : ℤ))
    (u : SlitBoxSplitInterior n) (v : ParafermionicCoverBoxVertex n)
    (hadj : (parafermionicCoverBoxGraph n).Adj
      (slitBoxSplitShiftedEmbedding n hn k hlo hhi (Sum.inl u)) v) :
    ∃ y : SlitBoxSplitCoverVertex n,
      slitBoxSplitShiftedEmbedding n hn k hlo hhi y = v ∧
      (slitBoxSplitCoverGraph n).Adj (Sum.inl u) y := by
  let z : ParafermionicCoverVertex :=
    parafermionicCoverSheetTranslate (-k) v.val
  have hzAdj : parafermionicCoverGraph.Adj
      (slitBoxInteriorCoverLift n u) z := by
    have h := hadj
    rw [parafermionicCoverBoxGraph, SimpleGraph.induce_adj] at h
    change parafermionicCoverGraph.Adj
      (parafermionicCoverSheetTranslate k (slitBoxInteriorCoverLift n u)) v.val at h
    have hz := (parafermionicCoverSheetTranslationIso (-k)).map_rel_iff.mpr h
    have hcancel : parafermionicCoverSheetTranslationIso (-k)
        (parafermionicCoverSheetTranslate k (slitBoxInteriorCoverLift n u)) =
          slitBoxInteriorCoverLift n u := by
      apply Prod.ext
      · rfl
      · simp [parafermionicCoverSheetTranslationIso,
          parafermionicCoverSheetTranslate]
    rw [hcancel] at hz
    simpa [z, parafermionicCoverSheetTranslationIso,
      parafermionicCoverSheetTranslate] using hz
  have hzbox : z ∈ parafermionicCoverBoxVertices n := by
    have hvbox := (parafermionicCoverBoxVertices_mem n v.val).mp v.property
    have hsheet := slitBoxInteriorCoverLift_neighbor_sheet_range n u z hzAdj
    rcases hvbox with ⟨hxl, hxu, hyl, hyu, _, _⟩
    have hn5 : 1 ≤ (n ^ 5 : ℤ) := by
      exact_mod_cast (Nat.one_le_pow 5 n (by omega))
    have hzbase : -(n : ℤ) ≤ z.1.1 ∧ z.1.1 ≤ n ∧
        -(n : ℤ) ≤ z.1.2 ∧ z.1.2 ≤ n := by
      simpa [z, parafermionicCoverSheetTranslate] using
        (show -(n : ℤ) ≤ v.val.1.1 ∧ v.val.1.1 ≤ n ∧
          -(n : ℤ) ≤ v.val.1.2 ∧ v.val.1.2 ≤ n from ⟨hxl, hxu, hyl, hyu⟩)
    simpa [parafermionicCoverSheetTranslate] using
      slitBoxSplitShiftedVertex_mem_coverBox n hn 0 (by omega) (by omega)
      z hzbase hsheet
  let zbox : ParafermionicCoverBoxVertex n := ⟨z, hzbox⟩
  obtain ⟨y, hy, hyAdj⟩ :=
    slitBoxSplitCover_interior_neighbor_closed n hn u zbox hzAdj
  refine ⟨y, ?_, hyAdj⟩
  apply Subtype.ext
  have hyval := congrArg Subtype.val hy
  change parafermionicCoverSheetTranslate k (slitBoxSplitCoverMap n y) = v.val
  have hmap : slitBoxSplitCoverMap n y = z := by
    simpa [zbox] using hyval
  rw [hmap]
  simp [z, parafermionicCoverSheetTranslate]

end
end PottsContinuity.FKC.FiniteFK
