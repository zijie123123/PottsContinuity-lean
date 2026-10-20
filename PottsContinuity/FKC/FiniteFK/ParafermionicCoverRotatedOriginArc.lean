-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverRotatedOriginArc.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverRotatedBoxLaw
public import PottsContinuity.FKC.FiniteFK.SlitBoxDomain
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

def parafermionicCoverQuarterTurnOriginImage (j : Fin 4) : ParafermionicCoverVertex :=
  match j.val with
  | 0 => ((0, 0), 0)
  | 1 => ((0, -1), 0)
  | 2 => ((1, -1), 1)
  | _ => ((1, 0), 1)

theorem parafermionicCoverQuarterTurn_iterate_origin_eq_routePoint (j : Fin 4) :
    parafermionicCoverQuarterTurnIsoIterate j.val ((0, 0), 0) =
      parafermionicCoverQuarterTurnOriginImage j := by
  fin_cases j <;>
    norm_num [parafermionicCoverQuarterTurnOriginImage, parafermionicCoverQuarterTurnIsoIterate_apply,
      Function.iterate_succ_apply', parafermionicCoverQuarterTurn,
      parafermionicCoverQuarterTurnBase, parafermionicCoverQuarterTurnGauge]

private theorem rotatedOriginRoute_point_mem (m : ℕ) (hm : 1 ≤ m)
    (p : ParafermionicCoverVertex)
    (hp : p = ((0, 0), 0) ∨ p = ((0, -1), 0) ∨
      p = ((1, -1), 1) ∨ p = ((1, 0), 1) ∨ p = ((0, 0), 1)) :
    p ∈ parafermionicCoverBoxVertices m := by
  rw [parafermionicCoverBoxVertices_mem]
  have hmz : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  have hpow : (1 : ℤ) ≤ (m : ℤ) ^ 5 := by
    exact_mod_cast (Nat.one_le_pow 5 m hm)
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num <;> omega

 theorem rotatedOriginRoute_iterate_mem (m : ℕ) (hm : 1 ≤ m) (j : Fin 4) :
    parafermionicCoverQuarterTurnOriginImage j ∈
      parafermionicCoverBoxVertices m := by
  rw [parafermionicCoverBoxVertices_mem]
  have hmz : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  have hpow : (1 : ℤ) ≤ (m : ℤ) ^ 5 := by
    exact_mod_cast (Nat.one_le_pow 5 m hm)
  fin_cases j <;> simp [parafermionicCoverQuarterTurnOriginImage]<;> omega

private theorem rotatedOriginRoute_adj_box (m : ℕ)
    (p q : ParafermionicCoverVertex)
    (hp : p ∈ parafermionicCoverBoxVertices m)
    (hq : q ∈ parafermionicCoverBoxVertices m)
    (h : parafermionicCoverGraph.Adj p q) :
    (parafermionicCoverBoxGraph m).Adj ⟨p, hp⟩ ⟨q, hq⟩ := h

private theorem rotatedOriginRoute_vertical :
    parafermionicCoverGraph.Adj ((0, -1), 0) ((0, 0), 0) := by
  norm_num [parafermionicCoverGraph_adj_iff_cases, parafermionicCoverAdjCases,
    parafermionicCoverSheetShift,
    squareLattice_adj_iff]

private theorem rotatedOriginRoute_lowerSeam :
    parafermionicCoverGraph.Adj ((1, -1), 1) ((0, -1), 0) := by
  norm_num [parafermionicCoverGraph_adj_iff_cases, parafermionicCoverAdjCases,
    parafermionicCoverSheetShift,
    squareLattice_adj_iff]

private theorem rotatedOriginRoute_upperSeam :
    parafermionicCoverGraph.Adj ((1, 0), 1) ((0, 0), 1) := by
  norm_num [parafermionicCoverGraph_adj_iff_cases, parafermionicCoverAdjCases,
    parafermionicCoverSheetShift,
    squareLattice_adj_iff]

/-- Each quarter-turn image of the original cover origin has a concrete
length-at-most-two route inside `U_m` to the actual slit-arc basepoint
`(0,0)` on sheet zero or one. The third image uses the lower-seam edge. -/
theorem parafermionicCoverQuarterTurn_origin_reaches_slitArcBase
    (m : ℕ) (hm : 1 ≤ m) (j : Fin 4) :
    ∃ t : ParafermionicCoverBoxVertex m,
      t.val.1 = (0, 0) ∧ (t.val.2 = 0 ∨ t.val.2 = 1) ∧
      ∃ p : (parafermionicCoverBoxGraph m).Walk
        ⟨parafermionicCoverQuarterTurnOriginImage j,
          rotatedOriginRoute_iterate_mem m hm j⟩ t, p.length ≤ 2 := by
  have h0 := rotatedOriginRoute_point_mem m hm ((0, 0), 0) (Or.inl rfl)
  have hminus := rotatedOriginRoute_point_mem m hm ((0, -1), 0) (Or.inr (Or.inl rfl))
  have hlower := rotatedOriginRoute_point_mem m hm ((1, -1), 1) (Or.inr (Or.inr (Or.inl rfl)))
  have hupper := rotatedOriginRoute_point_mem m hm ((1, 0), 1)
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hV := rotatedOriginRoute_vertical
  have hL := rotatedOriginRoute_lowerSeam
  have hU := rotatedOriginRoute_upperSeam
  fin_cases j <;> simp only [parafermionicCoverQuarterTurnOriginImage]
  · refine ⟨⟨((0, 0), 0), h0⟩, rfl, Or.inl rfl, ?_⟩
    exact ⟨SimpleGraph.Walk.nil, by simp⟩
  · refine ⟨⟨((0, 0), 0), h0⟩, rfl, Or.inl rfl, ?_⟩
    refine ⟨SimpleGraph.Walk.cons (rotatedOriginRoute_adj_box m _ _ hminus h0 hV)
      SimpleGraph.Walk.nil, by simp⟩
  · refine ⟨⟨((0, 0), 0), h0⟩, rfl, Or.inl rfl, ?_⟩
    refine ⟨SimpleGraph.Walk.cons
      (rotatedOriginRoute_adj_box m _ _ hlower hminus hL)
      (SimpleGraph.Walk.cons (rotatedOriginRoute_adj_box m _ _ hminus h0 hV)
        SimpleGraph.Walk.nil), by simp⟩
  · refine ⟨⟨((0, 0), 1), ?_⟩, rfl, Or.inr rfl, ?_⟩
    · exact rotatedOriginRoute_point_mem m hm ((0, 0), 1) (by norm_num)
    · refine ⟨SimpleGraph.Walk.cons (rotatedOriginRoute_adj_box m _ _ hupper
          (rotatedOriginRoute_point_mem m hm ((0, 0), 1) (by norm_num)) hU)
        SimpleGraph.Walk.nil, by simp⟩

end
end PottsContinuity.FKC.FiniteFK
