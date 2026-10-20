-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverRotatedSideEndpoint.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverSideBoundary
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverRotatedBoxLaw
public import PottsContinuity.FKC.FiniteFK.SlitBoxSplitShiftedEmbedding
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open PottsContinuity.FKC.Medial

noncomputable section

private theorem parafermionicCoverQuarterTurnGauge_bounds (p : LatticeVertex) :
    0 ≤ parafermionicCoverQuarterTurnGauge p ∧
      parafermionicCoverQuarterTurnGauge p ≤ 1 := by
  simp [parafermionicCoverQuarterTurnGauge]
  split_ifs <;> omega

private theorem parafermionicCoverQuarterTurn_iterate_sheet_bounds
    (m : ℕ) (hm : m ≤ 3) (v : ParafermionicCoverVertex) :
    v.2 ≤ ((parafermionicCoverQuarterTurn^[m]) v).2 ∧
      ((parafermionicCoverQuarterTurn^[m]) v).2 ≤ v.2 + m := by
  induction m generalizing v with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply]
      have h := ih (by omega) (parafermionicCoverQuarterTurn v)
      rcases h with ⟨hlo, hhi⟩
      have hg := parafermionicCoverQuarterTurnGauge_bounds v.1
      simp only [parafermionicCoverQuarterTurn] at hlo hhi ⊢
      constructor <;> omega

theorem parafermionicCoverRotatedSideEndpoint_spec
    (n : ℕ) {v : ParafermionicCoverVertex}
    (hv : v ∈ parafermionicCoverExteriorNeighborBoundary n) :
    ∃ j : Fin 4, let z := parafermionicCoverQuarterTurnIsoIterate j.val v
      z.1.2 = -(n : ℤ) ∨ z.1.2 = -((n : ℤ) + 1) := by
  classical
  have hcoord := parafermionicCoverExteriorNeighborBoundary_coord n hv
  rcases Finset.mem_filter.mp hv with ⟨hbox, _, _⟩
  have hb := (parafermionicCoverBoxVertices_mem n v).mp hbox
  rcases hcoord with hleft | hright | hbottom | htop
  · refine ⟨⟨1, by decide⟩, ?_⟩
    simp only [parafermionicCoverQuarterTurnIsoIterate_apply]
    simp [parafermionicCoverQuarterTurn, parafermionicCoverQuarterTurnBase, hleft]; omega
  · refine ⟨⟨3, by decide⟩, ?_⟩
    simp only [parafermionicCoverQuarterTurnIsoIterate_apply]
    simp [Function.iterate_succ_apply,
      parafermionicCoverQuarterTurn, parafermionicCoverQuarterTurnBase, hright]
  · refine ⟨⟨0, by decide⟩, ?_⟩
    simp only [parafermionicCoverQuarterTurnIsoIterate_apply]
    exact Or.inl hbottom
  · refine ⟨⟨2, by decide⟩, ?_⟩
    simp only [parafermionicCoverQuarterTurnIsoIterate_apply]
    simp [Function.iterate_succ_apply,
      parafermionicCoverQuarterTurn, parafermionicCoverQuarterTurnBase, htop]; omega

/-- Extend a lower-side point by zero or one vertical edge to the bottom side of
the next box. This statement keeps the sheet fixed. -/
theorem parafermionicCoverExtendLowerSideEndpoint
    (n : ℕ) (z : ParafermionicCoverVertex)
    (hzbox : z ∈ parafermionicCoverBoxVertices (n + 1))
    (hy : z.1.2 = -(n : ℤ) ∨ z.1.2 = -((n : ℤ) + 1))
    :
    let w : ParafermionicCoverVertex := ((z.1.1, -((n : ℤ) + 1)), z.2)
    w ∈ parafermionicCoverBoxVertices (n + 1) ∧
      (z = w ∨ parafermionicCoverGraph.Adj z w) := by
  dsimp only
  have hb := (parafermionicCoverBoxVertices_mem (n + 1) z).mp hzbox
  have hncast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by norm_cast
  have hnonneg : (0 : ℤ) ≤ (n : ℤ) + 1 := by positivity
  constructor
  · rw [parafermionicCoverBoxVertices_mem]
    rcases hb with ⟨hxlo, hxhi, hylo, hyhi, hklo, hkhi⟩
    refine ⟨hxlo, hxhi, ?_, ?_, hklo, hkhi⟩
    · rw [hncast]
    · rw [hncast]
      linarith
  · rcases hy with hy | hy
    · right
      rw [parafermionicCoverGraph_adj_iff_cases]
      refine Or.inr (Or.inl ?_)
      change z.1.1 = z.1.1 ∧ -((n : ℤ) + 1) + 1 = z.1.2 ∧ z.2 = z.2
      exact ⟨rfl, by omega, rfl⟩
    · left
      apply Prod.ext
      · exact Prod.ext rfl hy
      · rfl

/-- A rotated exterior-side vertex has a bottom endpoint in the next box,
which is represented by a shifted canonical split-interior lift. -/
theorem parafermionicCoverRotatedSideEndpoint_shiftedInterior
    (n : ℕ) (hn : 1 ≤ n) {v : ParafermionicCoverVertex}
    (hv : v ∈ parafermionicCoverExteriorNeighborBoundary n) :
    ∃ (j : Fin 4) (z w : ParafermionicCoverVertex)
      (u : SlitBoxSplitInterior (n + 1)) (k : ℤ)
      (hklo : -(((n + 1) ^ 5 : ℕ) : ℤ) ≤ k)
      (hkhi : k + 1 ≤ (((n + 1) ^ 5 : ℕ) : ℤ)),
      z = parafermionicCoverQuarterTurnIsoIterate j.val v ∧
      (z.1.2 = -(n : ℤ) ∨ z.1.2 = -((n : ℤ) + 1)) ∧
      w = ((z.1.1, -((n : ℤ) + 1)), z.2) ∧
      w ∈ parafermionicCoverBoxVertices (n + 1) ∧
      (z = w ∨ parafermionicCoverGraph.Adj z w) ∧
      (slitBoxSplitShiftedEmbedding (n + 1) (by omega) k
        hklo hkhi (Sum.inl u)).val = w := by
  classical
  obtain ⟨j, hside⟩ := parafermionicCoverRotatedSideEndpoint_spec n hv
  let z := parafermionicCoverQuarterTurnIsoIterate j.val v
  have hboxv : v ∈ parafermionicCoverBoxVertices n :=
    (Finset.mem_filter.mp hv).1
  have hzbox : z ∈ parafermionicCoverBoxVertices (n + 1) := by
    simpa [z, parafermionicCoverQuarterTurnIsoIterate_apply] using
      (parafermionicCoverQuarterTurn_iterates_mem_box_succ n v hboxv j)
  have hjle : j.val ≤ 3 := by omega
  have hsheetiter := parafermionicCoverQuarterTurn_iterate_sheet_bounds
    j.val hjle v
  have hfilter := Finset.mem_filter.mp hv
  rcases hfilter with ⟨_, ⟨hvlo, hvhi, _⟩⟩
  have hsheet : v.2 ≤ z.2 ∧ z.2 ≤ v.2 + (j.val : ℤ) := by
    simpa [z, parafermionicCoverQuarterTurnIsoIterate_apply] using hsheetiter
  have hzlo : -((n ^ 5 : ℕ) : ℤ) ≤ z.2 := by
    omega
  have hzhi : z.2 ≤ ((n ^ 5 : ℕ) : ℤ) + 2 := by
    omega
  have hpow : ((n : ℤ) + 1) ^ 5 = (n : ℤ) ^ 5 +
      5 * (n : ℤ) ^ 4 + 10 * (n : ℤ) ^ 3 +
      10 * (n : ℤ) ^ 2 + 5 * (n : ℤ) + 1 := by ring
  have hnZ : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hgap : (n : ℤ) ^ 5 + 4 ≤ ((n : ℤ) + 1) ^ 5 := by
    rw [hpow]
    nlinarith [sq_nonneg (n : ℤ), sq_nonneg ((n : ℤ) ^ 2)]
  have hgapCast : ((n ^ 5 : ℕ) : ℤ) + 4 ≤ (((n + 1) ^ 5 : ℕ) : ℤ) := by
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hgap
  have hpowNCast : ((n ^ 5 : ℕ) : ℤ) = (n : ℤ) ^ 5 := by simp
  have hpowMcast : (((n + 1) ^ 5 : ℕ) : ℤ) = ((n : ℤ) + 1) ^ 5 := by simp
  let w : ParafermionicCoverVertex := ((z.1.1, -((n : ℤ) + 1)), z.2)
  have hwinfo := parafermionicCoverExtendLowerSideEndpoint n z hzbox hside
  have hwbox : w ∈ parafermionicCoverBoxVertices (n + 1) := hwinfo.1
  have hwrel : z = w ∨ parafermionicCoverGraph.Adj z w := hwinfo.2
  let κ : ℤ := w.2 - if 0 < w.1.1 then 1 else 0
  have hklo : -(((n + 1) ^ 5 : ℕ) : ℤ) ≤ κ := by
    dsimp [κ, w]
    by_cases hx : 0 < z.1.1 <;> simp [hx] <;> omega
  have hkhi : κ + 1 ≤ (((n + 1) ^ 5 : ℕ) : ℤ) := by
    dsimp [κ, w]
    by_cases hx : 0 < z.1.1 <;> simp [hx] <;> omega
  let b : LatticeVertex := (w.1.1, w.1.2)
  have hbbox : b ∈ latticeRectangle (-( (n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
      (2 * (n + 1)) (2 * (n + 1)) := by
    have hb := (parafermionicCoverBoxVertices_mem (n + 1) w).mp hwbox
    rw [mem_latticeRectangle]
    rcases hb with ⟨hxl, hxu, hyl, hyu, _, _⟩
    simp only [b]
    constructor
    · exact ⟨hxl, by push_cast; omega⟩
    · exact ⟨hyl, by push_cast; omega⟩
  let vb : SlitBoxVertex (n + 1) := ⟨b, hbbox⟩
  have hvbArc : vb ∉ slitBoxWiredArc (n + 1) := by
    intro h
    have hmem := (mem_slitBoxWiredArc_iff (n + 1) vb).mp h
    have hnpos : 0 < ((n : ℤ) + 1) := by omega
    dsimp [vb, b, w] at hmem
    omega
  let u : SlitBoxSplitInterior (n + 1) := ⟨vb, hvbArc⟩
  have hcanonical : slitBoxInteriorCoverLift (n + 1) u =
      ((w.1.1, w.1.2), if 0 < w.1.1 then (1 : ℤ) else 0) := by
    rfl
  have htranslate : parafermionicCoverSheetTranslate κ
      (slitBoxInteriorCoverLift (n + 1) u) = w := by
    rw [hcanonical]
    apply Prod.ext
    · rfl
    · dsimp only [parafermionicCoverSheetTranslate]
      dsimp [κ]
      split_ifs <;> omega
  refine ⟨j, z, w, u, κ, hklo, hkhi, rfl, hside, rfl, hwbox, hwrel, ?_⟩
  simpa [slitBoxSplitShiftedEmbedding, slitBoxSplitCoverMap] using htranslate

end
end PottsContinuity.FKC.FiniteFK
