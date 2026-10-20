-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverQuarterTurnIterates.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverQuarterTurn
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC

private theorem parafermionicCoverQuarterTurn_iterate_two (u : ParafermionicCoverVertex) :
    (parafermionicCoverQuarterTurn^[2]) u =
      (parafermionicCoverQuarterTurnBase
          (parafermionicCoverQuarterTurnBase u.1),
        u.2 + parafermionicCoverQuarterTurnGauge u.1 +
          parafermionicCoverQuarterTurnGauge
            (parafermionicCoverQuarterTurnBase u.1)) := by
  simp [Function.iterate_succ_apply', parafermionicCoverQuarterTurn,
    parafermionicCoverQuarterTurnBase, parafermionicCoverQuarterTurnGauge, add_assoc]

private theorem parafermionicCoverQuarterTurn_iterate_three (u : ParafermionicCoverVertex) :
    (parafermionicCoverQuarterTurn^[3]) u =
      (parafermionicCoverQuarterTurnBase
          (parafermionicCoverQuarterTurnBase
            (parafermionicCoverQuarterTurnBase u.1)),
        u.2 + parafermionicCoverQuarterTurnGauge u.1 +
          parafermionicCoverQuarterTurnGauge
            (parafermionicCoverQuarterTurnBase u.1) +
          parafermionicCoverQuarterTurnGauge
            (parafermionicCoverQuarterTurnBase
              (parafermionicCoverQuarterTurnBase u.1))) := by
  simp [Function.iterate_succ_apply', parafermionicCoverQuarterTurn,
    parafermionicCoverQuarterTurnBase, parafermionicCoverQuarterTurnGauge, add_assoc]

private theorem parafermionicCoverQuarterTurn_gauge_sum_two_bounds
    (p : LatticeVertex) :
    0 ≤ parafermionicCoverQuarterTurnGauge p +
        parafermionicCoverQuarterTurnGauge (parafermionicCoverQuarterTurnBase p) ∧
      parafermionicCoverQuarterTurnGauge p +
        parafermionicCoverQuarterTurnGauge (parafermionicCoverQuarterTurnBase p) ≤ 1 := by
  rcases p with ⟨x, y⟩
  simp [parafermionicCoverQuarterTurnGauge, parafermionicCoverQuarterTurnBase]
  split_ifs <;> norm_num; omega

private theorem parafermionicCoverQuarterTurn_gauge_sum_three_bounds
    (p : LatticeVertex) :
    0 ≤ parafermionicCoverQuarterTurnGauge p +
        parafermionicCoverQuarterTurnGauge (parafermionicCoverQuarterTurnBase p) +
        parafermionicCoverQuarterTurnGauge
          (parafermionicCoverQuarterTurnBase (parafermionicCoverQuarterTurnBase p)) ∧
      parafermionicCoverQuarterTurnGauge p +
        parafermionicCoverQuarterTurnGauge (parafermionicCoverQuarterTurnBase p) +
        parafermionicCoverQuarterTurnGauge
          (parafermionicCoverQuarterTurnBase (parafermionicCoverQuarterTurnBase p)) ≤ 1 := by
  rcases p with ⟨x, y⟩
  simp [parafermionicCoverQuarterTurnGauge, parafermionicCoverQuarterTurnBase]
  split_ifs <;> norm_num <;> omega

private theorem parafermionicCoverBoxVertices_mono_succ (n : ℕ)
    (u : ParafermionicCoverVertex) (hu : u ∈ parafermionicCoverBoxVertices n) :
    u ∈ parafermionicCoverBoxVertices (n + 1) := by
  rw [parafermionicCoverBoxVertices_mem] at hu ⊢
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] at hu ⊢
  have hn : 0 ≤ (n : ℤ) := Int.natCast_nonneg n
  have hn2 : 0 ≤ (n : ℤ) ^ 2 := sq_nonneg (n : ℤ)
  have hn3 : 0 ≤ (n : ℤ) ^ 3 := by positivity
  have hn4 : 0 ≤ (n : ℤ) ^ 4 := by positivity
  have hpow : (n : ℤ) ^ 5 ≤ ((n : ℤ) + 1) ^ 5 := by nlinarith
  omega

/-- Every one of the first four lifted quarter-turn positions of a vertex of `U_n`
belongs to the common enlarged box `U_(n+1)`. -/
theorem parafermionicCoverQuarterTurn_iterates_mem_box_succ (n : ℕ)
    (u : ParafermionicCoverVertex) (hu : u ∈ parafermionicCoverBoxVertices n) :
    ∀ j : Fin 4,
      (parafermionicCoverQuarterTurn^[j.val]) u ∈ parafermionicCoverBoxVertices (n + 1) := by
  intro j
  fin_cases j
  · simpa using parafermionicCoverBoxVertices_mono_succ n u hu
  · simpa using parafermionicCoverQuarterTurn_mem_box_succ n u hu
  · rw [parafermionicCoverQuarterTurn_iterate_two]
    rcases u with ⟨⟨x, y⟩, k⟩
    rw [parafermionicCoverBoxVertices_mem] at hu ⊢
    simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] at hu ⊢
    rcases hu with ⟨hxlo, hxhi, hylo, hyhi, hklo, hkhi⟩
    have hn : 0 ≤ (n : ℤ) := Int.natCast_nonneg n
    have hn2 : 0 ≤ (n : ℤ) ^ 2 := sq_nonneg (n : ℤ)
    have hn3 : 0 ≤ (n : ℤ) ^ 3 := by positivity
    have hn4 : 0 ≤ (n : ℤ) ^ 4 := by positivity
    have hpow : (n : ℤ) ^ 5 + 1 ≤ ((n : ℤ) + 1) ^ 5 := by nlinarith
    have hsum := parafermionicCoverQuarterTurn_gauge_sum_two_bounds (x, y)
    simp only [parafermionicCoverQuarterTurnBase] at hsum ⊢
    omega
  · rw [parafermionicCoverQuarterTurn_iterate_three]
    rcases u with ⟨⟨x, y⟩, k⟩
    rw [parafermionicCoverBoxVertices_mem] at hu ⊢
    simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] at hu ⊢
    rcases hu with ⟨hxlo, hxhi, hylo, hyhi, hklo, hkhi⟩
    have hn : 0 ≤ (n : ℤ) := Int.natCast_nonneg n
    have hn2 : 0 ≤ (n : ℤ) ^ 2 := sq_nonneg (n : ℤ)
    have hn3 : 0 ≤ (n : ℤ) ^ 3 := by positivity
    have hn4 : 0 ≤ (n : ℤ) ^ 4 := by positivity
    have hpow : (n : ℤ) ^ 5 + 1 ≤ ((n : ℤ) + 1) ^ 5 := by nlinarith
    have hsum := parafermionicCoverQuarterTurn_gauge_sum_three_bounds (x, y)
    simp only [parafermionicCoverQuarterTurnBase] at hsum ⊢
    omega

end PottsContinuity.FKC.Medial
