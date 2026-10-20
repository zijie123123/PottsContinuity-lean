module

public import PottsContinuity.Thm3.RSW.BufferedPositivity

/-! Finite positive minima and all-scale closure for the exact buffered event. -/

@[expose] public section

namespace PottsContinuity.RSW

/-- Finitely many strictly positive real values have a positive common lower
bound. The empty family imposes no constraint. -/
theorem exists_positive_lower_finset {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < a i) : ∃ c : ℝ, 0 < c ∧ ∀ i ∈ s, c ≤ a i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1,one_pos,by simp⟩
  | @insert i s his ih =>
    obtain ⟨d,hd,hs⟩ := ih (fun j hj => hpos j (Finset.mem_insert_of_mem hj))
    refine ⟨min (a i) d,lt_min (hpos i (Finset.mem_insert_self _ _)) hd,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hs j hj)

/-- Positivity at finite scales extends a positive uniform tail bound to
every positive integer scale. -/
theorem positive_lower_all_positive_of_tail (a : ℕ → ℝ)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (N : ℕ)
    (htail : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, N ≤ n → c ≤ a n) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → c ≤ a n := by
  obtain ⟨c,hc,hbound⟩ := htail
  obtain ⟨d,hd,hbase⟩ := exists_positive_lower_finset (Finset.Icc 1 N) a
    (fun n hn => hpos n (Finset.mem_Icc.mp hn).1)
  refine ⟨min c d,lt_min hc hd,fun n hn => ?_⟩
  by_cases hnN : n ≤ N
  · exact (min_le_right _ _).trans (hbase n (Finset.mem_Icc.mpr ⟨hn,hnN⟩))
  · exact (min_le_left _ _).trans (hbound n (by omega))

/-- Exact buffered P5 extends from a uniform tail without any additional
small-scale model premise. This is only the tail-to-all-scale consumer. -/
theorem bufferedCrossingProbability_uniform_of_tail (θ : PD.FK.Parameters)
    (α : ℝ) (hα : 0 < α) (N : ℕ)
    (htail : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, N ≤ n →
      c ≤ bufferedCrossingProbability θ.toP θ.toQ α n) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ bufferedCrossingProbability θ.toP θ.toQ α n :=
  positive_lower_all_positive_of_tail _ (fun n hn => bufferedCrossingProbability_pos θ α hα n hn) N htail

end PottsContinuity.RSW
