module

public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory

/-- A finite event cover supplies a seed with the exact averaged lower bound,
including the final closed segment of a geometric partition. -/
theorem finite_union_seed_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (N : ℕ) (hN : 0 < N)
    (E : Set Ω) (F : Fin N → Set Ω) (hcover : E ⊆ ⋃ j, F j)
    (c : ℝ) (hc : c ≤ μ.real E) :
    ∃ j : Fin N, c/(N:ℝ) ≤ μ.real (F j) := by
  classical
  by_contra h
  push Not at h
  have hsum : (∑ j : Fin N, μ.real (F j)) < ∑ _j : Fin N, c/(N:ℝ) := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨⟨0,hN⟩,Finset.mem_univ _⟩
    · intro j hj
      exact h j
  have hNreal : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hconst : (∑ _j : Fin N, c/(N:ℝ)) = c := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  have hbound := (measureReal_mono (μ := μ) (h₂ := measure_ne_top _ _) hcover).trans (measureReal_iUnion_fintype_le F)
  rw [hconst] at hsum
  exact (not_lt_of_ge (hc.trans hbound)) hsum

end PottsContinuity.RSW
