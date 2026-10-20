module

public import PottsContinuity.Thm4.SideWitness
public import PottsContinuity.Thm4.SidePositive

@[expose] public section

namespace PottsContinuity.Thm4
noncomputable section

/-- The interior-sheet side witness in the source's Lemma 8 bootstrap, valid
at every scale and throughout the full closed real range 1 <= q <= 4.
The parameter is the explicit self-dual value. -/
theorem cover_side_connection_polynomial_witness (q : Set.Icc (1 : ℝ) 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ v ∈ coverSideBoundary n,
        c / (n : ℝ)^6 ≤ coverOriginConnectionProbability n ⟨q, q.2.1⟩ v := by
  classical
  obtain ⟨c₀, hc₀, N, hN, heventual⟩ := cover_side_connection_eventual_polynomial_witness q
  let S := Finset.range N
  let f : ℕ → ℝ := fun m =>
    coverOriginConnectionProbability (m + 1) ⟨q, q.2.1⟩
      (coverPositiveVerticalVertex (m + 1) (by omega)) * (((m + 1 : ℕ) : ℝ)^6)
  have hS : S.Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨i, hi, hmin⟩ := S.exists_min_image f hS
  have hfi : 0 < f i := by
    dsimp [f]
    exact mul_pos (coverPositiveVerticalVertex_probability_pos _ _ _)
      (pow_pos (by positivity) _)
  let c := min c₀ (f i)
  have hc : 0 < c := lt_min hc₀ hfi
  refine ⟨c, hc, ?_⟩
  intro n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  by_cases hnN : N ≤ n
  · obtain ⟨v, hv, hbound⟩ := heventual n hnN
    refine ⟨v, hv, ?_⟩
    exact (div_le_div_of_nonneg_right (min_le_left _ _) (pow_pos hnR _).le).trans hbound
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : m ∈ S := Finset.mem_range.mpr (by omega)
    have hcf : c ≤ f m := (min_le_right _ _).trans (hmin _ hm)
    refine ⟨coverPositiveVerticalVertex (m + 1) hn,
      coverPositiveVerticalVertex_mem (m + 1) hn, ?_⟩
    exact (div_le_iff₀ (pow_pos hnR _)).mpr hcf

end
end PottsContinuity.Thm4
