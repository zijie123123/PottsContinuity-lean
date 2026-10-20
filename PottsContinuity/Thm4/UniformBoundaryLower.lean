module

public import PottsContinuity.Thm4.CoverMeasureBridge

@[expose] public section

namespace PottsContinuity.Thm4
noncomputable section

/-- Equation (35), at the explicit self-dual parameter, on the literal full
cover box for every real 1 <= q <= 4. The strictly positive constant depends on
q alone. The endpoint proof uses actual winding and gives the constant 4/3. -/
theorem cover_boundary_connection_sum_uniform_lower (q : Set.Icc (1 : ℝ) 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ ∑ v ∈ coverExteriorBoundary n,
        coverOriginConnectionProbability n ⟨q, q.2.1⟩ v := by
  by_cases hq : q.val = 4
  · have heq : q = ⟨4, by norm_num⟩ := Subtype.ext hq
    subst q
    exact ⟨4 / 3, by norm_num, cover_boundary_connection_sum_lower_bound_four⟩
  · have hlt : q.val < 4 := lt_of_le_of_ne q.2.2 hq
    let q' : PottsContinuity.FKC.ClusterWeight := ⟨q.val, q.2.1, hlt⟩
    obtain ⟨c, hc, hbound⟩ :=
      PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteFreeBoundaryConnectionSum_uniform_lower q'
    refine ⟨c, hc, ?_⟩
    intro n hn
    have h := hbound n hn
    rw [fkc_boundary_connection_sum_eq] at h
    exact h

end
end PottsContinuity.Thm4
