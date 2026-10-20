module

public import PottsContinuity.Thm4.SlitReflection

@[expose] public section

namespace PottsContinuity.Thm4
noncomputable section

/-- A symmetric pair of bottom-to-arc connections has polynomial mass n^-12,
throughout the full closed real range. -/
theorem slit_paired_bottom_polynomial_witness (q : Set.Icc (1 : ℝ) 4) :
    ∃ d : ℝ, 0 < d ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ u : PottsContinuity.FKC.FiniteFK.SlitBoxVertex n,
        0 ≤ u.val.1 ∧ u.val.2 = -(n : ℤ) ∧
        d / (n : ℝ)^12 ≤ slitPairConnectionProbability n ⟨q, q.2.1⟩ u := by
  classical
  obtain ⟨c, hc, hbottom⟩ := slit_bottom_arc_polynomial_witness q
  refine ⟨c^2, pow_pos hc _, ?_⟩
  intro n hn
  obtain ⟨u₀, hu₀y, hu₀bound⟩ := hbottom n hn
  let σ := PottsContinuity.FKC.FiniteFK.slitBoxGraphHorizontalReflectionIso n
  let u := if 0 ≤ u₀.val.1 then u₀ else σ u₀
  have huy : u.val.2 = -(n : ℤ) := by
    by_cases hx : 0 ≤ u₀.val.1
    · simp [u, hx, hu₀y]
    · simp only [u, hx, ↓reduceIte]
      change (PottsContinuity.FKC.FiniteFK.slitBoxHorizontalReflectionVertexEquiv n u₀).val.2 = _
      rw [PottsContinuity.FKC.FiniteFK.slitBoxHorizontalReflectionVertexEquiv_val, hu₀y]
  have hux : 0 ≤ u.val.1 := by
    by_cases hx : 0 ≤ u₀.val.1
    · simp [u, hx]
    · simp only [u, hx, ↓reduceIte]
      change 0 ≤ (PottsContinuity.FKC.FiniteFK.slitBoxHorizontalReflectionVertexEquiv n u₀).val.1
      rw [PottsContinuity.FKC.FiniteFK.slitBoxHorizontalReflectionVertexEquiv_val]
      omega
  have huBound : c / (n : ℝ)^6 ≤ slitArcConnectionProbability n ⟨q, q.2.1⟩ u := by
    by_cases hx : 0 ≤ u₀.val.1
    · simpa [u, hx] using hu₀bound
    · simpa only [u, hx, ↓reduceIte, σ,
        ← slitArcConnectionProbability_reflection q n u₀] using hu₀bound
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ c / (n : ℝ)^6) huBound 2
  have hratio : (c / (n : ℝ)^6)^2 = c^2 / (n : ℝ)^12 := by
    rw [div_pow]
    congr 1
    ring
  refine ⟨u, hux, huy, ?_⟩
  rw [← hratio]
  exact hpow.trans (slitPairConnectionProbability_ge_square q n u)

end
end PottsContinuity.Thm4
