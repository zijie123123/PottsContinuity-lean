module

public import PottsContinuity.Thm4.SlitCenterPairComparison

@[expose] public section

namespace PottsContinuity.Thm4
noncomputable section

/-- Lemma 8: polynomial bottom-center to wired-arc connection probability,
for every real 1 <= q <= 4, at the explicit self-dual parameter. -/
theorem slit_center_arc_polynomial_lower_bound (q : Set.Icc (1 : ℝ) 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c / (n : ℝ)^16 ≤ slitArcConnectionProbability n ⟨q, q.2.1⟩
        (PottsContinuity.FKC.FiniteFK.slitBoxBottomCenterVertex n) := by
  obtain ⟨d, hd, hpair⟩ := slit_paired_bottom_polynomial_witness q
  refine ⟨d / 20, by positivity, ?_⟩
  intro n hn
  obtain ⟨u, huX, huY, hmass⟩ := hpair n hn
  have hcenter := slit_center_probability_ge_pair n hn u huY huX q
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hfactor : (d / 20) / (n : ℝ)^16 =
      (1 / (20 * (n : ℝ)^4)) * (d / (n : ℝ)^12) := by
    field_simp
  rw [hfactor]
  exact (mul_le_mul_of_nonneg_left hmass (by positivity)).trans hcenter

/-- The same statement with the actual PD finite measure displayed explicitly.
The designated boundary partition is the literal slit-box Dobrushin partition. -/
theorem slit_box_center_arc_polynomial_lower_bound (q : Set.Icc (1 : ℝ) 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c / (n : ℝ)^16 ≤
        (PottsContinuity.PD.FK.measure
          (PottsContinuity.FKC.FiniteFK.slitBoxGraph n)
          (selfDualParameters ⟨q, q.2.1⟩)
          (fkcBoundaryToPD (PottsContinuity.FKC.FiniteFK.slitBoxBoundary n))
          (PottsContinuity.FKC.FiniteFK.slitBoxWiredArcConnectionEvent n
            (PottsContinuity.FKC.FiniteFK.slitBoxBottomCenterVertex n))).toReal :=
  slit_center_arc_polynomial_lower_bound q

end
end PottsContinuity.Thm4
