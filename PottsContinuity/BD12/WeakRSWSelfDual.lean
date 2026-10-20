module

public import PottsContinuity.BD12.WiredIntegerAspectBounds

/-! Wired RSW for every real aspect bound at the explicit self-dual point.
The final uniform coefficient depends only on the cluster weight and aspect. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK MeasureTheory
noncomputable section

/-- The wired crossing bound for all positive integer widths m<alpha*n. -/
theorem wired_weakRSW_at_selfDual (q : Set.Ici (1 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 1 μ)
    (α : ℝ) (_hα : 1 < α) :
    ∃ c : ℝ, 0 < c ∧ ∀ m n : ℕ, 0 < m → (m : ℝ) < α*n →
      c ≤ μ.real (horizontalRectangle (0,0) m n) := by
  let R := max 1 ⌈α⌉₊
  have hR : 1 ≤ R := le_max_left _ _
  have hαR : α ≤ (R : ℝ) := (Nat.le_ceil α).trans (by exact_mod_cast (le_max_right 1 ⌈α⌉₊))
  obtain ⟨c,hc,hbound⟩ := wired_selfDual_integer_aspect_all_scales_lower_bound q μ hμ R hR
  refine ⟨c,hc,fun m n _ hmn => ?_⟩
  have hn : 1 ≤ n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    rw [hn0,Nat.cast_zero,mul_zero] at hmn
    exact not_lt_of_ge (Nat.cast_nonneg m) hmn
  have hw : m ≤ R*n := by
    exact_mod_cast (hmn.le.trans (mul_le_mul_of_nonneg_right hαR (Nat.cast_nonneg n)))
  exact hbound n m hn hw

/-- The coefficient is chosen before all measures and rectangle sizes; frozen
limit uniqueness makes its dependence only on alpha and q explicit. -/
theorem wired_weakRSW_uniform_at_selfDual (q : Set.Ici (1 : ℝ)) (α : ℝ) (hα : 1 < α) :
    ∃ c : ℝ, 0 < c ∧ ∀ (μ : Measure LatticeConfiguration),
      IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 1 μ →
      ∀ m n : ℕ, 0 < m → (m : ℝ) < α*n →
        c ≤ μ.real (horizontalRectangle (0,0) m n) := by
  obtain ⟨μ₀,hμ₀⟩ := Foundations.exists_isRCInfiniteVolumeLimit
    (criticalParameters q).toP (criticalParameters q).toQ (criticalParameters q).property 1
  obtain ⟨c,hc,hbound⟩ := wired_weakRSW_at_selfDual q μ₀ hμ₀ α hα
  refine ⟨c,hc,fun μ hμ m n hm hmn => ?_⟩
  have heq := WellDefined.limit_unique _ _ 1 μ μ₀ hμ hμ₀
  rw [heq]
  exact hbound m n hm hmn

end
end PottsContinuity.BD12
