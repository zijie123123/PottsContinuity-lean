module

public import PottsContinuity.BD12.WiredEvenAspectBounds

/-! Every integer aspect bound at every positive integer height, including
odd and unit heights. Coordinate truncation retains all original open bonds. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK MeasureTheory
noncomputable section

/-- A uniform positive bound on all widths bounded by R times the height. -/
theorem wired_selfDual_integer_aspect_all_scales_lower_bound (q : Set.Ici (1 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 1 μ)
    (R : ℕ) (hR : 1 ≤ R) :
    ∃ c : ℝ, 0 < c ∧ ∀ n w : ℕ, 1 ≤ n → w ≤ R*n →
      c ≤ μ.real (horizontalRectangle (0,0) w n) := by
  let : IsProbabilityMeasure μ := hμ.1
  obtain ⟨a,ha,heven⟩ := wired_selfDual_even_height_aspect_lower_bound q μ hμ (2*R) (by omega)
  let b := μ.real (horizontalRectangle (0,0) R 0)
  have hb : 0 < b := infinite_horizontalRectangle_probability_pos (criticalParameters q) 1 μ hμ (0,0) R 0
  refine ⟨min a b,lt_min ha hb,fun n w hn hw => ?_⟩
  by_cases hn2 : 2 ≤ n
  · let k := n/2
    have hk : 1 ≤ k := by dsimp only [k]; omega
    have hn4 : n ≤ 4*k := by dsimp only [k]; omega
    have hw' : w ≤ 2*(2*R)*k := by
      calc
        w ≤ R*n := hw
        _ ≤ R*(4*k) := Nat.mul_le_mul_left R hn4
        _ = _ := by ring
    have hbase := (heven k hk).trans_eq
      (wired_horizontalRectangle_probability_eq_origin (criticalParameters q) μ hμ _ _ _)
    have hsub := (horizontalRectangle_mono_width (0,0) w (2*(2*R)*k) (2*k) hw').trans
      (horizontalRectangle_mono_height (0,0) w (2*k) n (by dsimp only [k]; omega))
    exact (min_le_left _ _).trans (hbase.trans (measureReal_mono hsub))
  · have hn1 : n = 1 := by omega
    subst n
    have hw' : w ≤ R := by simpa only [Nat.mul_one] using hw
    have hsub := (horizontalRectangle_mono_width (0,0) w R 0 hw').trans
      (horizontalRectangle_mono_height (0,0) w 0 1 (by omega))
    exact (min_le_right _ _).trans (measureReal_mono hsub)

end
end PottsContinuity.BD12
