module

public import PottsContinuity.BD12.WeakRSWSelfDual
public import PottsContinuity.BD12.RectangleBoxComparison
public import PottsContinuity.BD12.RectangleTranslation

/-! Wired RSW in every finite box containing the entire translated rectangle. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory PD.FK PD.RCInfinite
noncomputable section

/-- The same positive aspect coefficient works for every containing finite
wired box and every translated rectangle. No infinite-limit or comparison
premise remains in this finite-volume bound. -/
theorem wired_finite_box_weakRSW_at_selfDual
    (q : Set.Ici (1 : ℝ)) (α : ℝ) (hα : 1 < α) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : LatticeVertex) (m n N : ℕ),
      0 < m → (m : ℝ) < α*n →
      PD.FK.latticeRectangle a m n ⊆ latticeBox (0,0) N →
      c ≤ (wiredBoxProbabilityMeasure (criticalParameters q) (0,0) N :
        Measure LatticeConfiguration).real (horizontalRectangle a m n) := by
  obtain ⟨c,hc,hbound⟩ := wired_weakRSW_uniform_at_selfDual q α hα
  obtain ⟨μraw,hμraw⟩ := Foundations.exists_isRCInfiniteVolumeLimit
    (criticalParameters q).toP (criticalParameters q).toQ (criticalParameters q).property 1
  let μ : Measure LatticeConfiguration := μraw
  have hμ : IsRCInfiniteVolumeLimit (criticalParameters q).toP
      (criticalParameters q).toQ 1 μ := hμraw
  refine ⟨c,hc,fun a m n N hm hmn hbox => ?_⟩
  have hrectangle : c ≤ μ.real (horizontalRectangle a m n) := by
    rw [wired_horizontalRectangle_probability_eq_origin (criticalParameters q) μ hμ a m n]
    exact hbound μ hμ m n hm hmn
  exact hrectangle.trans
    (wired_rectangle_probability_le_wired_box (criticalParameters q) μ hμ a m n N hbox)

end
end PottsContinuity.BD12
