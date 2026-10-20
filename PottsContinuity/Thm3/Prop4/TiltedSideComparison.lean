module

public import PottsContinuity.Thm3.Prop4.TiltedIntervalCylinders

/-! # The top-only finite tilted law is below the side-wired law -/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.RCInfinite

noncomputable section

/-- Literal boundary-partition order, with the same original-edge event. -/
theorem tiltedWindow_top_partition_le (n M : ℕ) (t : ℝ) (side : Fin 2) :
    (tiltedWindowBoundary n M t 0).partition ≤ (tiltedWindowBoundary n M t side).partition := by
  intro u v huv
  change (u = v ∨ (tiltedTop n t u.val ∨ _) ∧ (tiltedTop n t v.val ∨ _)) at huv
  simp only [Fin.zero_ne_one,false_and,or_false] at huv
  change u = v ∨ (tiltedTop n t u.val ∨ _) ∧ (tiltedTop n t v.val ∨ _)
  rcases huv with rfl | ⟨hu,hv⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨Or.inl hu,Or.inl hv⟩

/-- Finite all-open cylinders increase when the outer sides are wired. -/
theorem tiltedWindowPlane_top_allOpen_le_side (θ : Parameters) (n M : ℕ) (t : ℝ)
    (side : Fin 2) (F : Finset squareLattice.edgeSet) :
    (tiltedWindowPlaneProbabilityMeasure θ n t 0 M).toMeasure.real (LatticeConfiguration.allOpen F) ≤
      (tiltedWindowPlaneProbabilityMeasure θ n t side M).toMeasure.real (LatticeConfiguration.allOpen F) := by
  rw [tiltedWindowPlane_allOpen_eq,tiltedWindowPlane_allOpen_eq]
  apply measure_boundary_comparison θ _ _ (tiltedWindow_top_partition_le n M t side)
  intro A B hAB hA
  exact hA.trans (Finset.map_subset_map.mpr hAB)

end

end PottsContinuity.Thm3.Prop4
