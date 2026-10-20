module

public import PottsContinuity.Thm3.Prop4.TubeExitHeights

/-!
# Source-oriented upper and lower exit arcs

The source regions use the integer signed area. The affine height and its
sign are identified exactly, so the first-exit estimates consume the actual
one-sided region condition on the given open path.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

/-- Integer signed area agrees exactly with horizontal length times affine deviation. -/
theorem tubeLineOffset_eq_horizontal_mul_deviation (u v z : LatticeVertex) (t b : ℝ)
    (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b) :
    (tubeLineOffset u v z : ℝ) = ((v.1 : ℝ)-u.1)*((z.2 : ℝ)-(t*z.1+b)) := by
  unfold tubeLineOffset
  push_cast
  rw [hu,hv]
  ring

/-- For a left-to-right segment, the source area sign is the affine height sign. -/
theorem tubeLineOffset_nonneg_iff_deviation (u v z : LatticeVertex) (t b : ℝ)
    (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b) (hdir : u.1 < v.1) :
    0 ≤ tubeLineOffset u v z ↔ 0 ≤ (z.2 : ℝ)-(t*z.1+b) := by
  have hdirR : (0 : ℝ) < (v.1 : ℝ)-u.1 := by exact_mod_cast sub_pos.mpr hdir
  have heq := tubeLineOffset_eq_horizontal_mul_deviation u v z t b hu hv
  have hcast : 0 ≤ tubeLineOffset u v z ↔ (0 : ℝ) ≤ (tubeLineOffset u v z : ℝ) := by
    exact_mod_cast Iff.rfl
  rw [hcast,heq]
  exact mul_nonneg_iff_of_pos_left hdirR

/-- The lower source region has exactly the corresponding nonpositive height. -/
theorem tubeLineOffset_nonpos_iff_deviation (u v z : LatticeVertex) (t b : ℝ)
    (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b) (hdir : u.1 < v.1) :
    tubeLineOffset u v z ≤ 0 ↔ (z.2 : ℝ)-(t*z.1+b) ≤ 0 := by
  have hdirR : (0 : ℝ) < (v.1 : ℝ)-u.1 := by exact_mod_cast sub_pos.mpr hdir
  have heq := tubeLineOffset_eq_horizontal_mul_deviation u v z t b hu hv
  have hcast : tubeLineOffset u v z ≤ 0 ↔ (tubeLineOffset u v z : ℝ) ≤ (0 : ℝ) := by
    exact_mod_cast Iff.rfl
  rw [hcast,heq]
  exact ⟨fun h => nonpos_of_mul_nonpos_right h hdirR,
    fun h => mul_nonpos_of_nonneg_of_nonpos hdirR.le h⟩

end
end PottsContinuity.Thm3.Prop4
