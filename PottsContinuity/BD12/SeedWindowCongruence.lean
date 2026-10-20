module

public import PottsContinuity.BD12.SeedWindowMeasurability

/-! Exact dependence of finite independent seed windows on their original-input
laws. Pins outside the sampled window do not alter the law. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section

/-- Only the actual auxiliary laws at sampled times affect the seed window. -/
theorem finiteHybridSeedWindow_congr_aux (c d : ℕ) (U W : ℕ → ℝ)
    (background : ℕ → ℝ × ℝ) (start n : ℕ)
    (h : ∀ i, start ≤ i → i < start + n → finiteHybridAuxLaw c U i = finiteHybridAuxLaw d W i) :
    finiteHybridSeedWindow c U background start n =
      finiteHybridSeedWindow d W background start n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [finiteHybridSeedWindow]
    rw [h start le_rfl (by omega), ih (start + 1) (fun i hi hn => h i (by omega) (by omega))]

/-- Once all future original inputs are fresh, the earlier pin values and
pin count have no effect on the remaining seed window. -/
theorem finiteHybridSeedWindow_fresh (c d : ℕ) (U W : ℕ → ℝ)
    (background : ℕ → ℝ × ℝ) (start n : ℕ) (hc : c ≤ start) (hd : d ≤ start) :
    finiteHybridSeedWindow c U background start n =
      finiteHybridSeedWindow d W background start n := by
  apply finiteHybridSeedWindow_congr_aux
  intro i hi _
  simp only [finiteHybridAuxLaw, Nat.not_lt.mpr (hc.trans hi),
    Nat.not_lt.mpr (hd.trans hi), ite_false]

/-- The extra pin at c is outside any future window starting strictly after c. -/
theorem finiteHybridSeedWindow_pin_before (c : ℕ) (U : ℕ → ℝ)
    (background : ℕ → ℝ × ℝ) (start n : ℕ) (hc : c < start) (u : ℝ) :
    finiteHybridSeedWindow (c + 1) (Function.update U c u) background start n =
      finiteHybridSeedWindow c U background start n :=
  finiteHybridSeedWindow_fresh _ _ _ _ _ _ _ (by omega) hc.le

end
end PottsContinuity.BD12
