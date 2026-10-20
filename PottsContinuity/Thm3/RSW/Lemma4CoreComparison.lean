module

public import PottsContinuity.Thm3.RSW.Lemma4SymmetricReferenceRectangle
public import PottsContinuity.Thm3.RSW.RectangleOneColumnComparison
public import PottsContinuity.Thm3.RSW.Lemma4CollarCoreBandProbability

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality PD.RCInfinite MeasureTheory
noncomputable section

/-- The exact symmetric reference lower bound for the actual residual-dual
band. All collar, core, free-leaf, event and one-column comparisons are proved. -/
theorem lemma4_symmetric_reference_le_nativeDualBand (q : Set.Ici (1:ℝ))
    (n : ℕ) (hn : 2 ≤ n) :
    selfDualTopWiredCrossingProbability q
      ((56*(n:ℝ)+1)/(n-1:ℕ)) ((54*(n:ℝ))/(n-1:ℕ)) (n-1) ≤
    (measure (bottomCollarInducedDualGraph (-56*(n:ℤ),0) (112*n) (54*n))
      (selfDualParameters q)
      (rectangleDualBoundaryCondition (-56*(n:ℤ),-1) (112*n) (54*n+1))
      (lemma4NativeDualBandEvent n)).toReal := by
  have hc := rectangle_one_column_crossing_comparison (selfDualParameters q)
    (-56*(n:ℤ)-1,0) (112*n+1) (54*n) (n-1) (by omega)
  have hl := lemma4_nativeBand_probability_ge_asymmetricRectangle (selfDualParameters q) n (by omega)
  rw [rectangleBandConnectionEvent_eq_finiteBoolEvent] at hl
  have hright : -56*(n:ℤ)-1+((112*n+1+1:ℕ):ℤ) = 56*(n:ℤ)+1 := by omega
  have hsmall : -56*(n:ℤ)-1+((112*n+1:ℕ):ℤ) = -56*(n:ℤ)+((112*n:ℕ):ℤ) := by omega
  simp only [zero_add,hright,hsmall] at hc hl
  rw [lemma4_symmetric_reference_eq_canonical q n hn]
  exact hc.trans hl

end
end PottsContinuity.RSW
