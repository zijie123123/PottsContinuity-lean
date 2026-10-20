module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.NativeWindowEventTransport
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.ActualResidualProbabilityChain

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK RSW Exploration MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The one-window bound on the ACTUAL stopped native sample. All source
record, carrier, partition and event-transport inputs are discharged. -/
theorem lemma4_actual_native_window_noncrossing_lower
    (n : ℕ) (hn : 1 ≤ n) (q : Set.Ici (1:ℝ))
    (A : Configuration (lemma4AmbientGraph n)) (hA : A ∈ lemma4BandConstructionEvent n) (j : Fin 3) :
    1/(1+(q:ℝ)^2) ≤
      (measure (edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n A))
        (selfDualParameters q) (frozenBoundary (BoundaryCondition.free ∅)
          (revealRecordConfiguration (lemma4JointSourceReveal n) A).val)
        (nativePrimalWindowNoncrossing (box (56*n)) (lemma4JointSourceReveal n A)
          ((10*(j:ℤ)-13)*(n:ℤ)) ((10*(j:ℤ)-7)*(n:ℤ)) (-3*(n:ℤ)) (3*(n:ℤ)))).toReal := by
  have hcmp := embedded_decreasing_comparison_of_frozen_partition
    (lemma4ActiveNativeWindowGraph n A j)
    (edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n A))
    (lemma4ActiveNativeWindowEmbedding n A j) (lemma4ActiveNativeWindowGraph_map_le n A j)
    (selfDualParameters q) (frozenBoundary (BoundaryCondition.free ∅)
      (revealRecordConfiguration (lemma4JointSourceReveal n) A).val)
    (BoundaryCondition.wired (lemma4ActiveNativeWindowSides n A j))
    (lemma4ActiveNativeWindowHorizontalCrossing n A j)ᶜ
    (lemma4ActiveNativeWindowHorizontalCrossing_isUpperSet n A j).compl
    (lemma4_actual_native_window_induced_partition_le_joined_sides n hn A hA j)
  apply (lemma4_active_native_window_noncrossing_lower n hn q A j).trans
  apply hcmp.trans
  apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono _)
  intro C hC
  exact lemma4_active_noncrossing_implies_native_noncrossing n hn A j C hC

/-- The exact record-free band estimate used in the final recurrence of Lemma 4. -/
theorem lemma4_band_to_square_bound (q : Set.Ici (1:ℝ)) :
    ∀ n : ℕ, 1 ≤ n →
      (measure (lemma4AmbientGraph n) (selfDualParameters q) (BoundaryCondition.free ∅)
        (lemma4BandConstructionEvent n)).toReal ≤
        (1+(q:ℝ)^2)^3 * (annulusProbability (selfDualParameters q) 8 n)^2 := by
  intro n hn
  exact lemma4_band_to_square_bound_of_nativeWindowBounds n hn q
    (fun A hA j => lemma4_actual_native_window_noncrossing_lower n hn q A hA j)

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
