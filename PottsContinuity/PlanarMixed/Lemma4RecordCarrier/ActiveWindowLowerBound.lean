module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.NativeWindowReferenceEmbedding
public import PottsContinuity.PlanarMixed.EmbeddedOpenRestriction
public import PottsContinuity.Thm3.RSW.EmbeddedComparison

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK Square RSW MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Actual horizontal connection on the active native window carrier. -/
def lemma4ActiveNativeWindowHorizontalCrossing
    (n : ℕ) (A : Configuration (lemma4AmbientGraph n)) (j : Fin 3) :
    Set (Configuration (lemma4ActiveNativeWindowGraph n A j)) :=
  {C | ∃ u v : lemma4ActiveNativeWindowVertex n A j,
    u.val.val.1=(10*(j:ℤ)-13)*(n:ℤ) ∧ v.val.val.1=(10*(j:ℤ)-7)*(n:ℤ) ∧
      ActualConnected _ C u v}

theorem lemma4ActiveNativeWindowHorizontalCrossing_isUpperSet
    (n : ℕ) (A : Configuration (lemma4AmbientGraph n)) (j : Fin 3) :
    IsUpperSet (lemma4ActiveNativeWindowHorizontalCrossing n A j) := by
  rintro C D hCD ⟨u,v,hu,hv,hconn⟩
  exact ⟨u,v,hu,hv,actualConnected_mono hCD hconn⟩

/-- A crossing in the restricted active sample is an actual reference crossing. -/
theorem lemma4_active_window_crossing_implies_reference_crossing
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n)) (j : Fin 3)
    (C : Configuration (lemma4ReferenceCoreGraph n))
    (hC : embeddedConfigurationRestriction (lemma4ActiveNativeWindowGraph n A j)
      (lemma4ReferenceCoreGraph n) (lemma4ActiveWindowCoreEmbedding n hn A j)
      (lemma4ActiveWindowCoreGraph_map_le n hn A j) C ∈ lemma4ActiveNativeWindowHorizontalCrossing n A j) :
    C ∈ referenceDualCoreHorizontalCrossing (-3*(n:ℤ)+1) (6*n-1) := by
  obtain ⟨u,v,hu,hv,hconn⟩ := hC
  refine ⟨lemma4ActiveWindowCoreEmbedding n hn A j u,lemma4ActiveWindowCoreEmbedding n hn A j v,?_,?_,?_⟩
  · change u.val.val.1-(10*(j:ℤ)-10)*(n:ℤ)=(-3*(n:ℤ)+1)-1
    fin_cases j <;> dsimp at hu ⊢ <;> omega
  · change v.val.val.1-(10*(j:ℤ)-10)*(n:ℤ)=(-3*(n:ℤ)+1)+((6*n-1:ℕ):ℤ)
    fin_cases j <;> dsimp at hv ⊢ <;> omega
  · exact hconn.map (embeddedOpenRestrictionHom _ _ _ (lemma4ActiveWindowCoreGraph_map_le n hn A j) C)

/-- The ACTUAL active native window with joined vertical sides has the full
square lower bound. Deleting arbitrary queried edges only improves noncrossing. -/
theorem lemma4_active_native_window_noncrossing_lower
    (n : ℕ) (hn : 1 ≤ n) (q : Set.Ici (1:ℝ))
    (A : Configuration (lemma4AmbientGraph n)) (j : Fin 3) :
    1/(1+(q:ℝ)^2) ≤
      (measure (lemma4ActiveNativeWindowGraph n A j) (selfDualParameters q)
        (BoundaryCondition.wired (lemma4ActiveNativeWindowSides n A j))
        (lemma4ActiveNativeWindowHorizontalCrossing n A j)ᶜ).toReal := by
  let J := lemma4ActiveNativeWindowGraph n A j
  let H := lemma4ReferenceCoreGraph n
  let g := lemma4ActiveWindowCoreEmbedding n hn A j
  let ξ := BoundaryCondition.wired {u : lemma4ReferenceCoreVertex n |
    rectangleDualHorizontalCoreInclusion (-3*(n:ℤ)+1,-3*(n:ℤ)+1) (6*n-1) (6*n-1) u ∈
      rectangleDoubleCollarDualInnerVerticalSides (-3*(n:ℤ)+1,-3*(n:ℤ)+1) (6*n-1) (6*n-1)}
  let S := lemma4ActiveNativeWindowHorizontalCrossing n A j
  let read := embeddedConfigurationRestriction J H g (lemma4ActiveWindowCoreGraph_map_le n hn A j)
  have hcmp := embedded_boundary_probability_le J H g (lemma4ActiveWindowCoreGraph_map_le n hn A j)
    (selfDualParameters q) ξ S (lemma4ActiveNativeWindowHorizontalCrossing_isUpperSet n A j)
  rw [lemma4ActiveWindowCore_boundary_pullback] at hcmp
  have hcomp : (measure H (selfDualParameters q) ξ (read ⁻¹' S)ᶜ).toReal ≤
      (measure J (selfDualParameters q) (BoundaryCondition.wired (lemma4ActiveNativeWindowSides n A j)) Sᶜ).toReal := by
    change (measure J _ _).real S ≤ (measure H _ _).real (read ⁻¹' S) at hcmp
    change (measure H _ _).real (read ⁻¹' S)ᶜ ≤ (measure J _ _).real Sᶜ
    rw [probReal_compl_eq_one_sub (MeasurableSpace.measurableSet_top : MeasurableSet _),
      probReal_compl_eq_one_sub (MeasurableSpace.measurableSet_top : MeasurableSet _)]
    linarith
  have hsub : (referenceDualCoreHorizontalCrossing (-3*(n:ℤ)+1) (6*n-1))ᶜ ⊆ (read ⁻¹' S)ᶜ := by
    intro C hC hS
    exact hC (lemma4_active_window_crossing_implies_reference_crossing n hn A j C hS)
  exact (referenceDualCore_noncrossing_lower q (-3*(n:ℤ)+1) (6*n-1) (by omega)).trans
    ((ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans hcomp)

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
