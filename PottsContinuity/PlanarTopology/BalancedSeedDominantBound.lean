module

public import PottsContinuity.PlanarTopology.BalancedCellLeftEscape
public import PottsContinuity.BD12.KSTFiniteAssociation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite BD12 Filter Topology
noncomputable section

theorem rectangleSeed_subset_rectangle (W H s : ℕ) (v : Fin (W+1) × Fin (H+1)) :
    (latticeRectangle ((v.1.val:ℤ),(v.2.val:ℤ)) s s : Set LatticeVertex) ⊆
      latticeRectangle (0,0) (W+s) (H+s) := by
  intro z hz
  have hz := (mem_latticeRectangle _ z s s).mp hz
  apply (mem_latticeRectangle (0,0) z (W+s) (H+s)).mpr
  have hx := v.1.isLt
  have hy := v.2.isLt
  dsimp at *
  omega

/-- The dominant Left/Bottom probability obeys the finite fourth-root trick
at every balanced anchor, with the same translated infinite core as input. -/
theorem balanced_seed_dominant_complement_pow_four
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (W H r : ℕ) (v x y : Fin (W+1) × Fin (H+1))
    (hc : RectangleSeedBalancedCell μ W H (2*r+2) v x y) :
    (1-max (rectangleSeedLeftProbability μ W H (2*r+2) v)
      (rectangleSeedBottomProbability μ W H (2*r+2) v))^4 ≤
      1-μ.real (infiniteHit (latticeBox (0,0) r : Set LatticeVertex)) := by
  let s := 2*r+2
  let C := (latticeBox ((v.1.val:ℤ)+(r:ℤ)+1,(v.2.val:ℤ)+(r:ℤ)+1) r : Set LatticeVertex)
  let V := (latticeRectangle ((v.1.val:ℤ),(v.2.val:ℤ)) s s : Set LatticeVertex)
  let F : Fin 4 → Set LatticeConfiguration := ![
    rectangleSeedConnectionEvent W H s v {z | z.1 = 0},
    rectangleSeedConnectionEvent W H s v {z | z.1 = ((W+s:ℕ):ℤ)},
    rectangleSeedConnectionEvent W H s v {z | z.2 = 0},
    rectangleSeedConnectionEvent W H s v {z | z.2 = ((H+s:ℕ):ℤ)}]
  have hm : ∀ i, MeasurableSet (F i) := by
    intro i; fin_cases i <;> exact rectangleConnectionEvent_measurableSet _ _ _ _ _
  have hu : ∀ i, IsUpperSet (F i) := by
    intro i; fin_cases i <;> exact rectangleConnectionEvent_isUpperSet _ _ _ _ _
  have hcover : infiniteHit C ⊆ ⋃ i, F i := by
    have hCV : C ⊆ V := latticeBox_core_subset_seed r ((v.1.val:ℤ),(v.2.val:ℤ))
    intro ω hω
    have hh := infiniteHit_subset_rectangle_four_seed_union (0,0) (W+s) (H+s)
      C V V V V (hCV.trans (rectangleSeed_subset_rectangle W H s v)) hCV hCV hCV hCV hω
    simp only [zero_add] at hh
    rcases hh with ((hh | hh) | hh) | hh
    · exact Set.mem_iUnion.mpr ⟨0,hh⟩
    · exact Set.mem_iUnion.mpr ⟨1,hh⟩
    · exact Set.mem_iUnion.mpr ⟨2,hh⟩
    · exact Set.mem_iUnion.mpr ⟨3,hh⟩
  have hreal : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B) := by
    intro A B hA hB hAu hBu
    simpa only [Measure.real_def,ENNReal.toReal_mul] using
      ENNReal.toReal_mono (measure_ne_top μ _) (hFKG A B hA hB hAu hBu)
  obtain ⟨i,hi⟩ := kst_finite_cover_square_root μ hreal F hm hu hcover
  have hdom : μ.real (F i) ≤ max (rectangleSeedLeftProbability μ W H s v)
      (rectangleSeedBottomProbability μ W H s v) := by
    fin_cases i
    · exact le_max_left _ _
    · exact hc.left_ge_right.trans (le_max_left _ _)
    · exact le_max_right _ _
    · exact hc.bottom_ge_top.trans (le_max_right _ _)
  have hnonneg : 0 ≤ 1-max (rectangleSeedLeftProbability μ W H s v)
      (rectangleSeedBottomProbability μ W H s v) := by
    exact sub_nonneg.mpr (max_le measureReal_le_one measureReal_le_one)
  have hp := pow_le_pow_left₀ hnonneg (sub_le_sub_left hdom 1) 4
  have heq := congrArg ENNReal.toReal (measure_infiniteHit_latticeBox_translate μ
    ((v.1.val:ℤ)+(r:ℤ)+1,(v.2.val:ℤ)+(r:ℤ)+1) (htranslation _) r)
  change μ.real (infiniteHit C) = _ at heq
  simpa only [Fintype.card_fin,heq,s,Measure.real_def] using hp.trans hi

end
end PottsContinuity.PlanarTopology
