module

public import PottsContinuity.PlanarTopology.BalancedSeedCell
public import PottsContinuity.PlanarTopology.SeedSquareCore
public import PottsContinuity.PlanarTopology.CommonCoreBoundaryBound
public import PottsContinuity.PlanarTopology.RectangleHalfPlaneArmBound
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite BD12
noncomputable section

/-- A balanced cell near Left forces its common infinite-root probability to
be small. All three actual seed squares have side 2r+2; the bound is uniform
in the vertical anchor and rectangle dimensions. -/
theorem balanced_cell_near_left_core_probability_le_four_arms_of_three_comparisons
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (W H M r N : ℕ) (hW : N < W) (hH : 2*N+2 < H)
    (v x y : Fin (W+1) × Fin (H+1))
    (hbottom : rectangleSeedTopProbability μ W H (2*r+2) v ≤ rectangleSeedBottomProbability μ W H (2*r+2) v)
    (hrightComparison : rectangleSeedLeftProbability μ W H (2*r+2) x ≤ rectangleSeedRightProbability μ W H (2*r+2) x)
    (htop : rectangleSeedBottomProbability μ W H (2*r+2) y ≤ rectangleSeedTopProbability μ W H (2*r+2) y)
    (hx₁ : x.1.val ≤ v.1.val+1 ∧ v.1.val ≤ x.1.val+1)
    (hx₂ : x.2.val ≤ v.2.val+1 ∧ v.2.val ≤ x.2.val+1)
    (hy₁ : y.1.val ≤ v.1.val+1 ∧ v.1.val ≤ y.1.val+1)
    (hy₂ : y.2.val ≤ v.2.val+1 ∧ v.2.val ≤ y.2.val+1)
    (hnear : v.1.val ≤ M) :
    μ.real (infiniteHit (latticeBox ((v.1.val:ℤ)+(r:ℤ)+1,(v.2.val:ℤ)+(r:ℤ)+1) r : Set LatticeVertex)) ≤
      4 * μ.real (sampledGraphArmEvent
        (fun ω => (PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1})
        (halfPlaneRectangleSeeds (M+1+(2*r+2)) (2*r+2)) {z | z.val ∈ latticeBox (0,0) N}) := by
  let s := 2*r+2
  let A := fun a : Fin (W+1) × Fin (H+1) => ((a.1.val:ℤ),(a.2.val:ℤ))
  let S := fun a => (latticeRectangle (A a) s s : Set LatticeVertex)
  let C := (latticeBox ((v.1.val:ℤ)+(r:ℤ)+1,(v.2.val:ℤ)+(r:ℤ)+1) r : Set LatticeVertex)
  let P := μ.real (sampledGraphArmEvent
    (fun ω => (PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1})
    (halfPlaneRectangleSeeds (M+1+s) s) {z | z.val ∈ latticeBox (0,0) N})
  have hSv : C ⊆ S v := latticeBox_core_subset_seed r (A v)
  have hSx : C ⊆ S x := by
    apply latticeBox_core_subset_nearby_seed r (A v) (A x)
    · dsimp [A]
      exact_mod_cast hx₁
    · dsimp [A]
      exact_mod_cast hx₂
  have hSy : C ⊆ S y := by
    apply latticeBox_core_subset_nearby_seed r (A v) (A y)
    · dsimp [A]
      exact_mod_cast hy₁
    · dsimp [A]
      exact_mod_cast hy₂
  have hdom : S v ⊆ latticeRectangle (0,0) (W+s) (H+s) := by
    intro z hz
    have hz' := (mem_latticeRectangle (A v) z s s).mp hz
    apply (mem_latticeRectangle (0,0) z (W+s) (H+s)).mpr
    have hvx := v.1.isLt
    have hvy := v.2.isLt
    dsimp [A] at hz'
    dsimp only [Prod.fst_zero,Prod.snd_zero]
    omega
  have hvM : v.1.val ≤ M+1 := by omega
  have hxM : x.1.val ≤ M+1 := by have hh := hx₁; omega
  have hyM : y.1.val ≤ M+1 := by have hh := hy₁; omega
  have harm (a : Fin (W+1) × Fin (H+1)) (ha : a.1.val ≤ M+1)
      (T : Set LatticeVertex) (hT : ∀ z ∈ T, (z.1,z.2-(a.2.val:ℤ)) ∉ latticeBox (0,0) N) :
      μ.real (rectangleSeedConnectionEvent W H s a T) ≤ P := by
    exact rectangleConnectionEvent_real_le_halfPlaneArm μ (W+s) (H+s) (M+1) s N
      (a.1.val:ℤ) (a.2.val:ℤ) (by exact_mod_cast ha) (htranslation _) T hT
  have hright (a : Fin (W+1) × Fin (H+1)) (ha : a.1.val ≤ M+1) :
      rectangleSeedRightProbability μ W H s a ≤ P := by
    apply harm a ha
    intro z hz hb
    have hh := (mem_latticeBox (0,0) (z.1,z.2-(a.2.val:ℤ)) N).mp hb
    change z.1 = ((W+s:ℕ):ℤ) at hz
    dsimp only [Prod.fst_zero,Prod.snd_zero,Prod.fst,Prod.snd,zero_sub,zero_add] at hh
    omega
  have hL : rectangleSeedLeftProbability μ W H s x ≤ P := hrightComparison.trans (hright x hxM)
  have hR : rectangleSeedRightProbability μ W H s v ≤ P := hright v hvM
  by_cases hbot : N < v.2.val
  · have hB : rectangleSeedBottomProbability μ W H s v ≤ P := by
      apply harm v hvM
      intro z hz hb
      have hh := (mem_latticeBox (0,0) (z.1,z.2-(v.2.val:ℤ)) N).mp hb
      change z.2 = 0 at hz
      dsimp only [Prod.fst_zero,Prod.snd_zero,Prod.fst,Prod.snd,zero_sub,zero_add] at hh
      omega
    have hT : rectangleSeedTopProbability μ W H s v ≤ P := hbottom.trans hB
    have hh := infiniteHit_real_le_rectangle_four_seed_sum μ (0,0) (W+s) (H+s)
      C (S x) (S v) (S v) (S v) (hSv.trans hdom) hSx hSv hSv hSv
    simp only [zero_add] at hh
    change μ.real (infiniteHit C) ≤ rectangleSeedLeftProbability μ W H s x +
      rectangleSeedRightProbability μ W H s v + rectangleSeedBottomProbability μ W H s v +
      rectangleSeedTopProbability μ W H s v at hh
    change μ.real (infiniteHit C) ≤ 4*P
    linarith
  · have hT : rectangleSeedTopProbability μ W H s y ≤ P := by
      apply harm y hyM
      intro z hz hb
      have hh := (mem_latticeBox (0,0) (z.1,z.2-(y.2.val:ℤ)) N).mp hb
      have hyv := hy₂
      change z.2 = ((H+s:ℕ):ℤ) at hz
      dsimp only [Prod.fst_zero,Prod.snd_zero,Prod.fst,Prod.snd,zero_sub,zero_add] at hh
      omega
    have hB : rectangleSeedBottomProbability μ W H s y ≤ P := htop.trans hT
    have hh := infiniteHit_real_le_rectangle_four_seed_sum μ (0,0) (W+s) (H+s)
      C (S x) (S v) (S y) (S y) (hSv.trans hdom) hSx hSv hSy hSy
    simp only [zero_add] at hh
    change μ.real (infiniteHit C) ≤ rectangleSeedLeftProbability μ W H s x +
      rectangleSeedRightProbability μ W H s v + rectangleSeedBottomProbability μ W H s y +
      rectangleSeedTopProbability μ W H s y at hh
    change μ.real (infiniteHit C) ≤ 4*P
    linarith


/-- A balanced cell near Left forces its common infinite-root probability to
be small. All three actual seed squares have side 2r+2; the bound is uniform
in the vertical anchor and rectangle dimensions. -/
theorem balanced_cell_near_left_core_probability_le_four_arms
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (W H M r N : ℕ) (hW : N < W) (hH : 2*N+2 < H)
    (v x y : Fin (W+1) × Fin (H+1))
    (hcell : RectangleSeedBalancedCell μ W H (2*r+2) v x y) (hnear : v.1.val ≤ M) :
    μ.real (infiniteHit (latticeBox ((v.1.val:ℤ)+(r:ℤ)+1,(v.2.val:ℤ)+(r:ℤ)+1) r : Set LatticeVertex)) ≤
      4 * μ.real (sampledGraphArmEvent
        (fun ω => (PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1})
        (halfPlaneRectangleSeeds (M+1+(2*r+2)) (2*r+2)) {z | z.val ∈ latticeBox (0,0) N}) := by
  exact balanced_cell_near_left_core_probability_le_four_arms_of_three_comparisons
    μ htranslation W H M r N hW hH v x y hcell.bottom_ge_top hcell.right_ge_left
    hcell.top_ge_bottom hcell.right_close_fst hcell.right_close_snd
    hcell.top_close_fst hcell.top_close_snd hnear

end
end PottsContinuity.PlanarTopology
