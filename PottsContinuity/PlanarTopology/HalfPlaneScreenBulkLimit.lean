module

public import PottsContinuity.PlanarTopology.HalfPlaneScreenProbability
public import PottsContinuity.PlanarTopology.HalfPlaneBalancedExits
public import PottsContinuity.PlanarTopology.HalfPlaneExitUniformBound
public import PottsContinuity.PlanarTopology.HalfPlaneLocalProbability
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Int.Star
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite Filter Topology
open scoped ENNReal
noncomputable section

/-- A fixed marked-box hitting probability gives a screen bound by moving
balanced first-exit sources into the bulk. The dual law is the actual pushforward. -/
theorem halfPlane_screen_lower_bound_of_dualLaw
    (μ ν : Measure LatticeConfiguration) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : μ.map wholePlaneDualConfigurationHomeomorph = ν)
    (htranslation : ∀ a : LatticeVertex, ν.map (edgeTranslate a) = ν)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → ν A * ν B ≤ ν (A ∩ B))
    (hunique : ∀ᵐ ω ∂ν, atMostOneInfiniteCluster ω)
    (s : ℕ) (r : ℝ)
    (hr : r < 1-Real.sqrt (1-(ν.real (infiniteHit (latticeBox (0,0) s : Set LatticeVertex)))^2)) :
    2*r-1 ≤ μ.real halfPlaneFiniteUnitEvent := by
  classical
  let K := latticeBox (0,0) s
  let F := K ∪ K.image (latticeTranslate (0,2))
  let m := fun n : ℕ => (s : ℤ)+(n : ℤ)
  let S := fun n : ℕ => latticeTranslate (m n,0) '' (K : Set LatticeVertex)
  have hbal (n : ℕ) : ∃ j : ℤ,
      r < ν.real (halfPlaneExitEvent (latticeTranslate (0,j) '' S n) {y : ℤ | y ≤ -1}) ∧
      r < ν.real (halfPlaneExitEvent (latticeTranslate (0,j+2) '' S n) {y : ℤ | 1 ≤ y}) := by
    apply halfPlaneExitEvent_opposite_translated_balancing ν htranslation hFKG (S n) r
    have hh := halfPlaneExitEvent_translated_box_lower_bound ν htranslation hFKG hunique s (m n) 0
      (by dsimp [m]; omega)
    have hhR := ENNReal.toReal_mono (measure_ne_top ν _) hh
    have hhR' : (ν.real (infiniteHit (K : Set LatticeVertex)))^2 ≤
        ν.real (halfPlaneExitEvent (S n) Set.univ) := by
      simpa only [Measure.real_def,ENNReal.toReal_pow] using hhR
    exact hr.trans_le (by gcongr)
  choose j hj using hbal
  let U := fun n : ℕ => (F.image (latticeTranslate (m n,j n)) : Set LatticeVertex)
  have hlo (n : ℕ) : latticeTranslate (0,j n) '' S n ⊆ U n := by
    rintro z ⟨v,⟨w,hw,rfl⟩,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨w,Finset.mem_union_left _ hw,?_⟩
    ext <;> simp [latticeTranslate]
  have hhi (n : ℕ) : latticeTranslate (0,j n+2) '' S n ⊆ U n := by
    rintro z ⟨v,⟨w,hw,rfl⟩,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨latticeTranslate (0,2) w,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w,hw,rfl⟩),?_⟩
    ext <;> simp [latticeTranslate]; ring
  have hm : Tendsto m atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    obtain ⟨N,hN⟩ := exists_nat_ge b
    filter_upwards [eventually_ge_atTop N] with n hn
    dsimp [m]
    omega
  have hlocal := halfPlaneLocalUniquenessEvent_probability_tendsto_one ν htranslation hunique F m j hm
  have hlocalR : Tendsto (fun n : ℕ => ν.real (halfPlaneLocalUniquenessEvent (U n))) atTop (𝓝 1) := by
    have h := ENNReal.continuousAt_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤) |>.tendsto.comp hlocal
    simpa only [Function.comp_def,ENNReal.toReal_one,Measure.real_def,U] using h
  have hlim : Tendsto (fun n : ℕ => 2*r + ν.real (halfPlaneLocalUniquenessEvent (U n))-2)
      atTop (𝓝 (2*r-1)) := by
    convert (tendsto_const_nhds.add hlocalR).sub_const 2 using 1; congr 1; ring
  apply le_of_tendsto hlim
  filter_upwards [] with n
  have hh := halfPlane_screen_probability_lower_bound_of_dualLaw μ ν hν
    (latticeTranslate (0,j n) '' S n) (latticeTranslate (0,j n+2) '' S n) (U n) (hlo n) (hhi n)
  have h₁ := (hj n).1
  have h₂ := (hj n).2
  linarith

end
end PottsContinuity.PlanarTopology
