module

public import PottsContinuity.PlanarTopology.HalfPlaneExitBalance
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite
noncomputable section

/-- The adjacent balancing locations give opposite actual exterior targets
with source sets separated vertically by two lattice units. -/
theorem halfPlaneExitEvent_opposite_translated_balancing
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (S : Set LatticeVertex) (r : ℝ)
    (hr : r < 1-Real.sqrt (1-μ.real (halfPlaneExitEvent S Set.univ))) :
    ∃ j : ℤ,
      r < μ.real (halfPlaneExitEvent (latticeTranslate (0,j) '' S) {y : ℤ | y ≤ -1}) ∧
      r < μ.real (halfPlaneExitEvent (latticeTranslate (0,j+2) '' S) {y : ℤ | 1 ≤ y}) := by
  obtain ⟨j,hlo,hhi⟩ := halfPlaneExitEvent_adjacent_balancing μ hFKG S r hr
  have hL : (fun y : ℤ => y+j) '' {y : ℤ | y ≤ -j-1} = {y : ℤ | y ≤ -1} := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      change x ≤ -j-1 at hx
      change x+j ≤ -1
      omega
    · intro hy
      exact ⟨y-j,(by change y-j ≤ -j-1; change y ≤ -1 at hy; omega),by dsimp; omega⟩
  have hR : (fun y : ℤ => y+(j+2)) '' {y : ℤ | -(j+1) ≤ y} = {y : ℤ | 1 ≤ y} := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      change -(j+1) ≤ x at hx
      change 1 ≤ x+(j+2)
      omega
    · intro hy
      exact ⟨y-(j+2),(by change -(j+1) ≤ y-(j+2); change 1 ≤ y at hy; omega),by dsimp; omega⟩
  have h₁ := measure_halfPlaneExitEvent_vertical_translate μ j (htranslation _) S {y : ℤ | y ≤ -j-1}
  have h₂ := measure_halfPlaneExitEvent_vertical_translate μ (j+2) (htranslation _) S {y : ℤ | -(j+1) ≤ y}
  rw [hL] at h₁
  rw [hR] at h₂
  refine ⟨j,?_,?_⟩
  · simpa only [Measure.real_def,h₁] using hlo
  · simpa only [Measure.real_def,h₂] using hhi

end
end PottsContinuity.PlanarTopology
