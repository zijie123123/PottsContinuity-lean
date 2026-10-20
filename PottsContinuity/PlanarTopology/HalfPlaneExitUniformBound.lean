module

public import PottsContinuity.PlanarTopology.HalfPlaneExitFKG
public import PottsContinuity.PlanarTopology.InfiniteHitProbability
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite Filter Topology
noncomputable section

/-- DRT's actual first-exit bound, uniformly over all vertical translates
and all horizontal centers for which the complete marked box lies in the half-plane. -/
theorem halfPlaneExitEvent_translated_box_lower_bound
    (μ : Measure LatticeConfiguration)
    (htranslation : ∀ a : LatticeVertex, μ.map (latticeConfigurationTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster ω)
    (s : ℕ) (m t : ℤ) (hm : (s : ℤ) ≤ m) :
    μ (infiniteHit (latticeBox (0,0) s : Set LatticeVertex)) ^ 2 ≤
      μ (halfPlaneExitEvent (latticeTranslate (m,t) '' (latticeBox (0,0) s : Set LatticeVertex)) Set.univ) := by
  let S := latticeTranslate (m,t) '' (latticeBox (0,0) s : Set LatticeVertex)
  have hS : ∀ u ∈ S, 0 ≤ u.1 := by
    rintro u ⟨z,hz,rfl⟩
    have hh := (mem_latticeBox (0,0) z s).mp hz
    change 0 ≤ z.1+m
    simp only [zero_sub,zero_add] at hh
    omega
  have hT : ∀ v ∈ latticeTranslate (-2*m-1,0) '' S, v.1 ≤ -1 := by
    rintro v ⟨u,⟨z,hz,rfl⟩,rfl⟩
    have hh := (mem_latticeBox (0,0) z s).mp hz
    change (z.1+m)+(-2*m-1) ≤ -1
    simp only [zero_sub,zero_add] at hh
    omega
  have hh := halfPlaneExitEvent_ge_infiniteHit_square_of_translate
    μ hFKG hunique S (-2*m-1,0) (htranslation _) hS hT
  rw [measure_infiniteHit_translate μ (m,t) (htranslation _) (latticeBox (0,0) s : Set LatticeVertex)] at hh
  exact hh

end
end PottsContinuity.PlanarTopology
