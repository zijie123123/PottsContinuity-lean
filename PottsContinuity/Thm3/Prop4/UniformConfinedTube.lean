module

public import PottsContinuity.Thm3.Prop4.ContainingDomainTubeConfined

/-!
# Uniform tube-confined bulk crossings under finite wired laws

The domain may be larger than the tube. The crossing witness still stays
inside the tube at every vertex, as required by the next gluing step.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.RCInfinite
noncomputable section

/-- The finite wired domain dominates the actual tube-confined crossing event. -/
theorem wired_containing_domain_confined_crossing_ge_tube (q : Set.Ici (1 : ℝ))
    (μ₁ : Measure LatticeConfiguration)
    (hμ₁ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 1 μ₁)
    (n : ℕ) (R : ℝ) (u v : LatticeVertex) (S : Finset LatticeVertex)
    (hS : radiusTube n R u v ⊆ S) :
    μ₁.real (tubeHorizontalCrossingEvent n R u v) ≤
      (measure (finiteLatticeGraph S) (RSW.selfDualParameters q) (frozenBoundaryCondition S 1)
        (inducedTubeConfinedCrossingEvent S n R u v)).toReal := by
  let : IsProbabilityMeasure μ₁ := hμ₁.1
  let A := inducedTubeConfinedCrossingEvent S n R u v
  let E := Infinite.latticeGraphEvent (finiteLatticeGraph S)
    (finiteDomainEmbedding S) (finiteDomainEmbedding_map_le S) A
  have h := wired_induced_lower_event_le_infinite (RSW.selfDualParameters q) μ₁ hμ₁ S Aᶜ
    (inducedTubeConfinedCrossingEvent_isUpperSet S n R u v).compl
  change (measure _ _ _).real Aᶜ ≤ μ₁.real Eᶜ at h
  have hE : MeasurableSet E := (Infinite.latticeGraphEvent_isCylinder _ _ _ A).measurableSet
  rw [probReal_compl_eq_one_sub MeasurableSpace.measurableSet_top,
    probReal_compl_eq_one_sub hE] at h
  have hincl : μ₁.real (tubeHorizontalCrossingEvent n R u v) ≤ μ₁.real E :=
    measureReal_mono (tube_crossing_subset_containing_domain_confined n R u v S hS) (measure_ne_top _ _)
  change μ₁.real _ ≤ (measure _ _ _).real A
  linarith only [h,hincl]

/-- One cutoff gives an actual tube-confined crossing with probability at least
one half in every containing finite induced wired domain, for every real q>=1. -/
theorem selfDual_wired_containing_domain_confined_crossing_uniform_ge_half
    (c₀ α ε : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ (q : Set.Ici (1 : ℝ)) (μ₀ : Measure LatticeConfiguration),
      IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 0 μ₀ →
      (∀ m : ℕ, 1 ≤ m → RSW.oneArmProbability μ₀ m ≤ Real.exp (-c₀*(m : ℝ)^α)) →
      ∀ n : ℕ, N ≤ n → ∀ u v : LatticeVertex, u ∈ box n → v ∈ box n →
      u.1 = -(n : ℤ) → v.1 = (n : ℤ) →
      ∀ S : Finset LatticeVertex, radiusTube n (4*(n : ℝ)^ε) u v ⊆ S →
      1/2 ≤ (measure (finiteLatticeGraph S) (RSW.selfDualParameters q) (frozenBoundaryCondition S 1)
        (inducedTubeConfinedCrossingEvent S n (4*(n : ℝ)^ε) u v)).toReal := by
  obtain ⟨N,hN,hbulk⟩ := selfDual_wired_tube_crossing_uniform_ge_half c₀ α ε hc₀ hα hε hε1
  refine ⟨N,hN,?_⟩
  intro q μ₀ hμ₀ hdecay n hn u v hu hv ha hb S hS
  obtain ⟨μ₁,⟨hμ₁,_⟩,_⟩ := existsUnique_wired_dual_of_selfDual_free_limit q μ₀ hμ₀
  exact (hbulk q μ₀ μ₁ hμ₀ hμ₁ hdecay n hn u v hu hv ha hb).trans
    (wired_containing_domain_confined_crossing_ge_tube q μ₁ hμ₁ n (4*(n : ℝ)^ε) u v S hS)

end
end PottsContinuity.Thm3.Prop4
