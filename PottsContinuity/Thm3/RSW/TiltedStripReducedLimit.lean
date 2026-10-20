module

public import PottsContinuity.Thm3.RSW.TiltedStripMarginalFiniteWindow
public import PottsContinuity.Thm3.RSW.TiltedStripReducedReads

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK Thm3.Prop4 MeasureTheory Filter Topology
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Every clopen original-strip event converges under all admissible boundaries. -/
theorem selfDual_tiltedStrip_clopen_tendsto
    (q : Set.Ici (1 : ℝ)) (N : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (ξ : ∀ M : ℕ, BoundaryCondition (tiltedWindow N M t : Set (ℤ × ℤ)))
    (htop : ∀ M, (tiltedWindowBoundary N M t 0).partition ≤ (ξ M).partition)
    (hlateral : ∀ M, (ξ M).boundary ⊆ tiltedWindowWiredVertices N M t 1)
    (E : Set (TiltedConfiguration N t)) (hcl : IsClopen E) :
    Tendsto (fun M =>
      (measure (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ)))
        (selfDualParameters q) (ξ M) {C | tiltedStripWindowOriginalRead N t M C ∈ E}).toReal)
      atTop (𝓝 ((selfDualTiltedStripMeasure q N t).real E)) := by
  let θ := selfDualParameters q
  obtain ⟨ν,hν,_⟩ := tiltedWindowPlaneProbabilityMeasure_top_existsUnique_limit θ N t
  have heq : (ν.map (tiltedPlaneRestriction N t)).toMeasure = selfDualTiltedStripMeasure q N t :=
    isTiltedStripLimit_unique θ N t 0 _ _
      (isTiltedStripLimit_of_plane_tendsto θ N t 0 ν hν)
      (selfDualTiltedStripMeasure_isLimit q N t)
  have hplane : IsClopen ((tiltedPlaneRestriction N t) ⁻¹' E) :=
    hcl.preimage (tiltedPlaneRestriction_continuous N t)
  have hconv := tiltedBoundaryPlane_tendsto θ N t (abs_le.mpr ht) ξ htop hlateral ν hν
  have hNN := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hconv hplane
  have hreal : Tendsto (fun M =>
      (tiltedBoundaryPlaneProbabilityMeasure θ N M t (ξ M)).toMeasure.real
        ((tiltedPlaneRestriction N t) ⁻¹' E)) atTop
      (𝓝 (ν.toMeasure.real ((tiltedPlaneRestriction N t) ⁻¹' E))) := by
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn,Function.comp_def] using
      NNReal.continuous_coe.continuousAt.tendsto.comp hNN
  have hmass : ν.toMeasure.real ((tiltedPlaneRestriction N t) ⁻¹' E) =
      (selfDualTiltedStripMeasure q N t).real E := by
    rw [← heq]
    change _ = (ν.toMeasure.map (tiltedPlaneRestriction N t)).real E
    simp only [Measure.real,Measure.map_apply (tiltedPlaneRestriction_continuous N t).measurable
      hcl.isOpen.measurableSet]
  rw [hmass] at hreal
  have hterm (M : ℕ) :
      (tiltedBoundaryPlaneProbabilityMeasure θ N M t (ξ M)).toMeasure.real
        ((tiltedPlaneRestriction N t) ⁻¹' E) =
      (measure (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ))) θ (ξ M)
        {C | tiltedStripWindowOriginalRead N t M C ∈ E}).toReal := by
    rw [Measure.real,tiltedBoundaryPlane_apply θ N M t (ξ M) _ hplane.isOpen.measurableSet]
    rfl
  simpa only [hterm] using hreal


end
end PottsContinuity.RSW
