module

public import PottsContinuity.Thm3.Prop4.TiltedIsolationClopen
public import PottsContinuity.Thm3.Prop4.TiltedSelfDual

/-!
# The infinite tilted-strip isolation comparison, eq. (23)

The exact isolation event is clopen by finite incident-edge locality. Its
finite-extension preimage has the proved censored-cluster comparison bound.
Passing through the genuine strip cylinder limit needs no explored dual path.
-/

@[expose] public section

open MeasureTheory Filter Topology
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- Source eq. (23) on the actual infinite strip, for any independent interior parameters. -/
theorem tilted_isolation_probability_le_touch (θ : Parameters) (N n m : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (x : tiltedStripVertices N t)
    (hxheight : tiltedHeight t x.val+(n : ℝ) ≤ N)
    (μ : Measure (TiltedConfiguration N t)) (hμ : IsTiltedStripLimit θ N t 0 μ) :
    μ.real {ω | tiltedTouchIsolationEvent N n m t ω x} ≤ tiltedTouchProbability θ n m t := by
  let E : Set (TiltedConfiguration N t) := {ω | tiltedTouchIsolationEvent N n m t ω x}
  have hE : IsClopen E := isClopen_tiltedTouchIsolationEvent N n m t x
  let P : Set LatticeConfiguration := tiltedPlaneRestriction N t ⁻¹' E
  have hP : IsClopen P := hE.preimage (tiltedPlaneRestriction_continuous N t)
  obtain ⟨ν,hν,_⟩ := tiltedWindowPlaneProbabilityMeasure_top_existsUnique_limit θ N t
  have hmap := isTiltedStripLimit_of_plane_tendsto θ N t 0 ν hν
  have heq := isTiltedStripLimit_unique θ N t 0 μ _ hμ hmap
  have hreal : Tendsto (fun M => (tiltedWindowPlaneProbabilityMeasure θ N t 0 M).toMeasure.real P)
      atTop (𝓝 (ν.toMeasure.real P)) := by
    have h := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hν hP
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn,Function.comp_def] using
      NNReal.continuous_coe.continuousAt.tendsto.comp h
  obtain ⟨R,hxR⟩ := lattice_point_mem_some_box x.val
  have hbound : ∀ᶠ M in atTop,
      (tiltedWindowPlaneProbabilityMeasure θ N t 0 M).toMeasure.real P ≤
        tiltedTouchProbability θ n m t := by
    filter_upwards [eventually_ge_atTop (R+m)] with M hM
    have hc := translatedTiltedWindow_subset_window N n m R M t x.val hxR x.property.1 hxheight hM
    let xM : (tiltedWindow N M t : Set (ℤ × ℤ)) :=
      ⟨x.val,hc (mem_translatedTiltedWindow_self n m t x.val)⟩
    have hpre : {A | tiltedWindowPlaneConfiguration N M t A ∈ P} =
        finiteArcIsolationEvent (translatedWindowDomain N M n m t x.val)
          (translatedWindowArc N M n m t x.val) xM := by
      ext A
      exact tiltedTouchIsolationEvent_closedExtension_iff N M n m t x hc A
    change ((tiltedWindowPlaneProbabilityMeasure θ N t 0 M).toMeasure P).toReal ≤ _
    rw [tiltedWindowPlaneProbabilityMeasure_apply θ N t 0 M P hP.isOpen.measurableSet,hpre]
    exact tilted_finite_isolation_le_touch θ N M n m t ht xM hxheight hc
  have hlimit := le_of_tendsto hreal hbound
  change μ.real E ≤ _
  rw [heq]
  change (ν.toMeasure.map (tiltedPlaneRestriction N t)).real E ≤ _
  unfold Measure.real
  rw [Measure.map_apply (tiltedPlaneRestriction_continuous N t).measurable hE.isOpen.measurableSet]
  exact hlimit

/-- The source comparison at the explicit self-dual value for every real q≥1. -/
theorem selfDual_tilted_isolation_probability_le_touch (q : Set.Ici (1 : ℝ))
    (n m : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) (x : ℤ × ℤ)
    (hx : x ∈ tiltedStripVertices n t) :
    (selfDualTiltedStripMeasure q (2*n) t).real (tiltedIsolationAt (2*n) n m t x) ≤
      tiltedTouchProbability (RSW.selfDualParameters q) n m t := by
  have hxN : x ∈ tiltedStripVertices (2*n) t := by
    constructor
    · exact hx.1
    · have h := hx.2
      push_cast
      linarith only [h]
  have hheight : tiltedHeight t x+(n : ℝ) ≤ (2*n : ℕ) := by
    have h := hx.2
    push_cast
    linarith only [h]
  have hevent : tiltedIsolationAt (2*n) n m t x =
      {ω | tiltedTouchIsolationEvent (2*n) n m t ω ⟨x,hxN⟩} := by
    ext ω
    exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨hxN,h⟩⟩
  rw [hevent]
  exact tilted_isolation_probability_le_touch (RSW.selfDualParameters q) (2*n) n m t ht
    ⟨x,hxN⟩ hheight _ (selfDualTiltedStripMeasure_isLimit q (2*n) t)

end
end PottsContinuity.Thm3.Prop4
