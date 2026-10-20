module

public import PottsContinuity.Thm3.RSW.StripLimit

/-!
# Clopen positive association of the constructed top-only strip law

Finite top-wired FK laws are positively associated. Literal closed extension
preserves the coordinate order, weak convergence preserves inequalities on
clopen events, and restriction to the strip preserves both properties.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.RSW

open PD.FK

noncomputable section

attribute [local instance] configurationMeasurableSpace

/-- Positive association for measurable increasing plane events under each
finite mixed-boundary strip-window approximation. -/
theorem stripWindowPlane_measurable_fkg (θ : Parameters) (n : ℕ) (i : Fin 2) (m : ℕ)
    (s t : Set LatticeConfiguration) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsu : IsUpperSet s) (htu : IsUpperSet t) :
    (stripWindowPlaneProbabilityMeasure θ n i m).toMeasure.real s *
      (stripWindowPlaneProbabilityMeasure θ n i m).toMeasure.real t ≤
        (stripWindowPlaneProbabilityMeasure θ n i m).toMeasure.real (s ∩ t) := by
  have hs' : IsUpperSet {C | stripWindowPlaneConfiguration n m C ∈ s} := by
    intro A B hAB hA
    exact hsu (stripWindowPlaneConfiguration_mono n m hAB) hA
  have ht' : IsUpperSet {C | stripWindowPlaneConfiguration n m C ∈ t} := by
    intro A B hAB hA
    exact htu (stripWindowPlaneConfiguration_mono n m hAB) hA
  unfold Measure.real
  rw [stripWindowPlaneProbabilityMeasure_apply θ n i m s hs,
    stripWindowPlaneProbabilityMeasure_apply θ n i m t ht,
    stripWindowPlaneProbabilityMeasure_apply θ n i m (s ∩ t) (hs.inter ht)]
  exact measure_positive_association θ (stripWindowBoundary n m i) _ _ hs' ht'

/-- Weak limits of the actual window sequence inherit FKG on increasing
clopen events. The convergence premise is the genuine finite-law convergence. -/
theorem stripPlane_clopen_fkg_of_plane_tendsto (θ : Parameters) (n : ℕ) (i : Fin 2)
    (ν : ProbabilityMeasure LatticeConfiguration)
    (hν : Tendsto (stripWindowPlaneProbabilityMeasure θ n i) atTop (𝓝 ν))
    (s t : Set LatticeConfiguration) (hs : IsClopen s) (ht : IsClopen t)
    (hsu : IsUpperSet s) (htu : IsUpperSet t) :
    ν.toMeasure.real s * ν.toMeasure.real t ≤ ν.toMeasure.real (s ∩ t) := by
  have hreal (u : Set LatticeConfiguration) (hu : IsClopen u) :
      Tendsto (fun m => (stripWindowPlaneProbabilityMeasure θ n i m).toMeasure.real u)
        atTop (𝓝 (ν.toMeasure.real u)) := by
    have hconv := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hν hu
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, Function.comp_def] using
      NNReal.continuous_coe.continuousAt.tendsto.comp hconv
  exact le_of_tendsto_of_tendsto ((hreal s hs).mul (hreal t ht))
    (hreal (s ∩ t) (hs.inter ht))
    (Eventually.of_forall fun m => stripWindowPlane_measurable_fkg θ n i m s t
      hs.isOpen.measurableSet ht.isOpen.measurableSet hsu htu)

/-- The genuine strip cylinder limit is positively associated on increasing
clopen events. No RSW, duality, or lateral-independence hypothesis is used. -/
theorem strip_clopen_fkg (θ : Parameters) (n : ℕ)
    (μ : Measure (StripConfiguration n)) (hμ : IsTopWiredStripLimit θ n 0 μ)
    (s t : Set (StripConfiguration n)) (hs : IsClopen s) (ht : IsClopen t)
    (hsu : IsUpperSet s) (htu : IsUpperSet t) :
    μ.real s * μ.real t ≤ μ.real (s ∩ t) := by
  obtain ⟨ν, hν, _⟩ := stripWindowPlaneProbabilityMeasure_top_existsUnique_limit θ n
  have hmap : IsTopWiredStripLimit θ n 0 (ν.map (stripPlaneRestriction n)).toMeasure :=
    isTopWiredStripLimit_of_plane_tendsto θ n 0 ν hν
  have heq := isTopWiredStripLimit_unique θ n 0 μ _ hμ hmap
  rw [heq]
  have hs' : IsClopen ((stripPlaneRestriction n) ⁻¹' s) :=
    hs.preimage (stripPlaneRestriction_continuous n)
  have ht' : IsClopen ((stripPlaneRestriction n) ⁻¹' t) :=
    ht.preimage (stripPlaneRestriction_continuous n)
  have hsu' : IsUpperSet ((stripPlaneRestriction n) ⁻¹' s) := by
    intro ω η h hω
    exact hsu (fun e => h ((stripPlaneEmbedding n).mapEdgeSet e)) hω
  have htu' : IsUpperSet ((stripPlaneRestriction n) ⁻¹' t) := by
    intro ω η h hω
    exact htu (fun e => h ((stripPlaneEmbedding n).mapEdgeSet e)) hω
  change (ν.toMeasure.map (stripPlaneRestriction n)).real s *
    (ν.toMeasure.map (stripPlaneRestriction n)).real t ≤
      (ν.toMeasure.map (stripPlaneRestriction n)).real (s ∩ t)
  unfold Measure.real
  rw [Measure.map_apply (stripPlaneRestriction_continuous n).measurable hs.isOpen.measurableSet,
    Measure.map_apply (stripPlaneRestriction_continuous n).measurable ht.isOpen.measurableSet,
    Measure.map_apply (stripPlaneRestriction_continuous n).measurable
      (hs.inter ht).isOpen.measurableSet]
  exact stripPlane_clopen_fkg_of_plane_tendsto θ n 0 ν hν _ _ hs' ht' hsu' htu'

end

end PottsContinuity.RSW
