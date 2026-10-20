module

public import PottsContinuity.Thm3.Prop4.TiltedMonotone
public import PottsContinuity.PD.FK.CylinderConvergence

/-!
# Constructing the intrinsic-top tilted law on a common plane carrier

Adapted from the RSW.StripLaw proof: literal closed extension of each
finite approximation, monotonicity of all-open cylinders, compactness and
cylinder determination. No limiting measure is selected from non-unique existence.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Thm3.Prop4

open PD.FK

noncomputable section

attribute [local instance] configurationMeasurableSpace

/-- Original-edge inclusion of a finite tilted window in the plane. -/
def tiltedWindowPlaneEmbedding (n m : ℕ) (t : ℝ) :
    squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ)) ↪g squareLattice where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := Iff.rfl

/-- The specified finite approximation has closed edges outside its original window. -/
def tiltedWindowPlaneConfiguration (n m : ℕ) (t : ℝ)
    (A : Configuration (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ)))) :
    LatticeConfiguration := by
  classical
  exact fun e => decide (e ∈ A.map (tiltedWindowPlaneEmbedding n m t).mapEdgeSet)

/-- Increasing finite states have increasing closed plane extensions. -/
theorem tiltedWindowPlaneConfiguration_mono (n m : ℕ) (t : ℝ) :
    Monotone (tiltedWindowPlaneConfiguration n m t) := by
  classical
  intro A B hAB e
  apply Bool.le_iff_imp.mpr
  simp only [tiltedWindowPlaneConfiguration, decide_eq_true_eq]
  exact fun he => Finset.map_subset_map.mpr hAB he

/-- Restricting then extending by closed edges cannot open any new plane edge. -/
theorem tiltedWindowPlaneConfiguration_restrict_le {n M N : ℕ} {t : ℝ} (hMN : M ≤ N)
    (A : Configuration (squareLattice.induce (tiltedWindow n N t : Set (ℤ × ℤ)))) :
    tiltedWindowPlaneConfiguration n M t (embeddedConfigurationRestriction
      (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ)))
      (squareLattice.induce (tiltedWindow n N t : Set (ℤ × ℤ)))
      (tiltedWindowEmbedding hMN) (tiltedWindow_map_le hMN) A) ≤
    tiltedWindowPlaneConfiguration n N t A := by
  classical
  intro e
  apply Bool.le_iff_imp.mpr
  simp only [tiltedWindowPlaneConfiguration, decide_eq_true_eq]
  intro he
  obtain ⟨f, hf, hfe⟩ := Finset.mem_map.mp he
  refine Finset.mem_map.mpr ⟨embeddedEdgeEmbedding _ _
    (tiltedWindowEmbedding hMN) (tiltedWindow_map_le hMN) f,
    (mem_embeddedConfigurationRestriction _ _ _ _ A f).mp hf, ?_⟩
  rw [← hfe]
  apply Subtype.ext
  change Sym2.map Subtype.val ((tiltedWindowEmbedding hMN).sym2Map f.1) =
    Sym2.map Subtype.val f.1
  rw [Function.Embedding.sym2Map_apply, Sym2.map_map]
  rfl

/-- The specified genuine finite law on a common compact configuration space. -/
def tiltedWindowPlaneProbabilityMeasure (θ : Parameters)
    (n : ℕ) (t : ℝ) (i : Fin 2) (m : ℕ) : ProbabilityMeasure LatticeConfiguration :=
  ⟨((law (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))) θ
    (tiltedWindowBoundary n m t i)).map (tiltedWindowPlaneConfiguration n m t)).toMeasure,
    PMF.toMeasure.isProbabilityMeasure _⟩

/-- Probability of a measurable event equals its literal finite FK preimage. -/
theorem tiltedWindowPlaneProbabilityMeasure_apply (θ : Parameters)
    (n : ℕ) (t : ℝ) (i : Fin 2) (m : ℕ)
    (s : Set LatticeConfiguration) (hs : MeasurableSet s) :
    (tiltedWindowPlaneProbabilityMeasure θ n t i m : Measure LatticeConfiguration) s =
      measure (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))) θ
        (tiltedWindowBoundary n m t i)
        {A | tiltedWindowPlaneConfiguration n m t A ∈ s} := by
  change ((law _ θ (tiltedWindowBoundary n m t i)).map
    (tiltedWindowPlaneConfiguration n m t)).toMeasure s = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hs]
  rfl

private theorem tilted_plane_allOpen_upper (F : Finset squareLattice.edgeSet) :
    IsUpperSet (LatticeConfiguration.allOpen F) := by
  intro ω η h hω e he
  exact (Bool.le_iff_imp.mp (h e)) (hω e he)

/-- Actual all-open cylinder probabilities increase along intrinsic-top windows. -/
theorem tiltedWindowPlaneProbabilityMeasure_top_allOpen_mono (θ : Parameters)
    (n : ℕ) (t : ℝ) (F : Finset squareLattice.edgeSet) :
    Monotone (fun m => tiltedWindowPlaneProbabilityMeasure θ n t 0 m
      (LatticeConfiguration.allOpen F)) := by
  intro M N hMN
  let G := squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))
  let H := squareLattice.induce (tiltedWindow n N t : Set (ℤ × ℤ))
  let f := tiltedWindowEmbedding (n := n) (t := t) hMN
  have hGH : G.map f ≤ H := tiltedWindow_map_le hMN
  let S : Set (Configuration G) :=
    {A | tiltedWindowPlaneConfiguration n M t A ∈ LatticeConfiguration.allOpen F}
  have hS : IsUpperSet S := by
    intro A B hAB hA
    exact tilted_plane_allOpen_upper F (tiltedWindowPlaneConfiguration_mono n M t hAB) hA
  have hlaw : law G θ (isolatedExtensionPullbackBoundary f (tiltedWindowBoundary n N t 0)) =
      law G θ (tiltedWindowBoundary n M t 0) := by
    apply law_eq_of_boundary_partition_eq
    exact tiltedWindow_top_pullback_partition hMN
  have hmeasure : measure G θ
      (isolatedExtensionPullbackBoundary f (tiltedWindowBoundary n N t 0)) =
      measure G θ (tiltedWindowBoundary n M t 0) := by
    unfold PD.FK.measure
    rw [hlaw]
  have hcomp := RSW.embedded_boundary_probability_le G H f hGH θ
    (tiltedWindowBoundary n N t 0) S hS
  rw [hmeasure] at hcomp
  have hsub : {A | embeddedConfigurationRestriction G H f hGH A ∈ S} ⊆
      {A | tiltedWindowPlaneConfiguration n N t A ∈ LatticeConfiguration.allOpen F} := by
    intro A hA
    exact tilted_plane_allOpen_upper F (tiltedWindowPlaneConfiguration_restrict_le hMN A) hA
  apply NNReal.coe_le_coe.mp
  change ((tiltedWindowPlaneProbabilityMeasure θ n t 0 M : Measure LatticeConfiguration)
    (LatticeConfiguration.allOpen F)).toReal ≤
    ((tiltedWindowPlaneProbabilityMeasure θ n t 0 N : Measure LatticeConfiguration)
    (LatticeConfiguration.allOpen F)).toReal
  rw [tiltedWindowPlaneProbabilityMeasure_apply θ n t 0 M _
      (LatticeConfiguration.allOpen_isClopen F).isOpen.measurableSet,
    tiltedWindowPlaneProbabilityMeasure_apply θ n t 0 N _
      (LatticeConfiguration.allOpen_isClopen F).isOpen.measurableSet]
  exact hcomp.trans (measureReal_mono hsub)

/-- The increasing intrinsic-top approximations have a genuine unique plane weak limit. -/
theorem tiltedWindowPlaneProbabilityMeasure_top_existsUnique_limit
    (θ : Parameters) (n : ℕ) (t : ℝ) :
    ∃! ν : ProbabilityMeasure LatticeConfiguration,
      Tendsto (tiltedWindowPlaneProbabilityMeasure θ n t 0) atTop (𝓝 ν) := by
  apply probabilityMeasures_tendsto_of_monotone_allOpen
  exact tiltedWindowPlaneProbabilityMeasure_top_allOpen_mono θ n t

end

end PottsContinuity.Thm3.Prop4
