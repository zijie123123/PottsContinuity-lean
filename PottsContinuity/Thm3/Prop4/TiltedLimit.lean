module

public import PottsContinuity.Thm3.Prop4.TiltedLaw

/-!
# Genuine tilted-strip cylinder-limit construction

Adapted from the RSW.StripLimit proof, preserving actual original
edge patterns on S(n,t)∩Λ_m. The selected law has unique existence for i=0.
The proof uses only i=0, through `tiltedStripMeasure` in `Thm3.Prop4.TiltedSelfDual`;
the limit for i=1 and independence of the side boundary are not formalized here.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Thm3.Prop4

open PD.FK

noncomputable section

/-- Inclusion of the infinite strip graph into the original lattice. -/
def tiltedPlaneEmbedding (n : ℕ) (t : ℝ) : tiltedStripGraph n t ↪g squareLattice where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := Iff.rfl

/-- Restrict a plane configuration to its original strip edges. -/
def tiltedPlaneRestriction (n : ℕ) (t : ℝ) (ω : LatticeConfiguration) : TiltedConfiguration n t :=
  fun e => ω ((tiltedPlaneEmbedding n t).mapEdgeSet e)

/-- Restriction to original edges is continuous in the product topology. -/
theorem tiltedPlaneRestriction_continuous (n : ℕ) (t : ℝ) : Continuous (tiltedPlaneRestriction n t) :=
  continuous_pi fun e => continuous_apply ((tiltedPlaneEmbedding n t).mapEdgeSet e)

private theorem pattern_isClopen {ι : Type*} (A : Finset ι) (ξ : ι → Bool) :
    IsClopen {ω : ι → Bool | ∀ e ∈ A, ω e = ξ e} := by
  classical
  have heq : {ω : ι → Bool | ∀ e ∈ A, ω e = ξ e} =
      ⋂ e ∈ A, {ω | ω e = ξ e} := by ext ω; simp
  rw [heq]
  exact isClopen_biInter_finset fun e _ =>
    (isClopen_discrete ({ξ e} : Set Bool)).preimage (continuous_apply e)

/-- A finite pattern of original strip edges, read on the plane. -/
def tiltedPlanePattern (n : ℕ) (t : ℝ) (A : Finset (tiltedStripGraph n t).edgeSet)
    (ξ : TiltedConfiguration n t) : Set LatticeConfiguration :=
  (tiltedPlaneRestriction n t) ⁻¹' {ω | ∀ e ∈ A, ω e = ξ e}

/-- Finite strip patterns remain clopen on the common plane carrier. -/
theorem tiltedPlanePattern_isClopen (n : ℕ) (t : ℝ) (A : Finset (tiltedStripGraph n t).edgeSet)
    (ξ : TiltedConfiguration n t) : IsClopen (tiltedPlanePattern n t A ξ) :=
  (pattern_isClopen A ξ).preimage (tiltedPlaneRestriction_continuous n t)

private theorem tiltedWindowPlaneConfiguration_at (n m : ℕ) (t : ℝ)
    (C : Configuration (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))))
    (f : (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))).edgeSet) :
    tiltedWindowPlaneConfiguration n m t C ((tiltedWindowPlaneEmbedding n m t).mapEdgeSet f) =
      (boolConfigurationEquiv _).symm C f := by
  classical
  simp only [tiltedWindowPlaneConfiguration, boolConfigurationEquiv,
    Equiv.coe_fn_symm_mk, decide_eq_decide]
  change ((tiltedWindowPlaneEmbedding n m t).mapEdgeSet f ∈
    C.map (tiltedWindowPlaneEmbedding n m t).mapEdgeSet) ↔ f ∈ C
  constructor
  · intro h
    obtain ⟨g, hg, hgf⟩ := Finset.mem_map.mp h
    have heq := (tiltedWindowPlaneEmbedding n m t).mapEdgeSet.injective hgf
    exact heq ▸ hg
  · intro h
    exact Finset.mem_map.mpr ⟨f, h, rfl⟩

/-- On a window containing the pattern's edges, the literal finite extension
satisfies the plane pattern iff the original finite state satisfies the cylinder. -/
theorem tiltedWindowPlanePattern_iff (n m : ℕ) (t : ℝ) (A : Finset (tiltedStripGraph n t).edgeSet)
    (ξ : TiltedConfiguration n t)
    (hsupp : ∀ e ∈ A,
      ∃ f : (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))).edgeSet,
        Sym2.map Subtype.val f.1 = Sym2.map Subtype.val e.1)
    (C : Configuration (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ)))) :
    tiltedWindowPlaneConfiguration n m t C ∈ tiltedPlanePattern n t A ξ ↔
      tiltedWindowCylinder n m t A ξ ((boolConfigurationEquiv _).symm C) := by
  constructor
  · intro h e he
    obtain ⟨f, hf⟩ := hsupp e he
    have hfe : (tiltedWindowPlaneEmbedding n m t).mapEdgeSet f =
        (tiltedPlaneEmbedding n t).mapEdgeSet e := Subtype.ext hf
    refine ⟨f, hf, ?_⟩
    have hstate := h e he
    change tiltedWindowPlaneConfiguration n m t C ((tiltedPlaneEmbedding n t).mapEdgeSet e) =
      ξ e at hstate
    rw [← hfe, tiltedWindowPlaneConfiguration_at] at hstate
    exact hstate
  · intro h e he
    obtain ⟨f, hf, hstate⟩ := h e he
    have hfe : (tiltedWindowPlaneEmbedding n m t).mapEdgeSet f =
        (tiltedPlaneEmbedding n t).mapEdgeSet e := Subtype.ext hf
    change tiltedWindowPlaneConfiguration n m t C ((tiltedPlaneEmbedding n t).mapEdgeSet e) = ξ e
    rw [← hfe, tiltedWindowPlaneConfiguration_at]
    exact hstate

/-- Exact finite pattern probability transport once all pattern edges are present. -/
theorem tiltedWindowPlaneProbabilityMeasure_pattern (θ : Parameters)
    (n : ℕ) (t : ℝ) (i : Fin 2) (m : ℕ) (A : Finset (tiltedStripGraph n t).edgeSet)
    (ξ : TiltedConfiguration n t)
    (hsupp : ∀ e ∈ A,
      ∃ f : (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))).edgeSet,
        Sym2.map Subtype.val f.1 = Sym2.map Subtype.val e.1) :
    (tiltedWindowPlaneProbabilityMeasure θ n t i m).toMeasure.real (tiltedPlanePattern n t A ξ) =
      tiltedWindowCylinderProbability θ n t i m A ξ := by
  have hsets : {C | tiltedWindowPlaneConfiguration n m t C ∈ tiltedPlanePattern n t A ξ} =
      RSW.finiteBoolEvent (tiltedWindow n m t) (tiltedWindowCylinder n m t A ξ) := by
    ext C
    exact tiltedWindowPlanePattern_iff n m t A ξ hsupp C
  unfold Measure.real
  rw [tiltedWindowPlaneProbabilityMeasure_apply θ n t i m _
    (tiltedPlanePattern_isClopen n t A ξ).isOpen.measurableSet, hsets]
  rfl

/-- Any genuine weak limit of the specified plane window laws induces the
exact strip cylinder limit, preserving the lateral convention. -/
theorem isTiltedStripLimit_of_plane_tendsto (θ : Parameters) (n : ℕ) (t : ℝ) (i : Fin 2)
    (ν : ProbabilityMeasure LatticeConfiguration)
    (hν : Tendsto (tiltedWindowPlaneProbabilityMeasure θ n t i) atTop (𝓝 ν)) :
    IsTiltedStripLimit θ n t i (ν.map (tiltedPlaneRestriction n t)).toMeasure := by
  let μ := ν.map (tiltedPlaneRestriction n t)
  refine ⟨μ.prop, ?_⟩
  intro A ξ
  have hconv := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hν
    (tiltedPlanePattern_isClopen n t A ξ)
  have hreal : Tendsto
      (fun m => (tiltedWindowPlaneProbabilityMeasure θ n t i m).toMeasure.real
        (tiltedPlanePattern n t A ξ)) atTop
      (𝓝 (ν.toMeasure.real (tiltedPlanePattern n t A ξ))) := by
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, Function.comp_def] using
      NNReal.continuous_coe.continuousAt.tendsto.comp hconv
  have hlim : ν.toMeasure.real (tiltedPlanePattern n t A ξ) =
      μ.toMeasure.real {ω | ∀ e ∈ A, ω e = ξ e} := by
    change _ = (ν.toMeasure.map (tiltedPlaneRestriction n t)).real _
    unfold Measure.real
    rw [Measure.map_apply (tiltedPlaneRestriction_continuous n t).measurable
      (pattern_isClopen A ξ).isOpen.measurableSet]
    rfl
  rw [hlim] at hreal
  refine hreal.congr' ?_
  filter_upwards [eventually_tiltedWindow_finset_edge_lift n t A] with m hm
  exact tiltedWindowPlaneProbabilityMeasure_pattern θ n t i m A ξ hm

/-- The genuine top-only strip cylinder law exists and is unique, on the actual
infinite strip-edge carrier and with no critical or RSW hypothesis. -/
theorem isTiltedStripLimit_top_existsUnique (θ : Parameters) (n : ℕ) (t : ℝ) :
    ∃! μ : Measure (TiltedConfiguration n t), IsTiltedStripLimit θ n t 0 μ := by
  obtain ⟨ν, hν, _⟩ := tiltedWindowPlaneProbabilityMeasure_top_existsUnique_limit θ n t
  let μ := ν.map (tiltedPlaneRestriction n t)
  have hμ : IsTiltedStripLimit θ n t 0 μ.toMeasure :=
    isTiltedStripLimit_of_plane_tendsto θ n t 0 ν hν
  exact ⟨μ.toMeasure, hμ, fun ρ hρ => isTiltedStripLimit_unique θ n t 0 ρ μ.toMeasure hρ hμ⟩

end

end PottsContinuity.Thm3.Prop4
