module

public import PottsContinuity.Thm3.RSW.StripLaw

/-!
# The top-only strip law satisfies the actual strip cylinder-limit predicate

The whole-plane finite approximations are used only as a common carrier. Their
limit is pushed to the genuine strip edge space, and every finite strip pattern
is checked using its original edges. No lateral-boundary independence is asserted.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.RSW

open PD.FK

noncomputable section

/-- Inclusion of the infinite strip graph into the original lattice. -/
def stripPlaneEmbedding (n : ℕ) : stripGraph n ↪g squareLattice where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := Iff.rfl

/-- Restrict a plane configuration to its original strip edges. -/
def stripPlaneRestriction (n : ℕ) (ω : LatticeConfiguration) : StripConfiguration n :=
  fun e => ω ((stripPlaneEmbedding n).mapEdgeSet e)

/-- Restriction to original edges is continuous in the product topology. -/
theorem stripPlaneRestriction_continuous (n : ℕ) : Continuous (stripPlaneRestriction n) :=
  continuous_pi fun e => continuous_apply ((stripPlaneEmbedding n).mapEdgeSet e)

private theorem pattern_isClopen {ι : Type*} (A : Finset ι) (ξ : ι → Bool) :
    IsClopen {ω : ι → Bool | ∀ e ∈ A, ω e = ξ e} := by
  classical
  have heq : {ω : ι → Bool | ∀ e ∈ A, ω e = ξ e} =
      ⋂ e ∈ A, {ω | ω e = ξ e} := by ext ω; simp
  rw [heq]
  exact isClopen_biInter_finset fun e _ =>
    (isClopen_discrete ({ξ e} : Set Bool)).preimage (continuous_apply e)

/-- A finite pattern of original strip edges, read on the plane. -/
def stripPlanePattern (n : ℕ) (A : Finset (stripGraph n).edgeSet)
    (ξ : StripConfiguration n) : Set LatticeConfiguration :=
  (stripPlaneRestriction n) ⁻¹' {ω | ∀ e ∈ A, ω e = ξ e}

/-- Finite strip patterns remain clopen on the common plane carrier. -/
theorem stripPlanePattern_isClopen (n : ℕ) (A : Finset (stripGraph n).edgeSet)
    (ξ : StripConfiguration n) : IsClopen (stripPlanePattern n A ξ) :=
  (pattern_isClopen A ξ).preimage (stripPlaneRestriction_continuous n)

private theorem stripWindowPlaneConfiguration_at (n m : ℕ)
    (C : Configuration (squareLattice.induce (stripWindow n m : Set (ℤ × ℤ))))
    (f : (squareLattice.induce (stripWindow n m : Set (ℤ × ℤ))).edgeSet) :
    stripWindowPlaneConfiguration n m C ((stripWindowPlaneEmbedding n m).mapEdgeSet f) =
      (boolConfigurationEquiv _).symm C f := by
  classical
  simp only [stripWindowPlaneConfiguration, boolConfigurationEquiv,
    Equiv.coe_fn_symm_mk, decide_eq_decide]
  change ((stripWindowPlaneEmbedding n m).mapEdgeSet f ∈
    C.map (stripWindowPlaneEmbedding n m).mapEdgeSet) ↔ f ∈ C
  constructor
  · intro h
    obtain ⟨g, hg, hgf⟩ := Finset.mem_map.mp h
    have heq := (stripWindowPlaneEmbedding n m).mapEdgeSet.injective hgf
    exact heq ▸ hg
  · intro h
    exact Finset.mem_map.mpr ⟨f, h, rfl⟩

/-- On a window containing the pattern's edges, the literal finite extension
satisfies the plane pattern iff the original finite state satisfies the cylinder. -/
theorem stripWindowPlanePattern_iff (n m : ℕ) (A : Finset (stripGraph n).edgeSet)
    (ξ : StripConfiguration n)
    (hsupp : ∀ e ∈ A,
      ∃ f : (squareLattice.induce (stripWindow n m : Set (ℤ × ℤ))).edgeSet,
        Sym2.map Subtype.val f.1 = Sym2.map Subtype.val e.1)
    (C : Configuration (squareLattice.induce (stripWindow n m : Set (ℤ × ℤ)))) :
    stripWindowPlaneConfiguration n m C ∈ stripPlanePattern n A ξ ↔
      stripWindowCylinder n m A ξ ((boolConfigurationEquiv _).symm C) := by
  constructor
  · intro h e he
    obtain ⟨f, hf⟩ := hsupp e he
    have hfe : (stripWindowPlaneEmbedding n m).mapEdgeSet f =
        (stripPlaneEmbedding n).mapEdgeSet e := Subtype.ext hf
    refine ⟨f, hf, ?_⟩
    have hstate := h e he
    change stripWindowPlaneConfiguration n m C ((stripPlaneEmbedding n).mapEdgeSet e) =
      ξ e at hstate
    rw [← hfe, stripWindowPlaneConfiguration_at] at hstate
    exact hstate
  · intro h e he
    obtain ⟨f, hf, hstate⟩ := h e he
    have hfe : (stripWindowPlaneEmbedding n m).mapEdgeSet f =
        (stripPlaneEmbedding n).mapEdgeSet e := Subtype.ext hf
    change stripWindowPlaneConfiguration n m C ((stripPlaneEmbedding n).mapEdgeSet e) = ξ e
    rw [← hfe, stripWindowPlaneConfiguration_at]
    exact hstate

/-- Exact finite pattern probability transport once all pattern edges are present. -/
theorem stripWindowPlaneProbabilityMeasure_pattern (θ : Parameters)
    (n : ℕ) (i : Fin 2) (m : ℕ) (A : Finset (stripGraph n).edgeSet)
    (ξ : StripConfiguration n)
    (hsupp : ∀ e ∈ A,
      ∃ f : (squareLattice.induce (stripWindow n m : Set (ℤ × ℤ))).edgeSet,
        Sym2.map Subtype.val f.1 = Sym2.map Subtype.val e.1) :
    (stripWindowPlaneProbabilityMeasure θ n i m).toMeasure.real (stripPlanePattern n A ξ) =
      stripWindowCylinderProbability θ n i m A ξ := by
  have hsets : {C | stripWindowPlaneConfiguration n m C ∈ stripPlanePattern n A ξ} =
      finiteBoolEvent (stripWindow n m) (stripWindowCylinder n m A ξ) := by
    ext C
    exact stripWindowPlanePattern_iff n m A ξ hsupp C
  unfold Measure.real
  rw [stripWindowPlaneProbabilityMeasure_apply θ n i m _
    (stripPlanePattern_isClopen n A ξ).isOpen.measurableSet, hsets]
  rfl

/-- Any genuine weak limit of the specified plane window laws induces the
exact strip cylinder limit, preserving the lateral convention. -/
theorem isTopWiredStripLimit_of_plane_tendsto (θ : Parameters) (n : ℕ) (i : Fin 2)
    (ν : ProbabilityMeasure LatticeConfiguration)
    (hν : Tendsto (stripWindowPlaneProbabilityMeasure θ n i) atTop (𝓝 ν)) :
    IsTopWiredStripLimit θ n i (ν.map (stripPlaneRestriction n)).toMeasure := by
  let μ := ν.map (stripPlaneRestriction n)
  refine ⟨μ.prop, ?_⟩
  intro A ξ
  have hconv := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hν
    (stripPlanePattern_isClopen n A ξ)
  have hreal : Tendsto
      (fun m => (stripWindowPlaneProbabilityMeasure θ n i m).toMeasure.real
        (stripPlanePattern n A ξ)) atTop
      (𝓝 (ν.toMeasure.real (stripPlanePattern n A ξ))) := by
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, Function.comp_def] using
      NNReal.continuous_coe.continuousAt.tendsto.comp hconv
  have hlim : ν.toMeasure.real (stripPlanePattern n A ξ) =
      μ.toMeasure.real {ω | ∀ e ∈ A, ω e = ξ e} := by
    change _ = (ν.toMeasure.map (stripPlaneRestriction n)).real _
    unfold Measure.real
    rw [Measure.map_apply (stripPlaneRestriction_continuous n).measurable
      (pattern_isClopen A ξ).isOpen.measurableSet]
    rfl
  rw [hlim] at hreal
  refine hreal.congr' ?_
  filter_upwards [eventually_stripWindow_finset_edge_lift n A] with m hm
  exact stripWindowPlaneProbabilityMeasure_pattern θ n i m A ξ hm

/-- The genuine top-only strip cylinder law exists and is unique, on the actual
infinite strip-edge carrier and with no critical or RSW hypothesis. -/
theorem isTopWiredStripLimit_top_existsUnique (θ : Parameters) (n : ℕ) :
    ∃! μ : Measure (StripConfiguration n), IsTopWiredStripLimit θ n 0 μ := by
  obtain ⟨ν, hν, _⟩ := stripWindowPlaneProbabilityMeasure_top_existsUnique_limit θ n
  let μ := ν.map (stripPlaneRestriction n)
  have hμ : IsTopWiredStripLimit θ n 0 μ.toMeasure :=
    isTopWiredStripLimit_of_plane_tendsto θ n 0 ν hν
  exact ⟨μ.toMeasure, hμ, fun ρ hρ => isTopWiredStripLimit_unique θ n 0 ρ μ.toMeasure hρ hμ⟩

end

end PottsContinuity.RSW
