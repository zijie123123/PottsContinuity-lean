module

public import PottsContinuity.Thm3.RSW.StripMonotone
public import PottsContinuity.PD.FK.CylinderConvergence

/-!
# Existence of the increasing-width top-wired strip law on a common carrier

Finite configurations are literally extended by closed edges outside the window.
This is a specified finite-law embedding, not an infinite-volume fallback. The
existence theorem below constructs a genuine unique weak limit, for all q≥1 and
independent interior p. Independence of lateral wiring is a separate assertion.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.RSW

open PD.FK

noncomputable section

attribute [local instance] configurationMeasurableSpace

/-- Inclusion of the finite window's actual edges in the original lattice. -/
def stripWindowPlaneEmbedding (n m : ℕ) :
    squareLattice.induce (stripWindow n m : Set (ℤ × ℤ)) ↪g squareLattice where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := Iff.rfl

/-- A finite window state, extended with closed edges outside the window. -/
def stripWindowPlaneConfiguration (n m : ℕ)
    (A : Configuration (squareLattice.induce (stripWindow n m : Set (ℤ × ℤ)))) :
    LatticeConfiguration := by
  classical
  exact fun e => decide (e ∈ A.map (stripWindowPlaneEmbedding n m).mapEdgeSet)

/-- Opening additional actual window edges opens additional plane edges. -/
theorem stripWindowPlaneConfiguration_mono (n m : ℕ) :
    Monotone (stripWindowPlaneConfiguration n m) := by
  classical
  intro A B hAB e
  apply Bool.le_iff_imp.mpr
  simp only [stripWindowPlaneConfiguration, decide_eq_true_eq]
  exact fun he => Finset.map_subset_map.mpr hAB he

/-- Restriction followed by closed extension cannot create any extra open edge. -/
theorem stripWindowPlaneConfiguration_restrict_le {n M N : ℕ} (hMN : M ≤ N)
    (A : Configuration (squareLattice.induce (stripWindow n N : Set (ℤ × ℤ)))) :
    stripWindowPlaneConfiguration n M (embeddedConfigurationRestriction
      (squareLattice.induce (stripWindow n M : Set (ℤ × ℤ)))
      (squareLattice.induce (stripWindow n N : Set (ℤ × ℤ)))
      (stripWindowEmbedding hMN) (stripWindow_map_le hMN) A) ≤
    stripWindowPlaneConfiguration n N A := by
  classical
  intro e
  apply Bool.le_iff_imp.mpr
  simp only [stripWindowPlaneConfiguration, decide_eq_true_eq]
  intro he
  obtain ⟨f, hf, hfe⟩ := Finset.mem_map.mp he
  refine Finset.mem_map.mpr ⟨embeddedEdgeEmbedding _ _
    (stripWindowEmbedding hMN) (stripWindow_map_le hMN) f,
    (mem_embeddedConfigurationRestriction _ _ _ _ A f).mp hf, ?_⟩
  rw [← hfe]
  apply Subtype.ext
  change Sym2.map Subtype.val ((stripWindowEmbedding hMN).sym2Map f.1) =
    Sym2.map Subtype.val f.1
  rw [Function.Embedding.sym2Map_apply, Sym2.map_map]
  rfl

/-- The specified finite top-wired law on the common plane carrier. -/
def stripWindowPlaneProbabilityMeasure (θ : Parameters) (n : ℕ) (i : Fin 2) (m : ℕ) :
    ProbabilityMeasure LatticeConfiguration :=
  ⟨((law (squareLattice.induce (stripWindow n m : Set (ℤ × ℤ))) θ
    (stripWindowBoundary n m i)).map (stripWindowPlaneConfiguration n m)).toMeasure,
    PMF.toMeasure.isProbabilityMeasure _⟩

/-- A measurable plane event has exactly its original finite FK preimage probability. -/
theorem stripWindowPlaneProbabilityMeasure_apply (θ : Parameters)
    (n : ℕ) (i : Fin 2) (m : ℕ) (s : Set LatticeConfiguration) (hs : MeasurableSet s) :
    (stripWindowPlaneProbabilityMeasure θ n i m : Measure LatticeConfiguration) s =
      measure (squareLattice.induce (stripWindow n m : Set (ℤ × ℤ))) θ
        (stripWindowBoundary n m i) {A | stripWindowPlaneConfiguration n m A ∈ s} := by
  change ((law _ θ (stripWindowBoundary n m i)).map
    (stripWindowPlaneConfiguration n m)).toMeasure s = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hs]
  rfl

private theorem plane_allOpen_upper (F : Finset squareLattice.edgeSet) :
    IsUpperSet (LatticeConfiguration.allOpen F) := by
  intro ω η h hω e he
  exact (Bool.le_iff_imp.mp (h e)) (hω e he)

/-- All-open cylinder probabilities increase with window width under top-only wiring. -/
theorem stripWindowPlaneProbabilityMeasure_top_allOpen_mono (θ : Parameters)
    (n : ℕ) (F : Finset squareLattice.edgeSet) :
    Monotone (fun m => stripWindowPlaneProbabilityMeasure θ n 0 m
      (LatticeConfiguration.allOpen F)) := by
  intro M N hMN
  let G := squareLattice.induce (stripWindow n M : Set (ℤ × ℤ))
  let H := squareLattice.induce (stripWindow n N : Set (ℤ × ℤ))
  let f := stripWindowEmbedding (n := n) hMN
  have hGH : G.map f ≤ H := stripWindow_map_le hMN
  let S : Set (Configuration G) :=
    {A | stripWindowPlaneConfiguration n M A ∈ LatticeConfiguration.allOpen F}
  have hS : IsUpperSet S := by
    intro A B hAB hA
    exact plane_allOpen_upper F (stripWindowPlaneConfiguration_mono n M hAB) hA
  have hlaw : law G θ (isolatedExtensionPullbackBoundary f (stripWindowBoundary n N 0)) =
      law G θ (stripWindowBoundary n M 0) := by
    apply law_eq_of_boundary_partition_eq
    exact stripWindow_top_pullback_partition hMN
  have hmeasure : measure G θ
      (isolatedExtensionPullbackBoundary f (stripWindowBoundary n N 0)) =
      measure G θ (stripWindowBoundary n M 0) := by
    unfold PD.FK.measure
    rw [hlaw]
  have hcomp := embedded_boundary_probability_le G H f hGH θ
    (stripWindowBoundary n N 0) S hS
  rw [hmeasure] at hcomp
  have hsub : {A | embeddedConfigurationRestriction G H f hGH A ∈ S} ⊆
      {A | stripWindowPlaneConfiguration n N A ∈ LatticeConfiguration.allOpen F} := by
    intro A hA
    exact plane_allOpen_upper F (stripWindowPlaneConfiguration_restrict_le hMN A) hA
  apply NNReal.coe_le_coe.mp
  change ((stripWindowPlaneProbabilityMeasure θ n 0 M : Measure LatticeConfiguration)
    (LatticeConfiguration.allOpen F)).toReal ≤
    ((stripWindowPlaneProbabilityMeasure θ n 0 N : Measure LatticeConfiguration)
    (LatticeConfiguration.allOpen F)).toReal
  rw [stripWindowPlaneProbabilityMeasure_apply θ n 0 M _
      (LatticeConfiguration.allOpen_isClopen F).isOpen.measurableSet,
    stripWindowPlaneProbabilityMeasure_apply θ n 0 N _
      (LatticeConfiguration.allOpen_isClopen F).isOpen.measurableSet]
  exact hcomp.trans (measureReal_mono hsub)

/-- The genuine weak limit of the top-only strip windows exists and is unique
on the common whole-plane carrier. No limiting measure is postulated. -/
theorem stripWindowPlaneProbabilityMeasure_top_existsUnique_limit
    (θ : Parameters) (n : ℕ) :
    ∃! ν : ProbabilityMeasure LatticeConfiguration,
      Tendsto (stripWindowPlaneProbabilityMeasure θ n 0) atTop (𝓝 ν) := by
  apply probabilityMeasures_tendsto_of_monotone_allOpen
  exact stripWindowPlaneProbabilityMeasure_top_allOpen_mono θ n

end

end PottsContinuity.RSW
