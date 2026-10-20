module

public import PottsContinuity.Thm1.ShellCylinderLimit
public import PottsContinuity.PD.FK.CylinderConvergence

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open MeasureTheory Filter Topology
open PottsContinuity
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

local instance pottsESShellBondVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype (PottsESVertex V) := Fintype.ofFinite _

local instance pottsESShellBondEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (pottsESGraph V).edgeSet := Fintype.ofFinite _

local instance pottsESShellBondConfigurationDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (pottsESGraph V).edgeSet := Classical.decEq _

/-- Extend a finite shell bond configuration by closing every lattice edge
outside the shell graph. -/
def pottsESShellBondExtension (V : Finset (ℤ × ℤ))
    (A : Configuration (pottsESGraph V)) : LatticeConfiguration := by
  classical
  exact fun e =>
    if h : ∃ g : (pottsESGraph V).edgeSet,
        ((pottsESEdgeEquiv V).symm g).1 = e.1
    then decide (Classical.choose h ∈ A) else false

private theorem pottsESShellBondExtension_at (V : Finset (ℤ × ℤ))
    (A : Configuration (pottsESGraph V)) (e : PD.FK.squareLattice.edgeSet)
    (h : ∃ g : (pottsESGraph V).edgeSet,
      ((pottsESEdgeEquiv V).symm g).1 = e.1) :
    pottsESShellBondExtension V A e = decide (Classical.choose h ∈ A) := by
  simp [pottsESShellBondExtension, h]

/-- An extended lattice edge is open exactly when its corresponding shell
graph edge is open. -/
theorem pottsESShellBondExtension_edge_open_iff
    (V : Finset (ℤ × ℤ)) (A : Configuration (pottsESGraph V))
    (e : PD.FK.squareLattice.edgeSet) :
    pottsESShellBondExtension V A e = true ↔
      ∃ g : (pottsESGraph V).edgeSet,
        g ∈ A ∧ ((pottsESEdgeEquiv V).symm g).1 = e.1 := by
  classical
  constructor
  · intro hstate
    by_cases hex : ∃ g : (pottsESGraph V).edgeSet,
        ((pottsESEdgeEquiv V).symm g).1 = e.1
    · refine ⟨Classical.choose hex, ?_, Classical.choose_spec hex⟩
      rw [pottsESShellBondExtension_at V A e hex] at hstate
      exact decide_eq_true_eq.mp hstate
    · simp [pottsESShellBondExtension, hex] at hstate
  · rintro ⟨g, hgA, hge⟩
    let hex : ∃ g' : (pottsESGraph V).edgeSet,
        ((pottsESEdgeEquiv V).symm g').1 = e.1 := ⟨g, hge⟩
    have hchoose : Classical.choose hex = g := by
      apply (pottsESEdgeEquiv V).symm.injective
      apply Subtype.ext
      exact (Classical.choose_spec hex).trans hge.symm
    rw [pottsESShellBondExtension_at V A e hex]
    exact decide_eq_true hgA ▸ congrArg (fun g' => decide (g' ∈ A)) hchoose

/-- On cylinders supported by the shell edges, the whole-lattice extension
reads exactly the ghost-wired finite configuration. -/
theorem pottsESShellBondExtension_allOpen_iff
    (V : Finset (ℤ × ℤ)) (F : Finset PD.FK.squareLattice.edgeSet)
    (hF : ∀ e ∈ F, ∃ g : (pottsESGraph V).edgeSet,
      ((pottsESEdgeEquiv V).symm g).1 = e.1)
    (A : Configuration (pottsESGraph V)) :
    pottsESShellBondExtension V A ∈ LatticeConfiguration.allOpen F ↔
      A ∈ pottsESAllOpenCylinderEvent V F := by
  classical
  constructor
  · intro h e he g hg
    have hEdge := hF e he
    have hChoose := Classical.choose_spec hEdge
    have hgEq : g = Classical.choose hEdge := by
      apply (pottsESEdgeEquiv V).symm.injective
      apply Subtype.ext
      exact hg.trans hChoose.symm
    have hstate := h e he
    rw [pottsESShellBondExtension_at V A e hEdge] at hstate
    have hmem : Classical.choose hEdge ∈ A := decide_eq_true_eq.mp hstate
    simpa [hgEq] using hmem
  · intro hA e he
    have hEdge := hF e he
    have hmem := hA e he (Classical.choose hEdge) (Classical.choose_spec hEdge)
    rw [pottsESShellBondExtension_at V A e hEdge]
    exact decide_eq_true hmem

/-- The finite Edwards--Sokal shell bond law, extended by closed edges, on the
common whole-lattice configuration space. -/
def pottsESShellBondProbabilityMeasure (θ : Parameters) (V : Finset (ℤ × ℤ)) :
    ProbabilityMeasure LatticeConfiguration :=
  ⟨((law (pottsESGraph V) θ (pottsESBoundaryCondition V)).map
      (pottsESShellBondExtension V)).toMeasure,
    PMF.toMeasure.isProbabilityMeasure _⟩

attribute [local instance] configurationMeasurableSpace

theorem pottsESShellBondProbabilityMeasure_apply (θ : Parameters)
    (V : Finset (ℤ × ℤ)) {S : Set LatticeConfiguration}
    (hS : MeasurableSet S) :
    (pottsESShellBondProbabilityMeasure θ V : Measure LatticeConfiguration) S =
      measure (pottsESGraph V) θ (pottsESBoundaryCondition V)
        {A | pottsESShellBondExtension V A ∈ S} := by
  change (((law (pottsESGraph V) θ (pottsESBoundaryCondition V)).map
    (pottsESShellBondExtension V)).toMeasure) S = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hS]
  rfl

theorem pottsESShellBondProbabilityMeasure_allOpen (θ : Parameters)
    (V : Finset (ℤ × ℤ)) (F : Finset PD.FK.squareLattice.edgeSet)
    (hF : ∀ e ∈ F, ∃ g : (pottsESGraph V).edgeSet,
      ((pottsESEdgeEquiv V).symm g).1 = e.1) :
    (pottsESShellBondProbabilityMeasure θ V : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F) =
      measure (pottsESGraph V) θ (pottsESBoundaryCondition V)
        (pottsESAllOpenCylinderEvent V F) := by
  change (((law (pottsESGraph V) θ (pottsESBoundaryCondition V)).map
    (pottsESShellBondExtension V)).toMeasure) _ = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    (LatticeConfiguration.allOpen_isClopen F).isOpen.measurableSet]
  congr 1
  ext A
  exact pottsESShellBondExtension_allOpen_iff V F hF A

theorem pottsESShellBondProbabilityMeasure_tendsto
    (θ : Parameters) (V : ℕ → Finset (ℤ × ℤ))
    (hNest : ∀ n, V n ⊆ V (n + 1))
    (hExhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ V n)
    (μ : Measure LatticeConfiguration)
    (hμ : PottsContinuity.PD.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 1 μ) :
    Tendsto (fun n => pottsESShellBondProbabilityMeasure θ (V n)) atTop
      (𝓝 (⟨μ, hμ.1⟩ : ProbabilityMeasure LatticeConfiguration)) := by
  classical
  let ν : ProbabilityMeasure LatticeConfiguration := ⟨μ, hμ.1⟩
  have hAllOpen (F : Finset PD.FK.squareLattice.edgeSet) :
      Tendsto
        (fun n => pottsESShellBondProbabilityMeasure θ (V n)
          (LatticeConfiguration.allOpen F)) atTop
        (𝓝 (ν (LatticeConfiguration.allOpen F))) := by
    obtain ⟨rF, hrF⟩ := exists_box_supporting_edge_finset F
    have hFrozenRange : ∀ e ∈ F,
        e ∈ Set.range (frozenEdgeEmbedding (latticeBox (0, 0) rF)) := by
      intro e he
      exact boxEdges_subset_frozenEdgeEmbedding_range rF (hrF e he)
    have hEdgeId (r : ℕ) :
        frozenEdgeEmbedding (latticeBox (0, 0) r) = boxEdgeEmbedding (0, 0) r := rfl
    have hFBox : ∀ e ∈ F, e ∈ Set.range (boxEdgeEmbedding (0, 0) rF) := by
      intro e he
      rw [← hEdgeId rF]
      exact hFrozenRange e he
    have hInclude := eventually_latticeBox_subset_of_exhaustion V hNest hExhaust rF
    have hSupport : ∀ᶠ n : ℕ in atTop,
        ∀ e ∈ F, ∃ g : (pottsESGraph (V n)).edgeSet,
          ((pottsESEdgeEquiv (V n)).symm g).1 = e.1 := by
      filter_upwards [hInclude] with n hInc
      intro e he
      obtain ⟨f, hf⟩ := Set.mem_range.mp (hFBox e he)
      obtain ⟨g, hg⟩ := pottsESBoxEdge_shellWitness (V n) rF hInc f
      exact ⟨g, hg.trans (congrArg Subtype.val hf)⟩
    have hShell := pottsESWiredShell_allOpenProbability_tendsto θ V hNest hExhaust μ hμ F
    have hReal : Tendsto
        (fun n => (pottsESShellBondProbabilityMeasure θ (V n) :
          Measure LatticeConfiguration).real (LatticeConfiguration.allOpen F)) atTop
        (𝓝 (μ.real (LatticeConfiguration.allOpen F))) := by
      apply hShell.congr'
      filter_upwards [hSupport] with n hn
      have hid := pottsESShellBondProbabilityMeasure_allOpen θ (V n) F hn
      simpa only [Measure.real] using (congrArg ENNReal.toReal hid).symm
    have hμν : μ.real (LatticeConfiguration.allOpen F) =
        (ν (LatticeConfiguration.allOpen F) : ℝ) := by
      change (ν : Measure LatticeConfiguration).real
          (LatticeConfiguration.allOpen F) =
        (ν (LatticeConfiguration.allOpen F) : ℝ)
      exact ProbabilityMeasure.measureReal_eq_coe_coeFn ν _
    have hCoe : Tendsto
        (fun n => (pottsESShellBondProbabilityMeasure θ (V n)
          (LatticeConfiguration.allOpen F) : ℝ)) atTop
        (𝓝 (ν (LatticeConfiguration.allOpen F) : ℝ)) := by
      simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, Function.comp_def,
        hμν] using hReal
    exact NNReal.tendsto_coe.mp hCoe
  let κ := cylinderProbabilityCoordinates
  have hκcont : Continuous κ := continuous_cylinderProbabilityCoordinates
  have hκinj : Function.Injective κ := by
    intro μ₁ μ₂ h
    apply LatticeConfiguration.probabilityMeasure_eq_of_allOpen
    intro F
    exact congrFun h F
  have hκembed : IsClosedEmbedding κ := hκcont.isClosedEmbedding hκinj
  have hκtendsto : Tendsto (fun n => κ (pottsESShellBondProbabilityMeasure θ (V n)))
      atTop (𝓝 (κ ν)) := by
    apply tendsto_pi_nhds.2
    intro F
    exact hAllOpen F
  have hfull := hκembed.tendsto_nhds_iff.mpr hκtendsto
  simpa [κ, ν] using hfull

end

end PottsContinuity.Thm1
