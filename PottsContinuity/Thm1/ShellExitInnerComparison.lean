module

public import PottsContinuity.Thm1.ShellExitFiniteComparison
public import PottsContinuity.Thm1.ShellCylinderBridge
public import PottsContinuity.PD.FK.WiredBoxLaw

@[expose] public section

namespace PottsContinuity.Thm1

open MeasureTheory
open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite
attribute [local instance] configurationMeasurableSpace

noncomputable section

local instance pottsESExitVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype (PottsESVertex V) := Fintype.ofFinite _

local instance pottsESExitEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (pottsESGraph V).edgeSet := Fintype.ofFinite _

local instance pottsESExitEdgeDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (pottsESGraph V).edgeSet := Classical.decEq _

theorem pottsESShellBoxRestriction_exitEvent_iff
    (V : Finset (ℤ × ℤ)) (r : ℕ)
    (hV : latticeBox (0, 0) r ⊆ V)
    (W : Finset (ℤ × ℤ)) (h0W : (0, 0) ∈ W)
    (hW : (pottsESLatticeEdgeSet W : Set
      PottsContinuity.PD.FK.squareLattice.edgeSet) ⊆
      boxEdges (0, 0) r)
    (A : Configuration (pottsESGraph V)) :
    pottsESLatticeExitEvent W (pottsESShellBondExtension V A) ↔
      pottsESLatticeExitEvent W
        (boxExtension 1 (0, 0) r
          (embeddedConfigurationRestriction (boxGraph (0, 0) r)
            (pottsESGraph V) (pottsESBoxEmbedding V r hV)
            (pottsESBoxEmbedding_map_le V r hV) A)) := by
  classical
  let C := embeddedConfigurationRestriction (boxGraph (0, 0) r)
    (pottsESGraph V) (pottsESBoxEmbedding V r hV)
    (pottsESBoxEmbedding_map_le V r hV) A
  have hstates : ∀ e ∈ pottsESLatticeEdgeSet W,
      pottsESShellBondExtension V A e = boxExtension 1 (0, 0) r C e := by
    intro e he
    have hboxRange := boxEdges_subset_frozenEdgeEmbedding_range r (hW he)
    have hEdgeId : frozenEdgeEmbedding (latticeBox (0, 0) r) =
        boxEdgeEmbedding (0, 0) r := rfl
    rw [hEdgeId] at hboxRange
    obtain ⟨f, hf⟩ := hboxRange
    let g := embeddedEdgeEmbedding (boxGraph (0, 0) r)
      (pottsESGraph V) (pottsESBoxEmbedding V r hV)
      (pottsESBoxEmbedding_map_le V r hV) f
    have hOriginal : ((pottsESEdgeEquiv V).symm g).1 = e.1 := by
      calc
        ((pottsESEdgeEquiv V).symm g).1 =
            (boxEdgeEmbedding (0, 0) r f).1 :=
              pottsESBoxEmbeddedEdge_original V r hV f
        _ = e.1 := congrArg Subtype.val hf
    have hRestrict : f ∈ C ↔ g ∈ A := by
      dsimp [C]
      exact mem_embeddedConfigurationRestriction _ _ _ _ A f
    have hShellOpen : pottsESShellBondExtension V A e = true ↔ g ∈ A := by
      rw [pottsESShellBondExtension_edge_open_iff]
      constructor
      · rintro ⟨g', hg', hge'⟩
        have hgg' : g' = g := by
          apply (pottsESEdgeEquiv V).symm.injective
          apply Subtype.ext
          exact hge'.trans hOriginal.symm
        simpa [hgg'] using hg'
      · intro hg
        exact ⟨g, hg, hOriginal⟩
    have hBoxAt := boxExtension_at 1 (0, 0) r C f
    have hBoxOpen : boxExtension 1 (0, 0) r C e = true ↔ f ∈ C := by
      have hState : boxExtension 1 (0, 0) r C e =
          boxExtension 1 (0, 0) r C (boxEdgeEmbedding (0, 0) r f) :=
        congrArg (boxExtension 1 (0, 0) r C) hf.symm
      rw [hState, hBoxAt]
      simp
      exact Iff.rfl
    have hSameOpen : pottsESShellBondExtension V A e = true ↔
        boxExtension 1 (0, 0) r C e = true :=
      hShellOpen.trans (hRestrict.symm.trans hBoxOpen.symm)
    exact Bool.eq_iff_iff.mpr hSameOpen
  have hdep := pottsESLatticeExitEvent_dependsOn W h0W
  exact hdep (pottsESShellBondExtension V A)
    (boxExtension 1 (0, 0) r C) hstates

theorem pottsESOriginExteriorConnectionProbability_le_wiredBoxExit
    (θ : Parameters) (V : Finset (ℤ × ℤ)) (h0 : (0, 0) ∈ V)
    (r : ℕ) (hV : latticeBox (0, 0) r ⊆ V)
    (W : Finset (ℤ × ℤ)) (h0W : (0, 0) ∈ W) (hWV : W ⊆ V)
    (hW : (pottsESLatticeEdgeSet W : Set
      PottsContinuity.PD.FK.squareLattice.edgeSet) ⊆
      boxEdges (0, 0) r) :
    (measure (pottsESGraph V) θ (pottsESBoundaryCondition V)
      {A | pottsESOriginExteriorConnected V h0 A}).toReal ≤
    (boxMeasure θ 1 (0, 0) r : Measure LatticeConfiguration).real
      (pottsESLatticeExitEvent W) := by
  classical
  let S : Set (Configuration (boxGraph (0, 0) r)) :=
    (boxExtension 1 (0, 0) r) ⁻¹' pottsESLatticeExitEvent W
  have hExtMono : Monotone (boxExtension 1 (0, 0) r) := by
    intro A B hAB e
    by_cases he : e ∈ boxEdges (0, 0) r
    · obtain ⟨f, hf⟩ := he
      rw [← hf, boxExtension_at, boxExtension_at]
      by_cases hA : f ∈ A
      · have hB := hAB hA
        simp [hA, hB]
      · simp [hA]
    · simp [boxExtension, wiredBoxConfiguration_outside (0, 0) r A e he,
        wiredBoxConfiguration_outside (0, 0) r B e he]
  have hS : IsUpperSet S := by
    intro A B hAB hA
    exact pottsESLatticeExitEvent_upper W (hExtMono hAB) hA
  have hCompare := pottsESWiredShell_upper_le_wiredBox V θ r hV S hS
  have hEvent :
      {A | embeddedConfigurationRestriction (boxGraph (0, 0) r)
        (pottsESGraph V) (pottsESBoxEmbedding V r hV)
        (pottsESBoxEmbedding_map_le V r hV) A ∈ S} =
      {A | pottsESLatticeExitEvent W (pottsESShellBondExtension V A)} := by
    ext A
    change pottsESLatticeExitEvent W
        (boxExtension 1 (0, 0) r
          (embeddedConfigurationRestriction (boxGraph (0, 0) r)
            (pottsESGraph V) (pottsESBoxEmbedding V r hV)
            (pottsESBoxEmbedding_map_le V r hV) A)) ↔
      pottsESLatticeExitEvent W (pottsESShellBondExtension V A)
    exact (pottsESShellBoxRestriction_exitEvent_iff V r hV W h0W hW A).symm
  rw [hEvent] at hCompare
  have hSubset :
      {A : Configuration (pottsESGraph V) |
        pottsESOriginExteriorConnected V h0 A} ⊆
      {A | pottsESLatticeExitEvent W (pottsESShellBondExtension V A)} := by
    intro A hA
    change pottsESOriginExteriorConnected V h0 A at hA
    rw [pottsESOriginExteriorConnected_iff_latticeExit V h0] at hA
    obtain ⟨y, hy, hpath⟩ := hA
    exact ⟨y, fun hyW => hy (hWV hyW), hpath⟩
  have hSubMeasure :
      measure (pottsESGraph V) θ (pottsESBoundaryCondition V)
          {A | pottsESOriginExteriorConnected V h0 A} ≤
        measure (pottsESGraph V) θ (pottsESBoundaryCondition V)
          {A | pottsESLatticeExitEvent W (pottsESShellBondExtension V A)} :=
    measure_mono hSubset
  have hProbability : IsProbabilityMeasure
      (measure (pottsESGraph V) θ (pottsESBoundaryCondition V)) :=
    PottsContinuity.PD.FK.measure_isProbabilityMeasure
      (pottsESGraph V) θ
      (pottsESBoundaryCondition V)
  let := hProbability
  have hFinite := measure_ne_top (measure (pottsESGraph V) θ
    (pottsESBoundaryCondition V))
    {A | pottsESLatticeExitEvent W (pottsESShellBondExtension V A)}
  have hSubReal := ENNReal.toReal_mono hFinite hSubMeasure
  have hMeas : MeasurableSet (pottsESLatticeExitEvent W) :=
    (pottsESLatticeExitEvent_isCylinder W h0W).measurableSet
  have hBoxId :
      (boxMeasure θ 1 (0, 0) r : Measure LatticeConfiguration).real
          (pottsESLatticeExitEvent W) =
        (measure (boxGraph (0, 0) r) θ
          (BoundaryCondition.wired (boxVertexBoundary (0, 0) r)) S).toReal := by
    rw [Measure.real, boxMeasure_apply θ 1 (0, 0) r hMeas]
    simp [PottsContinuity.PD.RCInfinite.boxBoundary, S]
  exact hSubReal.trans (hCompare.trans (le_of_eq hBoxId.symm))

end

end PottsContinuity.Thm1
