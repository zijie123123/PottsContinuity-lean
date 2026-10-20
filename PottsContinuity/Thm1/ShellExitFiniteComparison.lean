module

public import PottsContinuity.Thm1.ShellExitComparison
public import PottsContinuity.Thm1.ShellOuterCylinderBridge
public import PottsContinuity.Thm1.ShellPathBridge
public import PottsContinuity.Thm1.ShellBondLimit
public import PottsContinuity.PD.RCInfinite.FiniteEnergy

@[expose] public section

namespace PottsContinuity.Thm1

open MeasureTheory
open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

theorem pottsESLatticeEdgeSet_subset_shellComparisonBox (V : Finset (ℤ × ℤ)) :
    (pottsESLatticeEdgeSet V : Set
      PottsContinuity.PD.FK.squareLattice.edgeSet) ⊆
      boxEdges (0, 0) (pottsESShellComparisonRadius V) := by
  intro e he
  rw [mem_boxEdges_iff]
  intro x hx
  obtain ⟨f, hf⟩ := (pottsESLatticeEdgeSet_mem_iff V e).mp he
  have hx' : x ∈ f.1 := by rw [hf]; exact hx
  have hxSupport := pottsEdges_endpoints_support V f.2 hx'
  have hxBase := subgraph_subset_boxRadius (pottsESSupport V) hxSupport
  exact latticeBox_mono (0, 0) (by
    dsimp [pottsESShellComparisonRadius]
    omega) hxBase

theorem pottsESOriginExteriorConnected_upper (V : Finset (ℤ × ℤ))
    (h0 : (0, 0) ∈ V) :
    IsUpperSet {A : Configuration (pottsESGraph V) |
      pottsESOriginExteriorConnected V h0 A} := by
  intro A B hAB hA
  have hExtension : pottsESShellBondExtension V A ≤
      pottsESShellBondExtension V B := by
    intro e
    apply Bool.le_iff_imp.mpr
    intro hOpen
    obtain ⟨g, hgA, hge⟩ :=
      (pottsESShellBondExtension_edge_open_iff V A e).mp hOpen
    exact (pottsESShellBondExtension_edge_open_iff V B e).mpr
      ⟨g, hAB hgA, hge⟩
  change pottsESOriginExteriorConnected V h0 A at hA
  change pottsESOriginExteriorConnected V h0 B
  rw [pottsESOriginExteriorConnected_iff_latticeExit V h0] at hA ⊢
  change pottsESLatticeExitEvent V (pottsESShellBondExtension V A) at hA
  change pottsESLatticeExitEvent V (pottsESShellBondExtension V B)
  exact pottsESLatticeExitEvent_upper V hExtension hA

theorem pottsESShellRestriction_exit_iff
    (V : Finset (ℤ × ℤ)) (h0 : (0, 0) ∈ V)
    (A : Configuration (boxGraph (0, 0) (pottsESShellComparisonRadius V))) :
    pottsESOriginExteriorConnected V h0
      (embeddedConfigurationRestriction (pottsESGraph V)
        (boxGraph (0, 0) (pottsESShellComparisonRadius V))
        (pottsESShellToBoxEmbedding V) (pottsESShellToBoxEmbedding_map_le V) A) ↔
      boxExtension 1 (0, 0) (pottsESShellComparisonRadius V) A ∈
        pottsESLatticeExitEvent V := by
  let B := embeddedConfigurationRestriction (pottsESGraph V)
    (boxGraph (0, 0) (pottsESShellComparisonRadius V))
    (pottsESShellToBoxEmbedding V) (pottsESShellToBoxEmbedding_map_le V) A
  have hstate : ∀ e ∈ pottsESLatticeEdgeSet V,
      pottsESShellBondExtension V B e =
        boxExtension 1 (0, 0) (pottsESShellComparisonRadius V) A e := by
    intro e he
    obtain ⟨f, hfe⟩ := (pottsESLatticeEdgeSet_mem_iff V e).mp he
    let g : (pottsESGraph V).edgeSet := pottsESEdgeEquiv V f
    let eBox := embeddedEdgeEmbedding (pottsESGraph V)
      (boxGraph (0, 0) (pottsESShellComparisonRadius V))
      (pottsESShellToBoxEmbedding V) (pottsESShellToBoxEmbedding_map_le V) g
    have hEmbedded : boxEdgeEmbedding (0, 0) (pottsESShellComparisonRadius V) eBox = e := by
      apply Subtype.ext
      rw [pottsESShellEmbeddedEdge_original]
      simp [g, hfe]
    have hRestrict : g ∈ B ↔ eBox ∈ A := by
      dsimp [B]
      exact mem_embeddedConfigurationRestriction _ _ _ _ A g
    have hOrig : ((pottsESEdgeEquiv V).symm g).1 = e.1 := by
      simp [g, hfe]
    have hOpen : pottsESShellBondExtension V B e = true ↔ g ∈ B := by
      rw [pottsESShellBondExtension_edge_open_iff]
      constructor
      · rintro ⟨g', hg', hge'⟩
        have hgg' : g' = g := by
          apply (pottsESEdgeEquiv V).symm.injective
          apply Subtype.ext
          exact hge'.trans hOrig.symm
        simpa [hgg'] using hg'
      · intro hg
        exact ⟨g, hg, hOrig⟩
    have hOpenBox :
        boxExtension 1 (0, 0) (pottsESShellComparisonRadius V) A e = true ↔
          eBox ∈ A := by
      rw [← hEmbedded, boxExtension_at]
      simp
    have hSameOpen : pottsESShellBondExtension V B e = true ↔
        boxExtension 1 (0, 0) (pottsESShellComparisonRadius V) A e = true :=
      hOpen.trans (hRestrict.trans hOpenBox.symm)
    by_cases hval : eBox ∈ A
    · have hs : pottsESShellBondExtension V B e = true :=
        hOpen.mpr (hRestrict.mpr hval)
      have hb : boxExtension 1 (0, 0) (pottsESShellComparisonRadius V) A e = true :=
        hOpenBox.mpr hval
      rw [hs, hb]
    · have hs : pottsESShellBondExtension V B e ≠ true := by
        intro hs
        exact hval (hRestrict.mp (hOpen.mp hs))
      have hb : boxExtension 1 (0, 0) (pottsESShellComparisonRadius V) A e ≠ true := by
        intro hb
        exact hval (hOpenBox.mp hb)
      cases hShell : pottsESShellBondExtension V B e <;>
        cases hBox : boxExtension 1 (0, 0) (pottsESShellComparisonRadius V) A e <;>
        simp_all
  have hEvent := pottsESLatticeExitEvent_dependsOn V h0
    (pottsESShellBondExtension V B)
    (boxExtension 1 (0, 0) (pottsESShellComparisonRadius V) A) hstate
  have hPath := pottsESOriginExteriorConnected_iff_latticeExit V h0 B
  simpa [B, pottsESLatticeExitEvent] using hPath.trans hEvent

theorem pottsESLatticeExitProbability_le_pottsESShell
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : PottsContinuity.PD.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 1 μ)
    (V : Finset (ℤ × ℤ)) (h0 : (0, 0) ∈ V) :
    μ.real (pottsESLatticeExitEvent V) ≤
      (measure (pottsESGraph V) θ (pottsESBoundaryCondition V)
        {A | pottsESOriginExteriorConnected V h0 A}).toReal := by
  let R := pottsESShellComparisonRadius V
  have hBox := pottsESLatticeExitProbability_le_wiredBox θ μ hμ V h0 R
    (pottsESLatticeEdgeSet_subset_shellComparisonBox V)
  have hMeas : MeasurableSet (pottsESLatticeExitEvent V) :=
    (pottsESLatticeExitEvent_isCylinder V h0).measurableSet
  simp only [Measure.real, boxMeasure_apply θ 1 (0, 0) R hMeas] at hBox
  let S : Set (Configuration (pottsESGraph V)) :=
    {A | pottsESOriginExteriorConnected V h0 A}
  have hEvent :
      {A | embeddedConfigurationRestriction (pottsESGraph V)
        (boxGraph (0, 0) R) (pottsESShellToBoxEmbedding V)
        (pottsESShellToBoxEmbedding_map_le V) A ∈ S} =
      (boxExtension 1 (0, 0) R) ⁻¹' pottsESLatticeExitEvent V := by
    ext A
    simpa [S, R, Set.mem_preimage] using
      pottsESShellRestriction_exit_iff V h0 A
  rw [← hEvent] at hBox
  have hCompare := wiredBox_restriction_le_pottsESWiredShell V θ S
    (pottsESOriginExteriorConnected_upper V h0)
  simpa only [Measure.real, S] using hBox.trans hCompare

end

end PottsContinuity.Thm1
