module

public import PottsContinuity.Thm1.ShellPairPatterns
public import PottsContinuity.Thm1.ShellExitFiniteComparison
public import PottsContinuity.Infinite.LocalComparisons
public import PottsContinuity.PD.RCInfinite.FiniteEnergy

@[expose] public section

namespace PottsContinuity.Thm1

open MeasureTheory
open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

attribute [local instance] configurationMeasurableSpace

theorem pottsESShellUpperCylinder_lower_bound
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : PD.IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (V : Finset (ℤ × ℤ)) (E : Set LatticeConfiguration)
    (hE : IsCylinder E)
    (hDepends : DependsOn (pottsESLatticeEdgeSet V :
      Set PottsContinuity.PD.FK.squareLattice.edgeSet) E)
    (hUpper : IsUpperSet E) :
    μ.real E ≤
      (pottsESShellBondProbabilityMeasure θ V :
        Measure LatticeConfiguration).real E := by
  classical
  let R := pottsESShellComparisonRadius V
  have hEdges := pottsESLatticeEdgeSet_subset_shellComparisonBox V
  have hDependsBox : DependsOn (boxEdges (0, 0) R) E := by
    exact PottsContinuity.PD.RCInfinite.DependsOn.mono hDepends
      (by simpa [R] using hEdges)
  have hLimitBox := PottsContinuity.Infinite.limit_le_wired_box_local
    θ μ hμ R hE hDependsBox hUpper
  have hBox : μ.real E ≤ (boxMeasure θ 1 (0, 0) R :
      Measure LatticeConfiguration).real E := hLimitBox
  let S : Set (Configuration (pottsESGraph V)) :=
    {A | pottsESShellBondExtension V A ∈ E}
  have hSUpper : IsUpperSet S := by
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
    change pottsESShellBondExtension V A ∈ E at hA
    exact hUpper hExtension hA
  have hRestriction (A : Configuration (boxGraph (0, 0) R)) :
      embeddedConfigurationRestriction (pottsESGraph V)
        (boxGraph (0, 0) R) (pottsESShellToBoxEmbedding V)
        (pottsESShellToBoxEmbedding_map_le V) A ∈ S ↔
      boxExtension 1 (0, 0) R A ∈ E := by
    apply hDepends
    intro e he
    obtain ⟨f, hf⟩ := (pottsESLatticeEdgeSet_mem_iff V e).mp he
    let g : (pottsESGraph V).edgeSet := pottsESEdgeEquiv V f
    let gBox := embeddedEdgeEmbedding (pottsESGraph V) (boxGraph (0, 0) R)
      (pottsESShellToBoxEmbedding V) (pottsESShellToBoxEmbedding_map_le V) g
    have hEmbedded : boxEdgeEmbedding (0, 0) R gBox = e := by
      apply Subtype.ext
      rw [pottsESShellEmbeddedEdge_original]
      simp [g, hf]
    have hRestrict : g ∈
        embeddedConfigurationRestriction (pottsESGraph V)
          (boxGraph (0, 0) R) (pottsESShellToBoxEmbedding V)
          (pottsESShellToBoxEmbedding_map_le V) A ↔ gBox ∈ A := by
      exact mem_embeddedConfigurationRestriction _ _ _ _ A g
    have hShellOpen :
        pottsESShellBondExtension V
          (embeddedConfigurationRestriction (pottsESGraph V)
            (boxGraph (0, 0) R) (pottsESShellToBoxEmbedding V)
            (pottsESShellToBoxEmbedding_map_le V) A) e = true ↔ g ∈
          embeddedConfigurationRestriction (pottsESGraph V)
            (boxGraph (0, 0) R) (pottsESShellToBoxEmbedding V)
            (pottsESShellToBoxEmbedding_map_le V) A := by
      rw [pottsESShellBondExtension_edge_open_iff]
      constructor
      · rintro ⟨g', hg', hge'⟩
        have hgg' : g' = g := by
          apply (pottsESEdgeEquiv V).symm.injective
          apply Subtype.ext
          exact hge'.trans (by simp [g, hf])
        simpa [hgg'] using hg'
      · intro hg
        exact ⟨g, hg, by simp [g, hf]⟩
    have hBoxAt := boxExtension_at 1 (0, 0) R A gBox
    have hBoxOpen : boxExtension 1 (0, 0) R A e = true ↔ gBox ∈ A := by
      have hState : boxExtension 1 (0, 0) R A e =
          boxExtension 1 (0, 0) R A (boxEdgeEmbedding (0, 0) R gBox) :=
        congrArg (boxExtension 1 (0, 0) R A) hEmbedded.symm
      rw [hState, hBoxAt]
      simp
    have hSame :
        pottsESShellBondExtension V
          (embeddedConfigurationRestriction (pottsESGraph V)
            (boxGraph (0, 0) R) (pottsESShellToBoxEmbedding V)
            (pottsESShellToBoxEmbedding_map_le V) A) e = true ↔
        boxExtension 1 (0, 0) R A e = true :=
      hShellOpen.trans (hRestrict.trans hBoxOpen.symm)
    exact Bool.eq_iff_iff.mpr hSame
  have hEvent :
      {A | embeddedConfigurationRestriction (pottsESGraph V)
        (boxGraph (0, 0) R) (pottsESShellToBoxEmbedding V)
        (pottsESShellToBoxEmbedding_map_le V) A ∈ S} =
      {A | boxExtension 1 (0, 0) R A ∈ E} := by
    ext A
    exact hRestriction A
  have hCompare := wiredBox_restriction_le_pottsESWiredShell V θ S hSUpper
  rw [hEvent] at hCompare
  have hBoxEq : (boxMeasure θ 1 (0, 0) R :
      Measure LatticeConfiguration).real E =
      (measure (boxGraph (0, 0) R) θ
        (BoundaryCondition.wired (boxVertexBoundary (0, 0) R))
        {A | boxExtension 1 (0, 0) R A ∈ E}).toReal := by
    rw [Measure.real, boxMeasure_apply θ 1 (0, 0) R hE.measurableSet]
    simp [boxBoundary, Set.preimage]
  have hBox' := hBox
  rw [hBoxEq] at hBox'

  have hShell :
      (pottsESShellBondProbabilityMeasure θ V :
        Measure LatticeConfiguration).real E =
      (measure (pottsESGraph V) θ (pottsESBoundaryCondition V) S).toReal := by
    rw [Measure.real, pottsESShellBondProbabilityMeasure_apply θ V hE.measurableSet]
  rw [hShell]
  exact hBox'.trans hCompare

end

end PottsContinuity.Thm1
