/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/ParafermionicCoverToggle.lean`.
Adaptation: namespace relocation, existing PD finite-edge embedding and real-parameter toggle.
-/
module

public import PottsContinuity.Thm4.CriticalEdgeToggle
public import PottsContinuity.Thm4.CoverConfiguration
public import PottsContinuity.Thm4.CoverPorts

@[expose] public section

namespace PottsContinuity.Thm4.Medial

open PottsContinuity.PD.FK PottsContinuity.Thm4

noncomputable section

/-- The actual graph embedding of a finite ambient edge into the whole cover graph. -/
def parafermionicCoverFiniteEdgeEmbedding (n : ℕ) :
    (ParafermionicAmbientGraph n).edgeSet ↪ parafermionicCoverGraph.edgeSet :=
  embeddedEdgeEmbedding (ParafermionicAmbientGraph n) parafermionicCoverGraph
    (parafermionicCoverBoxVertexEmbedding n) (parafermionicCoverBoxGraph_map_le n)

theorem parafermionicCoverConfigurationExtensionState_toggle_at_image
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverConfigurationExtensionState n (toggleEdgeConfiguration e A)
        (parafermionicCoverFiniteEdgeEmbedding n e) =
      !(parafermionicCoverConfigurationExtensionState n A
        (parafermionicCoverFiniteEdgeEmbedding n e)) := by
  classical
  unfold parafermionicCoverConfigurationExtensionState parafermionicCoverFiniteEdgeEmbedding
  have h₁ : decide (embeddedEdgeEmbedding (ParafermionicAmbientGraph n)
      parafermionicCoverGraph (parafermionicCoverBoxVertexEmbedding n)
      (parafermionicCoverBoxGraph_map_le n) e ∈
      parafermionicCoverConfigurationExtension n (toggleEdgeConfiguration e A)) =
      decide (e ∈ toggleEdgeConfiguration e A) := by
    by_cases hp : embeddedEdgeEmbedding (ParafermionicAmbientGraph n)
        parafermionicCoverGraph (parafermionicCoverBoxVertexEmbedding n)
        (parafermionicCoverBoxGraph_map_le n) e ∈
        parafermionicCoverConfigurationExtension n (toggleEdgeConfiguration e A)
    · have hq := (parafermionicCoverConfigurationExtension_inside
        n (toggleEdgeConfiguration e A) e).mp hp
      simp [hp, hq]
    · have hq : e ∉ toggleEdgeConfiguration e A := by
        intro hq
        exact hp ((parafermionicCoverConfigurationExtension_inside
          n (toggleEdgeConfiguration e A) e).mpr hq)
      simp [hp, hq]
  have h₂ : decide (embeddedEdgeEmbedding (ParafermionicAmbientGraph n)
      parafermionicCoverGraph (parafermionicCoverBoxVertexEmbedding n)
      (parafermionicCoverBoxGraph_map_le n) e ∈
      parafermionicCoverConfigurationExtension n A) = decide (e ∈ A) := by
    by_cases hp : embeddedEdgeEmbedding (ParafermionicAmbientGraph n)
        parafermionicCoverGraph (parafermionicCoverBoxVertexEmbedding n)
        (parafermionicCoverBoxGraph_map_le n) e ∈ parafermionicCoverConfigurationExtension n A
    · have hq := (parafermionicCoverConfigurationExtension_inside n A e).mp hp
      simp [hp, hq]
    · have hq : e ∉ A := by
        intro hq
        exact hp ((parafermionicCoverConfigurationExtension_inside n A e).mpr hq)
      simp [hp, hq]
  have hflip : decide (e ∈ toggleEdgeConfiguration e A) = !decide (e ∈ A) := by
    by_cases he : e ∈ A <;> simp [toggleEdgeConfiguration, he]
  simp only [h₁, h₂, hflip]

/-- Toggling a finite edge changes exactly its actual embedded cover edge in the
closed-outside whole-cover extension. -/
theorem parafermionicCoverConfigurationExtensionState_toggle
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (f : parafermionicCoverGraph.edgeSet) :
    parafermionicCoverConfigurationExtensionState n (toggleEdgeConfiguration e A) f =
      if f = parafermionicCoverFiniteEdgeEmbedding n e then
        !(parafermionicCoverConfigurationExtensionState n A f)
      else parafermionicCoverConfigurationExtensionState n A f := by
  classical
  by_cases hf : f = parafermionicCoverFiniteEdgeEmbedding n e
  · subst f
    simpa using parafermionicCoverConfigurationExtensionState_toggle_at_image n A e
  · have hmem : f ∈ parafermionicCoverConfigurationExtension n (toggleEdgeConfiguration e A) ↔
        f ∈ parafermionicCoverConfigurationExtension n A := by
      rw [parafermionicCoverConfigurationExtension,
        parafermionicCoverConfigurationExtension]
      constructor
      · intro h
        rcases Finset.mem_map.mp h with ⟨g, hg, hgf⟩
        have hge : g ≠ e := by
          intro hge
          apply hf
          calc
            f = embeddedEdgeEmbedding (ParafermionicAmbientGraph n)
                parafermionicCoverGraph (parafermionicCoverBoxVertexEmbedding n)
                (parafermionicCoverBoxGraph_map_le n) g := hgf.symm
            _ = parafermionicCoverFiniteEdgeEmbedding n e := by
              rw [hge]
              change embeddedEdgeEmbedding (ParafermionicAmbientGraph n)
                parafermionicCoverGraph (parafermionicCoverBoxVertexEmbedding n)
                (parafermionicCoverBoxGraph_map_le n) e =
                embeddedEdgeEmbedding (ParafermionicAmbientGraph n)
                parafermionicCoverGraph (parafermionicCoverBoxVertexEmbedding n)
                (parafermionicCoverBoxGraph_map_le n) e
              rfl
        exact Finset.mem_map.mpr
          ⟨g, (toggleEdgeConfiguration_mem_of_ne A hge).mp hg, hgf⟩
      · intro h
        rcases Finset.mem_map.mp h with ⟨g, hg, hgf⟩
        have hge : g ≠ e := by
          intro hge
          apply hf
          calc
            f = embeddedEdgeEmbedding (ParafermionicAmbientGraph n)
                parafermionicCoverGraph (parafermionicCoverBoxVertexEmbedding n)
                (parafermionicCoverBoxGraph_map_le n) g := hgf.symm
            _ = parafermionicCoverFiniteEdgeEmbedding n e := by
              rw [hge]
              change embeddedEdgeEmbedding (ParafermionicAmbientGraph n)
                parafermionicCoverGraph (parafermionicCoverBoxVertexEmbedding n)
                (parafermionicCoverBoxGraph_map_le n) e =
                embeddedEdgeEmbedding (ParafermionicAmbientGraph n)
                parafermionicCoverGraph (parafermionicCoverBoxVertexEmbedding n)
                (parafermionicCoverBoxGraph_map_le n) e
              rfl
        exact Finset.mem_map.mpr
          ⟨g, (toggleEdgeConfiguration_mem_of_ne A hge).mpr hg, hgf⟩
    unfold parafermionicCoverConfigurationExtensionState
    have hbool : decide (f ∈ parafermionicCoverConfigurationExtension n
        (toggleEdgeConfiguration e A)) =
        decide (f ∈ parafermionicCoverConfigurationExtension n A) := by
      by_cases hp : f ∈ parafermionicCoverConfigurationExtension n
          (toggleEdgeConfiguration e A)
      · have hq := hmem.mp hp
        simp [hp, hq]
      · have hq : f ∉ parafermionicCoverConfigurationExtension n A := by
          intro hq
          exact hp (hmem.mpr hq)
        simp [hp, hq]
    simp [hf, hbool]

/-- At a lifted port, the toggle affects its queried actual edge exactly when that
cover edge is the embedded finite edge. -/
theorem parafermionicCoverPortBondState_toggle
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (c : ParafermionicCoverPort) :
    parafermionicCoverPortBondState
        (parafermionicCoverConfigurationExtensionState n (toggleEdgeConfiguration e A)) c =
      if parafermionicCoverPortEdge c = parafermionicCoverFiniteEdgeEmbedding n e then
        !(parafermionicCoverPortBondState
          (parafermionicCoverConfigurationExtensionState n A) c)
      else parafermionicCoverPortBondState
        (parafermionicCoverConfigurationExtensionState n A) c := by
  exact parafermionicCoverConfigurationExtensionState_toggle n A e
    (parafermionicCoverPortEdge c)

/-- A lifted port whose actual incident cover edge is not toggled keeps its local pairing. -/
theorem parafermionicCoverLocalPair_toggle_eq_of_edge_ne
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (c : ParafermionicCoverPort)
    (hne : parafermionicCoverPortEdge c ≠ parafermionicCoverFiniteEdgeEmbedding n e) :
    parafermionicCoverLocalPair
        (parafermionicCoverConfigurationExtensionState n (toggleEdgeConfiguration e A)) c =
      parafermionicCoverLocalPair (parafermionicCoverConfigurationExtensionState n A) c := by
  rw [parafermionicCoverLocalPair, parafermionicCoverLocalPair,
    parafermionicCoverPortBondState_toggle]
  simp [hne]

end
end PottsContinuity.Thm4.Medial
