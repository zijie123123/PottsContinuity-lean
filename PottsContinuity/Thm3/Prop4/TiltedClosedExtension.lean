module

public import PottsContinuity.Thm3.Prop4.TiltedIncidentEvents
public import PottsContinuity.Thm3.Prop4.ArcIsolationEmbedding
public import PottsContinuity.Thm3.Prop4.TiltedLimit

/-! # Exact actual strip graph of a closed finite-window extension -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- The two literal original-edge embeddings compose exactly. -/
theorem tiltedWindowStrip_plane_edge (n M : ℕ) (t : ℝ)
    (e : (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet) :
    (tiltedPlaneEmbedding n t).mapEdgeSet ((tiltedWindowStripEmbedding n M t).mapEdgeSet e) =
      (tiltedWindowPlaneEmbedding n M t).mapEdgeSet e := by
  apply Subtype.ext
  change Sym2.map Subtype.val (Sym2.map (tiltedWindowStripEmbedding n M t) e.val) =
    Sym2.map Subtype.val e.val
  rw [Sym2.map_map]
  rfl

/-- Reading a plane extension on the strip agrees with closing every unsampled strip edge. -/
theorem tiltedClosedExtension_state (n M : ℕ) (t : ℝ)
    (A : Configuration (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))))
    (e : (tiltedStripGraph n t).edgeSet) :
    tiltedPlaneRestriction n t (tiltedWindowPlaneConfiguration n M t A) e =
      decide (e ∈ A.map (tiltedWindowStripEmbedding n M t).mapEdgeSet) := by
  classical
  apply Bool.eq_iff_iff.mpr
  unfold tiltedPlaneRestriction tiltedWindowPlaneConfiguration
  simp only [decide_eq_true_eq]
  constructor
  · intro he
    obtain ⟨f,hf,hfe⟩ := Finset.mem_map.mp he
    apply Finset.mem_map.mpr
    refine ⟨f,hf,?_⟩
    apply (tiltedPlaneEmbedding n t).mapEdgeSet.injective
    rw [tiltedWindowStrip_plane_edge]
    exact hfe
  · intro he
    obtain ⟨f,hf,hfe⟩ := Finset.mem_map.mp he
    apply Finset.mem_map.mpr
    refine ⟨f,hf,?_⟩
    have h := congrArg (tiltedPlaneEmbedding n t).mapEdgeSet hfe
    rw [tiltedWindowStrip_plane_edge] at h
    exact h

/-- The infinite actual graph has precisely the sampled finite graph, with all other vertices isolated. -/
theorem tiltedClosedExtension_openGraph (n M : ℕ) (t : ℝ)
    (A : Configuration (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ)))) :
    tiltedOpenGraph n t (tiltedPlaneRestriction n t (tiltedWindowPlaneConfiguration n M t A)) =
      (openGraph (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))) A).map
        (tiltedWindowStripEmbedding n M t).toEmbedding := by
  classical
  have hgraph : tiltedOpenGraph n t
      (tiltedPlaneRestriction n t (tiltedWindowPlaneConfiguration n M t A)) =
      openGraph (tiltedStripGraph n t) (A.map (tiltedWindowStripEmbedding n M t).mapEdgeSet) := by
    change SimpleGraph.fromEdgeSet _ = SimpleGraph.fromEdgeSet _
    congr 1
    ext e
    constructor
    · rintro ⟨he,hω⟩
      have hmem : (⟨e,he⟩ : (tiltedStripGraph n t).edgeSet) ∈
          A.map (tiltedWindowStripEmbedding n M t).mapEdgeSet := by
        rw [tiltedClosedExtension_state] at hω
        exact of_decide_eq_true hω
      exact ⟨⟨e,he⟩,hmem,rfl⟩
    · rintro ⟨e,he,rfl⟩
      refine ⟨e.property,?_⟩
      rw [tiltedClosedExtension_state]
      exact decide_eq_true he
  rw [hgraph]
  apply SimpleGraph.edgeSet_injective
  rw [openGraph_edgeSet,SimpleGraph.edgeSet_map,openGraph_edgeSet]
  simp only [openEdges,Finset.coe_map,Set.image_image]
  rfl

end
end PottsContinuity.Thm3.Prop4
