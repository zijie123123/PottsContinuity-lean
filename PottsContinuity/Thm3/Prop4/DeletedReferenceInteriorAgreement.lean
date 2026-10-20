module

public import PottsContinuity.Thm3.Prop4.DeletedAmbientDualLaw
public import PottsContinuity.Thm3.Prop4.ArcIsolationLocality

/-!
# Agreement of the actual reference on every edge incident to an interior face

Ambient edges absent from the true sampled dual have both endpoints on the
physical exterior. Deletion of genuine crossed reveals preserves interior
agreement, and restriction keeps the exact original open-edge states there.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

/-- Every retained ambient edge meeting a physical interior face is a retained
edge of the genuine sampled dual graph. -/
theorem rectangle_deleted_ambient_adj_actual_of_left_interior (a : LatticeVertex) (w h : ℕ)
    (R : Configuration (rectangleGraph a w h)) (x y : RectangleDualVertex a w h)
    (hx : x.val ∈ rectangleDualInterior a w h)
    (hxy : (edgeRestriction (rectangleDualAmbientGraph a w h)
      (rectangleAmbientCrossedReveal a w h R)).Adj x y) :
    (edgeRestriction (rectangleDualGraph a w h) (rectangleCrossedEdges a w h R)).Adj x y := by
  have hopen := congrArg SimpleGraph.edgeSet
    (openGraph_subgraphConfigurationEmbedding (rectangleDualGraph_le_ambient a w h)
      (rectangleCrossedEdges a w h R))
  simp only [openGraph_edgeSet] at hopen
  simp only [edgeRestriction,SimpleGraph.deleteEdges_adj] at hxy ⊢
  exact ⟨rectangleDualAmbient_adj_actual_of_left_interior a w h x y hx hxy.1,
    by rw [← hopen]; exact hxy.2⟩

private theorem restriction_open_adj_iff {V : Type*} {G H : SimpleGraph V}
    (hGH : G ≤ H) (A : Configuration H) (x y : V) :
    (openGraph G (subgraphConfigurationRestriction hGH A)).Adj x y ↔
      G.Adj x y ∧ (openGraph H A).Adj x y := by
  constructor
  · intro hxy
    have hg := openGraph_le G _ hxy
    obtain ⟨e,he,hval⟩ := (openGraph_adj G _ x y).mp hxy
    refine ⟨hg,(openGraph_adj H A x y).mpr ?_⟩
    exact ⟨subgraphEdgeEmbedding hGH e,(mem_subgraphConfigurationRestriction hGH A e).mp he,hval⟩
  · rintro ⟨hg,hh⟩
    obtain ⟨e,he,hval⟩ := (openGraph_adj H A x y).mp hh
    let g : G.edgeSet := ⟨s(x,y),G.mem_edgeSet.mpr hg⟩
    have hge : subgraphEdgeEmbedding hGH g = e := Subtype.ext hval.symm
    apply (openGraph_adj G _ x y).mpr
    refine ⟨g,(mem_subgraphConfigurationRestriction hGH A g).mpr ?_,rfl⟩
    rw [hge]
    exact he

/-- The two actual sampled open graphs agree on every edge incident to an
interior face, with the smaller sample given by the exact law restriction. -/
theorem rectangle_deleted_open_interior_agreement (a : LatticeVertex) (w h : ℕ)
    (R : Configuration (rectangleGraph a w h))
    (A : Configuration (edgeRestriction (rectangleDualAmbientGraph a w h) (rectangleAmbientCrossedReveal a w h R)))
    (x : RectangleDualVertex a w h) (hx : x.val ∈ rectangleDualInterior a w h)
    (y : RectangleDualVertex a w h) :
    (openGraph _ A).Adj x y ↔
      (openGraph (edgeRestriction (rectangleDualGraph a w h) (rectangleCrossedEdges a w h R))
        (subgraphConfigurationRestriction (rectangle_deleted_dual_le_ambient a w h R) A)).Adj x y := by
  rw [restriction_open_adj_iff]
  constructor
  · intro hxy
    exact ⟨rectangle_deleted_ambient_adj_actual_of_left_interior a w h R x y hx
      (openGraph_le _ A hxy),hxy⟩
  · exact And.right

end
end PottsContinuity.Thm3.Prop4
