module

public import PottsContinuity.Thm3.Prop4.MaximalStripCrop
public import PottsContinuity.Thm3.Prop4.UpperHalfPlaneCrossingBond
public import PottsContinuity.Thm3.Prop4.DeletedAmbientDualLaw

/-!
# An actual-root strip avoids all revealed original bonds below its tangent

This comparison permits arbitrary rectangle reveals. Its only source-record
input is containment of both endpoints of every revealed bond below the line.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

/-- The actual translated crop embeds into the literal deleted dual ambient
graph whenever the original reveal lies below the supporting line. -/
theorem maximalStripEmbedding_map_le_deleted (n N M : ℕ) (t : ℝ) (z : LatticeVertex)
    (R : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)))
    (hR : ∀ e ∈ R,
      tiltedHeight t (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).source ≤ tiltedHeight t z ∧
      tiltedHeight t (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).target ≤ tiltedHeight t z) :
    (((squareLattice.induce (tiltedWindow N M t : Set LatticeVertex)).induce
      (maximalStripCrop n N M t z)).map (maximalStripEmbedding n N M t z)) ≤
      edgeRestriction (rectangleDualAmbientGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
        (rectangleAmbientCrossedReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) R) := by
  classical
  intro x y hxy
  obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp hxy
  change ((rectangleDualAmbientGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).deleteEdges _).Adj _ _
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨(latticeTranslationIso z).map_rel_iff.mpr hab,?_⟩
  rintro ⟨e,he,hval⟩
  change e ∈ (rectangleCrossedEdges (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) R).map
    (subgraphEdgeEmbedding (rectangleDualGraph_le_ambient (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))) at he
  obtain ⟨g,hg,rfl⟩ := Finset.mem_map.mp he
  change g ∈ R.map (rectangleCrossingEdgeEquiv (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).toEmbedding at hg
  obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hg
  let D := rectanglePrimalDualEdgeEquiv (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) p
  have hs : rectangleDualEdgeSource (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) D ∈
      (rectangleCrossingEdgeEquiv (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) p).val :=
    Sym2.mem_iff'.mpr (Or.inl rfl)
  have ht : rectangleDualEdgeTarget (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) D ∈
      (rectangleCrossingEdgeEquiv (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) p).val :=
    Sym2.mem_iff'.mpr (Or.inr rfl)
  have hfaces : ∀ w ∈ (rectangleCrossingEdgeEquiv (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) p).val,
      tiltedHeight t z ≤ tiltedHeight t w.val := by
    intro w hw
    have hw' : w ∈ s(maximalStripEmbedding n N M t z a,maximalStripEmbedding n N M t z b) := by
      rw [← hval]
      exact hw
    rcases Sym2.mem_iff'.mp hw' with rfl | rfl
    · exact maximalStrip_height_ge_root N M t z a.val
    · exact maximalStrip_height_ge_root N M t z b.val
  have hmem : rectangleDualGraphEdgeEquiv (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) D ∈
      rectangleCrossedEdges (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) R :=
    Finset.mem_map.mpr ⟨p,hp,rfl⟩
  exact (upper_face_dual_edge_not_crossed _ _ _ R t (tiltedHeight t z) hR D
    (hfaces _ hs) (hfaces _ ht)) hmem

end
end PottsContinuity.Thm3.Prop4
