module

public import PottsContinuity.Thm3.Prop4.TubeStripCropEmbedding
public import PottsContinuity.Thm3.Prop4.DeletedAmbientDualLaw

/-!
# The safe physical crop embeds into the actual deleted reference graph

Both endpoints of every cropped edge lie on the safe side. If such an edge
were deleted, its genuine crossed original bond would be revealed, contradicting
the proved tube half-plane bound at its actual target face.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

/-- The literal safely framed crop is a subgraph of the deleted ambient
reference, for either orientation and every actual tube radius. -/
theorem tubeStripPhysicalEmbedding_map_le_deleted (n N M : ℕ) (r : ℝ)
    (u v : LatticeVertex) (t b : ℝ) (ht : |t| ≤ 1)
    (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (c : ℤ) (reflected : Bool)
    (hc : if reflected then (c : ℝ) ≤ b-2*r else b+2*r ≤ (c : ℝ)) :
    (((squareLattice.induce (tiltedWindow N M (if reflected then -t else t) : Set LatticeVertex)).induce
      (tubeStripPhysicalCrop n N M (if reflected then -t else t) c reflected)).map
        (tubeStripPhysicalEmbedding n N M (if reflected then -t else t) c reflected)) ≤
      edgeRestriction (rectangleDualAmbientGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
        (rectangleAmbientCrossedReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
          (rectangleTubeRevealedEdges n r u v)) := by
  classical
  intro x y hxy
  obtain ⟨a,d,had,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp hxy
  change ((rectangleDualAmbientGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).deleteEdges _).Adj _ _
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨(tubeStripFrame c reflected).map_rel_iff.mpr had,?_⟩
  rintro ⟨e,he,hval⟩
  change e ∈ (rectangleCrossedEdges (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
      (rectangleTubeRevealedEdges n r u v)).map
        (subgraphEdgeEmbedding (rectangleDualGraph_le_ambient (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))) at he
  obtain ⟨g,hg,rfl⟩ := Finset.mem_map.mp he
  change g ∈ (rectangleTubeRevealedEdges n r u v).map
    (rectangleCrossingEdgeEquiv (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).toEmbedding at hg
  obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hg
  let D := rectanglePrimalDualEdgeEquiv (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) p
  have htarget : rectangleDualEdgeTarget (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) D ∈
      (rectangleCrossingEdgeEquiv (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) p).val := by
    change _ ∈ s(rectangleDualEdgeSource _ _ _ D,rectangleDualEdgeTarget _ _ _ D)
    exact Sym2.mem_iff'.mpr (Or.inr rfl)
  have hpair : rectangleDualEdgeTarget (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) D ∈
      s(tubeStripPhysicalEmbedding n N M (if reflected then -t else t) c reflected a,
        tubeStripPhysicalEmbedding n N M (if reflected then -t else t) c reflected d) := by
    rw [← hval]
    exact htarget
  have hface : D.crossingBond.target = tubeStripFrame c reflected a.val.val ∨
      D.crossingBond.target = tubeStripFrame c reflected d.val.val := by
    rcases Sym2.mem_iff'.mp hpair with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  have ha := framed_tiltedWindow_safe_height N M t b r c reflected hc a.val
  have hd := framed_tiltedWindow_safe_height N M t b r c reflected hc d.val
  have hsafe : if reflected then tiltedHeight t D.crossingBond.target ≤ b-2*r
      else b+2*r ≤ tiltedHeight t D.crossingBond.target := by
    rcases hface with h | h
    · simpa only [h] using ha
    · simpa only [h] using hd
  have hmem := (rectangle_crossed_edge_mem_iff (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
    (rectangleTubeRevealedEdges n r u v) p).mpr hp
  cases reflected
  · exact (upper_half_plane_dual_edge_not_crossed n r u v t b ht hu hv D hsafe) hmem
  · exact (lower_half_plane_dual_edge_not_crossed n r u v t b ht hu hv D hsafe) hmem

end
end PottsContinuity.Thm3.Prop4
