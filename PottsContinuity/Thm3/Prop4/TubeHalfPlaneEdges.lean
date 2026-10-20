module

public import PottsContinuity.Thm3.Prop4.RectangleTubeRevealMembership
public import PottsContinuity.Thm3.Prop4.RectangleFrozenDuality

/-!
# Affine half-planes outside the actual tube reveal

The original Euclidean tube stays within vertical deviation 2r of its
supporting line. Crossing dual bonds sufficiently above or below that line
therefore survive deletion of the crossed revealed primal bonds.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.FK.Medial
noncomputable section

/-- The lower affine half-plane lies outside the literal Euclidean tube. -/
theorem radiusTube_not_mem_of_lower_half_plane (n : ℕ) (r : ℝ) (u v z : LatticeVertex)
    (t b : ℝ) (ht : |t| ≤ 1) (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (hz : (z.2 : ℝ)-t*z.1 ≤ b-2*r) : z ∉ radiusTube n r u v := by
  intro hmem
  have hd := tube_vertical_deviation_lt u v z t b r ht hu hv ((mem_radiusTube n r u v z).mp hmem).2
  have ha := neg_le_abs ((z.2 : ℝ)-(t*z.1+b))
  linarith only [hd,hz,ha]

/-- The upper affine half-plane lies outside the literal Euclidean tube. -/
theorem radiusTube_not_mem_of_upper_half_plane (n : ℕ) (r : ℝ) (u v z : LatticeVertex)
    (t b : ℝ) (ht : |t| ≤ 1) (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (hz : b+2*r ≤ (z.2 : ℝ)-t*z.1) : z ∉ radiusTube n r u v := by
  intro hmem
  have hd := tube_vertical_deviation_lt u v z t b r ht hu hv ((mem_radiusTube n r u v z).mp hmem).2
  have ha := le_abs_self ((z.2 : ℝ)-(t*z.1+b))
  linarith only [hd,hz,ha]

private theorem crossed_mem_iff (a : LatticeVertex) (w h : ℕ)
    (R : Configuration (rectangleGraph a w h)) (d : RectangleDualEdgeCarrier a w h) :
    rectangleDualGraphEdgeEquiv a w h d ∈ rectangleCrossedEdges a w h R ↔ d.primalEdge ∈ R := by
  change rectangleDualGraphEdgeEquiv a w h d ∈ R.map (rectangleCrossingEdgeEquiv a w h).toEmbedding ↔ _
  rw [Finset.mem_map_equiv]
  change (rectanglePrimalDualEdgeEquiv a w h).symm
    ((rectangleDualGraphEdgeEquiv a w h).symm (rectangleDualGraphEdgeEquiv a w h d)) ∈ R ↔ _
  rw [Equiv.symm_apply_apply]
  rfl

private theorem face_true_source (c : LatticeBond) : c.faceBase true = c.source := by
  cases c with
  | mk base axis => cases axis <;> rfl

private theorem dual_target_source (a : LatticeVertex) (w h : ℕ)
    (d : RectangleDualEdgeCarrier a w h) :
    (rectanglePrimalEdgeBond a w h d.primalEdge).source = d.crossingBond.target := by
  have ht : d.crossingBond.target = (rectanglePrimalEdgeBond a w h d.primalEdge).faceBase true :=
    rectangleDualEdgeTarget_faceBase a w h d
  rw [face_true_source] at ht
  exact ht.symm

private theorem not_crossed_of_source_outside (n : ℕ) (r : ℝ) (u v : LatticeVertex)
    (d : RectangleDualEdgeCarrier (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (hout : (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) d.primalEdge).source ∉
      radiusTube n r u v) :
    rectangleDualGraphEdgeEquiv (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) d ∉
      rectangleCrossedEdges (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (rectangleTubeRevealedEdges n r u v) := by
  intro hd
  have he := (crossed_mem_iff _ _ _ _ d).mp hd
  let c := rectanglePrimalEdgeBondEquiv (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) d.primalEdge
  have hc : rectanglePrimalBondToEdge (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) c = d.primalEdge :=
    (rectanglePrimalEdgeBondEquiv _ _ _).symm_apply_apply d.primalEdge
  have hcMem : rectanglePrimalBondToEdge (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) c ∈
      rectangleTubeRevealedEdges n r u v := by simpa only [hc] using he
  exact hout ((rectangle_bond_mem_tube_reveal_iff n r u v c).mp hcMem).1

/-- Every genuine dual edge with its target face in the lower safe half-plane
is retained in the exact deleted reference graph. -/
theorem lower_half_plane_dual_edge_not_crossed (n : ℕ) (r : ℝ) (u v : LatticeVertex)
    (t b : ℝ) (ht : |t| ≤ 1) (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (d : RectangleDualEdgeCarrier (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (hd : (d.crossingBond.target.2 : ℝ)-t*d.crossingBond.target.1 ≤ b-2*r) :
    rectangleDualGraphEdgeEquiv (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) d ∉
      rectangleCrossedEdges (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (rectangleTubeRevealedEdges n r u v) := by
  apply not_crossed_of_source_outside
  rw [dual_target_source]
  exact radiusTube_not_mem_of_lower_half_plane n r u v _ t b ht hu hv hd

/-- Every genuine dual edge with its target face in the upper safe half-plane
is retained in the exact deleted reference graph. -/
theorem upper_half_plane_dual_edge_not_crossed (n : ℕ) (r : ℝ) (u v : LatticeVertex)
    (t b : ℝ) (ht : |t| ≤ 1) (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (d : RectangleDualEdgeCarrier (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (hd : b+2*r ≤ (d.crossingBond.target.2 : ℝ)-t*d.crossingBond.target.1) :
    rectangleDualGraphEdgeEquiv (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) d ∉
      rectangleCrossedEdges (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (rectangleTubeRevealedEdges n r u v) := by
  apply not_crossed_of_source_outside
  rw [dual_target_source]
  exact radiusTube_not_mem_of_upper_half_plane n r u v _ t b ht hu hv hd

end
end PottsContinuity.Thm3.Prop4
