module

public import PottsContinuity.Thm3.Prop4.TubeRectangleReference

/-!
# Endpoint characterization on the actual rectangle reveal carrier

Coordinate transport retains exactly the tube's internal original bonds,
including boundary bonds and every radius value.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

/-- A rectangle edge is revealed exactly when both original lattice endpoints
belong to the literal source tube. -/
theorem mem_rectangleTubeRevealedEdges (n : ℕ) (r : ℝ) (u v : LatticeVertex)
    (e : (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet) :
    e ∈ rectangleTubeRevealedEdges n r u v ↔ ∀ z ∈ e.val, z.val ∈ radiusTube n r u v := by
  constructor
  · intro he
    change e ∈ (radiusTubeRevealedEdges n r u v).map
      (configurationIsoEdgeEquiv (boxTubeRectangleIso n)).toEmbedding at he
    obtain ⟨d,hd,rfl⟩ := Finset.mem_map.mp he
    intro z hz
    change z ∈ Sym2.map (boxTubeRectangleIso n) d.val at hz
    obtain ⟨x,hx,rfl⟩ := Sym2.mem_map.mp hz
    exact (mem_radiusTubeRevealedEdges n r u v d).mp hd x hx
  · intro hends
    let d := (configurationIsoEdgeEquiv (boxTubeRectangleIso n)).symm e
    have hde : configurationIsoEdgeEquiv (boxTubeRectangleIso n) d = e :=
      Equiv.apply_symm_apply _ e
    change e ∈ (radiusTubeRevealedEdges n r u v).map
      (configurationIsoEdgeEquiv (boxTubeRectangleIso n)).toEmbedding
    refine Finset.mem_map.mpr ⟨d,?_,hde⟩
    apply (mem_radiusTubeRevealedEdges n r u v d).mpr
    intro x hx
    apply hends (boxTubeRectangleIso n x)
    have hm : boxTubeRectangleIso n x ∈
        (configurationIsoEdgeEquiv (boxTubeRectangleIso n) d).val := by
      change boxTubeRectangleIso n x ∈ Sym2.map (boxTubeRectangleIso n) d.val
      exact Sym2.mem_map.mpr ⟨x,hx,rfl⟩
    simpa only [hde] using hm

/-- A normalized genuine rectangle bond is revealed precisely when its
source and target both lie in the original tube. -/
theorem rectangle_bond_mem_tube_reveal_iff (n : ℕ) (r : ℝ) (u v : LatticeVertex)
    (c : RectanglePrimalBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) :
    rectanglePrimalBondToEdge (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) c ∈
      rectangleTubeRevealedEdges n r u v ↔
      c.val.source ∈ radiusTube n r u v ∧ c.val.target ∈ radiusTube n r u v := by
  let e : (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet :=
    rectanglePrimalBondToEdge (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) c
  change e ∈ rectangleTubeRevealedEdges n r u v ↔ _
  rw [mem_rectangleTubeRevealedEdges]
  change (∀ z : RectangleVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n),
    z ∈ s(⟨c.val.source,c.property.1⟩,⟨c.val.target,c.property.2⟩) →
    z.val ∈ radiusTube n r u v) ↔ _
  rw [Sym2.forall_mem_pair]

end
end PottsContinuity.Thm3.Prop4
