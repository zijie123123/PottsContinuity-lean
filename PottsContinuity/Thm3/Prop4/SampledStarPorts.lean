module

public import PottsContinuity.PlanarTopology.SampledStarPortRealization
public import PottsContinuity.Thm3.Prop4.SampledRectangleDualArms
public import PottsContinuity.Thm3.Prop4.VertexStarArms

/-!
# Actual sampled star ports at every rectangle vertex

Ports are faces of genuine retained incident bonds. At a corner the unused
exterior face is absent. Closing the sampled star connects all these ports.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

local instance sampledStarEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- The faces supplied by actual original incident rectangle bonds. -/
def sampledStarFacePorts (a : LatticeVertex) (w h : ℕ) (z : RectangleVertex a w h) :
    Set LatticeVertex :=
  {f | ∃ b : RectanglePrimalBond a w h,
    (b.val.source = z.val ∨ b.val.target = z.val) ∧
    (f = b.val.faceBase false ∨ f = b.val.faceBase true)}

/-- The actual star surgery closes every genuine sampled incident bond. -/
theorem rectangle_star_closing_closes_incident (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (z : RectangleVertex a w h)
    (b : RectanglePrimalBond a w h) (hb : b.val.source = z.val ∨ b.val.target = z.val) :
    rectanglePrimalBondToEdge a w h b ∉ A \ vertexStarEdges (rectangleGraph a w h) z := by
  classical
  intro he
  let e : (rectangleGraph a w h).edgeSet := rectanglePrimalBondToEdge a w h b
  have he' : e ∈ A \ vertexStarEdges (rectangleGraph a w h) z := he
  apply ((@Finset.mem_sdiff (rectangleGraph a w h).edgeSet
    (sampledStarEdgeDecidableEq a w h) A (vertexStarEdges (rectangleGraph a w h) z) e).mp he').2
  apply (mem_vertexStarEdges (rectangleGraph a w h) z e).mpr
  change z ∈ s(⟨b.val.source,b.property.1⟩,⟨b.val.target,b.property.2⟩)
  rw [Sym2.mem_iff]
  rcases hb with hb | hb
  · exact Or.inl (Subtype.ext hb.symm)
  · exact Or.inr (Subtype.ext hb.symm)

/-- Literal complementary-arc arms landing on genuine sampled star ports
separate the endpoints after star closing, including all boundary corners. -/
theorem sampled_star_closing_dual_arms_disconnect (a : LatticeVertex) (w h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) (A : Configuration (rectangleGraph a w h))
    (u v : RectangleVertex a w h) (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (z : RectangleVertex a w h) (P Q : LatticeVertex → Prop)
    (harms : A ∈ sampledRectangleDualArmsEvent a w h
      (sampledStarFacePorts a w h z) (sampledStarFacePorts a w h z)
      (PlanarTopology.rectangleLowerDualArc a w h u.val v.val)
      (PlanarTopology.rectangleUpperDualArc a w h u.val v.val) P Q) :
    ¬ ActualConnected (rectangleGraph a w h)
      (A \ vertexStarEdges (rectangleGraph a w h) z) u v := by
  have hclosed := rectangle_star_closing_closes_incident a w h A z
  have hsubset : A \ vertexStarEdges (rectangleGraph a w h) z ⊆ A := Finset.sdiff_subset
  have harm := isLowerSet_sampledRectangleDualArmsEvent a w h _ _ _ _ P Q
    hsubset harms
  obtain ⟨f,⟨b,hb,hf⟩,g,⟨c,hc,hg⟩,s,hs,t,ht,minus,plus,_,_⟩ := harm
  exact PlanarTopology.rectangle_disconnected_of_closed_boundary_star_and_dual_arms
    a w h hw hh _ u v hu hv z hclosed s f g t
    (PlanarTopology.rectangle_closed_star_bond_face_is_actual_port a w h _ z.val b hb
      (hclosed b hb) f hf)
    (PlanarTopology.rectangle_closed_star_bond_face_is_actual_port a w h _ z.val c hc
      (hclosed c hc) g hg) hs ht minus plus

end
end PottsContinuity.Thm3.Prop4
