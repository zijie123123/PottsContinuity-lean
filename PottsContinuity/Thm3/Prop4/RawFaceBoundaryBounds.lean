module

public import PottsContinuity.Thm3.Prop4.RawFaceComponentCycles

/-! # Original rectangle bounds for every raw unreached-component boundary -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section

/-- Every actual unreached cell base is strictly inside the face rectangle. -/
theorem rawUnreachedFaceCells_bounds (a : LatticeVertex) (w h : ℕ) (u v : LatticeVertex)
    (A : Configuration (rectangleGraph a w h))
    (C : (squareLattice.induce (rawExploredExterior a w h u v A)ᶜ).ConnectedComponent)
    (f : LatticeVertex) (hf : f ∈ rawUnreachedFaceCells a w h u v A C) :
    a.1 ≤ f.1 ∧ f.1 < a.1+(w : ℤ) ∧ a.2 ≤ f.2 ∧ f.2 < a.2+(h : ℤ) := by
  have hf' : f ∈ (rawUnreachedFaceCells a w h u v A C : Set LatticeVertex) := hf
  rw [coe_rawUnreachedFaceCells] at hf'
  obtain ⟨g,hg,rfl⟩ := hf'
  have hn : g.val ∉ rectangleExteriorFaces a w h := fun h => g.property (Or.inl h)
  dsimp [rectangleExteriorFaces] at hn
  omega

/-- Every bond on an actual unreached face-component boundary has BOTH
original primal endpoints in the sampled rectangle. No exterior cap is used. -/
theorem rawUnreachedFace_boundary_bond_endpoints (a : LatticeVertex) (w h : ℕ)
    (u v : LatticeVertex) (A : Configuration (rectangleGraph a w h))
    (C : (squareLattice.induce (rawExploredExterior a w h u v A)ᶜ).ConnectedComponent)
    (b : LatticeBond)
    (hb : (b.faceBase false ∈ rawUnreachedFaceCells a w h u v A C) ≠
      (b.faceBase true ∈ rawUnreachedFaceCells a w h u v A C)) :
    b.source ∈ PD.FK.latticeRectangle a w h ∧ b.target ∈ PD.FK.latticeRectangle a w h := by
  classical
  have hsome : b.faceBase false ∈ rawUnreachedFaceCells a w h u v A C ∨
      b.faceBase true ∈ rawUnreachedFaceCells a w h u v A C := by
    by_cases hf : b.faceBase false ∈ rawUnreachedFaceCells a w h u v A C
    · exact Or.inl hf
    · right
      by_contra ht
      exact hb (propext (iff_of_false hf ht))
  rcases b with ⟨⟨x,y⟩,axis⟩
  cases axis <;> rcases hsome with hf | hf <;>
    have hbounds := rawUnreachedFaceCells_bounds a w h u v A C _ hf <;>
    constructor <;> rw [PD.FK.mem_latticeRectangle] <;>
    dsimp [LatticeBond.source,LatticeBond.target,LatticeBond.faceBase] at hbounds ⊢ <;> omega

/-- A sampled original bond can supply only the actual top/bottom/side
exterior seeds; an unused exterior corner is not a bond face. -/
theorem rectangle_bond_exterior_face_is_marked_seed (a : LatticeVertex) (w h : ℕ)
    (u v : LatticeVertex) (b : LatticeBond)
    (hb : b.source ∈ PD.FK.latticeRectangle a w h ∧ b.target ∈ PD.FK.latticeRectangle a w h)
    (side : Bool) (hext : b.faceBase side ∈ rectangleExteriorFaces a w h) :
    b.faceBase side ∈ PlanarTopology.rectangleLowerDualArc a w h u v ∪
      PlanarTopology.rectangleUpperDualArc a w h u v := by
  have hs := (PD.FK.mem_latticeRectangle a b.source w h).mp hb.1
  have ht := (PD.FK.mem_latticeRectangle a b.target w h).mp hb.2
  rcases b with ⟨⟨x,y⟩,axis⟩
  cases axis <;> cases side <;>
    dsimp [LatticeBond.source,LatticeBond.target,LatticeBond.faceBase,rectangleExteriorFaces,
      PlanarTopology.rectangleLowerDualArc,PlanarTopology.rectangleUpperDualArc] at hs ht hext ⊢ <;>
    rcases a with ⟨a₁,a₂⟩ <;> dsimp at * <;> simp only [Set.mem_union,Set.mem_ofPred_eq] <;> omega

end
end PottsContinuity.Thm3.Prop4
