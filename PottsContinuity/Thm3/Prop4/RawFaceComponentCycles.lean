module

public import PottsContinuity.Thm3.Prop4.RawExploredExterior
public import PottsContinuity.Thm3.Prop4.CellBoundaryOneCycle

/-! # Single actual boundary cycles of the raw unexplored face components -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section

/-- A component outside the raw explored exterior has finitely many face labels. -/
theorem rawUnreachedComponent_finite (a : LatticeVertex) (w h : ℕ) (u v : LatticeVertex)
    (A : Configuration (rectangleGraph a w h))
    (C : (squareLattice.induce (rawExploredExterior a w h u v A)ᶜ).ConnectedComponent) :
    (complementComponentLabels squareLattice (rawExploredExterior a w h u v A) C).Finite := by
  apply (rawExploredExterior_complement_finite a w h u v A).subset
  rintro x ⟨y,hy,rfl⟩
  exact y.property

/-- The exact finite original face labels of one unexplored component. -/
def rawUnreachedFaceCells (a : LatticeVertex) (w h : ℕ) (u v : LatticeVertex)
    (A : Configuration (rectangleGraph a w h))
    (C : (squareLattice.induce (rawExploredExterior a w h u v A)ᶜ).ConnectedComponent) :
    Finset LatticeVertex := (rawUnreachedComponent_finite a w h u v A C).toFinset

@[simp] theorem coe_rawUnreachedFaceCells (a : LatticeVertex) (w h : ℕ) (u v : LatticeVertex)
    (A : Configuration (rectangleGraph a w h))
    (C : (squareLattice.induce (rawExploredExterior a w h u v A)ᶜ).ConnectedComponent) :
    (rawUnreachedFaceCells a w h u v A C : Set LatticeVertex) =
      complementComponentLabels squareLattice (rawExploredExterior a w h u v A) C := by
  simp only [rawUnreachedFaceCells,Set.Finite.coe_toFinset]

/-- Each actual unexplored face component is connected on its original labels. -/
theorem rawUnreachedFaceCells_preconnected (a : LatticeVertex) (w h : ℕ) (u v : LatticeVertex)
    (A : Configuration (rectangleGraph a w h))
    (C : (squareLattice.induce (rawExploredExterior a w h u v A)ᶜ).ConnectedComponent) :
    (squareLattice.induce (rawUnreachedFaceCells a w h u v A C : Set LatticeVertex)).Preconnected := by
  rw [coe_rawUnreachedFaceCells]
  exact complementComponentLabels_preconnected _ _ C

/-- The exterior of each actual unexplored face component is connected.
This uses explored-region connectivity, not a Jordan or source-law premise. -/
theorem rawUnreachedFaceCells_exterior_preconnected (a : LatticeVertex) (w h : ℕ)
    (u v : LatticeVertex) (A : Configuration (rectangleGraph a w h))
    (C : (squareLattice.induce (rawExploredExterior a w h u v A)ᶜ).ConnectedComponent) :
    (squareLattice.induce (rawUnreachedFaceCells a w h u v A C : Set LatticeVertex)ᶜ).Preconnected := by
  rw [coe_rawUnreachedFaceCells]
  apply complementComponentLabels_exterior_preconnected _ face_label_lattice_preconnected _
    (rawExploredExterior_preconnected a w h u v A) _ C
  exact ⟨(a.1-1,a.2-1),Or.inl (Or.inl (by omega))⟩

/-- All genuine boundary-bond vertices of one actual unexplored component
are connected through its SAME actual boundary bonds. -/
theorem rawUnreachedFace_boundary_vertices_connected (a : LatticeVertex) (w h : ℕ)
    (u v : LatticeVertex) (A : Configuration (rectangleGraph a w h))
    (C : (squareLattice.induce (rawExploredExterior a w h u v A)ᶜ).ConnectedComponent)
    (b c : LatticeBond)
    (hb : (b.faceBase false ∈ rawUnreachedFaceCells a w h u v A C) ≠
      (b.faceBase true ∈ rawUnreachedFaceCells a w h u v A C))
    (hc : (c.faceBase false ∈ rawUnreachedFaceCells a w h u v A C) ≠
      (c.faceBase true ∈ rawUnreachedFaceCells a w h u v A C))
    (x y : LatticeVertex) (hx : x ∈ b.toSym2) (hy : y ∈ c.toSym2) :
    (latticeCellBoundaryGraph (rawUnreachedFaceCells a w h u v A C)).Reachable x y :=
  cell_boundary_bond_vertices_connected _ (rawUnreachedFaceCells_preconnected a w h u v A C)
    (rawUnreachedFaceCells_exterior_preconnected a w h u v A C) b c hb hc x y hx hy

end
end PottsContinuity.Thm3.Prop4
