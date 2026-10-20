module

public import PottsContinuity.Thm3.Prop4.SampledRawDualRegion
public import PottsContinuity.Thm3.Prop4.RectangleExteriorConnectivity
public import PottsContinuity.Thm3.Prop4.ComplementComponentConnectivity

/-! # The connected geometric exterior of the raw two-sided exploration -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial PlanarTopology
noncomputable section

/-- The reached face region together with the geometric exterior of the host.
This is a face set for topology and adds no original sampled query. -/
def rawExploredExterior (a : LatticeVertex) (w h : ℕ) (u v : LatticeVertex)
    (A : Configuration (rectangleGraph a w h)) : Set LatticeVertex :=
  rectangleExteriorFaces a w h ∪ {f | sampledDualSeedRegion a w h A
    (rectangleLowerDualArc a w h u v ∪ rectangleUpperDualArc a w h u v) f}

/-- Every actual exterior arc seed lies in the geometric exterior face set. -/
theorem marked_dual_arc_seed_mem_exterior (a : LatticeVertex) (w h : ℕ)
    (u v s : LatticeVertex)
    (hs : s ∈ rectangleLowerDualArc a w h u v ∪ rectangleUpperDualArc a w h u v) :
    s ∈ rectangleExteriorFaces a w h := by
  rcases hs with hs | hs
  · rcases hs with hs | hs | hs
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl (by omega))
  · rcases hs with hs | hs | hs
    · exact Or.inr (Or.inr (Or.inr (by omega)))
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl (by omega))

/-- Forgetting sampled closed-edge states keeps literal nearest-neighbor
adjacency of their dual face labels. -/
def sampledClosedDualToFaceLattice (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    rectangleSampledClosedDualGraph a w h A →g squareLattice where
  toFun := id
  map_rel' := by
    rintro x y ⟨d,_,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact d.crossingBond.adjacent
    · exact d.crossingBond.adjacent.symm

/-- Each explored face joins the fixed exterior corner through the explored
face set. Extra geometric exterior steps do not change the source record. -/
theorem rawExploredExterior_reachable_corner (a : LatticeVertex) (w h : ℕ)
    (u v : LatticeVertex) (A : Configuration (rectangleGraph a w h))
    (f : rawExploredExterior a w h u v A) :
    (squareLattice.induce (rawExploredExterior a w h u v A)).Reachable f
      ⟨(a.1-1,a.2-1),Or.inl (Or.inl (by omega))⟩ := by
  let R := rawExploredExterior a w h u v A
  let inclusion : squareLattice.induce (rectangleExteriorFaces a w h) →g squareLattice.induce R := {
    toFun := fun x => ⟨x.val,Or.inl x.property⟩
    map_rel' := fun h => h }
  have exteriorReach (x : LatticeVertex) (hx : x ∈ rectangleExteriorFaces a w h) :
      (squareLattice.induce R).Reachable ⟨x,Or.inl hx⟩
        ⟨(a.1-1,a.2-1),Or.inl (Or.inl (by omega))⟩ :=
    (rectangleExteriorFaces_reachable_corner a w h ⟨x,hx⟩).map inclusion
  rcases f.property with hf | ⟨s,hs,⟨q⟩⟩
  · exact exteriorReach f.val hf
  · let r := q.map (sampledClosedDualToFaceLattice a w h A)
    have hr : ∀ x ∈ r.support, x ∈ R := by
      intro x hx
      rw [SimpleGraph.Walk.support_map] at hx
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
      exact Or.inr ⟨s,hs,(q.takeUntil y hy).reachable⟩
    have hsExt := marked_dual_arc_seed_mem_exterior a w h u v s hs
    exact ((r.induce R hr).reachable).symm.trans (exteriorReach s hsExt)

/-- The full raw explored exterior is connected, including before marked
connection success and without any planar component assumption. -/
theorem rawExploredExterior_preconnected (a : LatticeVertex) (w h : ℕ)
    (u v : LatticeVertex) (A : Configuration (rectangleGraph a w h)) :
    (squareLattice.induce (rawExploredExterior a w h u v A)).Preconnected := by
  intro x y
  exact (rawExploredExterior_reachable_corner a w h u v A x).trans
    (rawExploredExterior_reachable_corner a w h u v A y).symm

/-- Every unexplored face is confined to a fixed finite face rectangle. -/
theorem rawExploredExterior_complement_finite (a : LatticeVertex) (w h : ℕ)
    (u v : LatticeVertex) (A : Configuration (rectangleGraph a w h)) :
    (rawExploredExterior a w h u v A)ᶜ.Finite := by
  apply (Finset.finite_toSet (PD.FK.latticeRectangle a w h)).subset
  intro x hx
  have hnone : x ∉ rectangleExteriorFaces a w h := fun h => hx (Or.inl h)
  change x ∈ PD.FK.latticeRectangle a w h
  rw [PD.FK.mem_latticeRectangle]
  dsimp [rectangleExteriorFaces] at hnone
  constructor <;> constructor <;> omega

end
end PottsContinuity.Thm3.Prop4
