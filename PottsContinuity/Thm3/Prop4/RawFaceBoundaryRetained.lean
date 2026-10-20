module

public import PottsContinuity.Thm3.Prop4.RawFaceBoundaryBounds
public import PottsContinuity.Thm3.Prop4.RawMarkedStoppedLaw

/-! # Raw unreached-component boundary bonds are recorded open original bonds -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section

/-- On the actual faces of a sampled bond, the geometric explored exterior
is precisely the actual closed-dual reached region. -/
theorem sampled_bond_face_explored_iff_reached (a : LatticeVertex) (w h : ℕ)
    (u v : LatticeVertex) (A : Configuration (rectangleGraph a w h)) (b : LatticeBond)
    (hb : b.source ∈ PD.FK.latticeRectangle a w h ∧ b.target ∈ PD.FK.latticeRectangle a w h)
    (side : Bool) :
    b.faceBase side ∈ rawExploredExterior a w h u v A ↔
      sampledDualSeedRegion a w h A
        (PlanarTopology.rectangleLowerDualArc a w h u v ∪
          PlanarTopology.rectangleUpperDualArc a w h u v) (b.faceBase side) := by
  constructor
  · rintro (hext | hreached)
    · exact ⟨_,rectangle_bond_exterior_face_is_marked_seed a w h u v b hb side hext,
        SimpleGraph.Reachable.refl _⟩
    · exact hreached
  · exact Or.inr

/-- Every original bond separating an actual unreached face component from
its exterior is queried and OPEN in the uncompleted source record. -/
theorem rawUnreachedFace_boundary_edge_open_and_revealed (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h))
    (C : (squareLattice.induce (rawExploredExterior a w h u.val v.val A)ᶜ).ConnectedComponent)
    (e : (rectangleGraph a w h).edgeSet)
    (he : ((rectangleCrossingDualBond a w h e).source ∈ rawUnreachedFaceCells a w h u.val v.val A C) ≠
      ((rectangleCrossingDualBond a w h e).target ∈ rawUnreachedFaceCells a w h u.val v.val A C)) :
    e ∈ A ∧ e ∈ sourceMarkedRawReveal a w h u v A := by
  classical
  let R := rawExploredExterior a w h u.val v.val A
  let S := PlanarTopology.rectangleLowerDualArc a w h u.val v.val ∪
    PlanarTopology.rectangleUpperDualArc a w h u.val v.val
  let P := sampledDualSeedRegion a w h A S
  let F := rawUnreachedFaceCells a w h u.val v.val A C
  let b := rectanglePrimalEdgeBond a w h e
  let s := (rectangleCrossingDualBond a w h e).source
  let t := (rectangleCrossingDualBond a w h e).target
  have hsBase : s = b.faceBase false :=
    rectangleDualEdgeSource_faceBase a w h (rectanglePrimalDualEdgeEquiv a w h e)
  have htBase : t = b.faceBase true :=
    rectangleDualEdgeTarget_faceBase a w h (rectanglePrimalDualEdgeEquiv a w h e)
  have hbounds := rectanglePrimalEdgeBond_endpoints_mem_public a w h e
  have atSource : s ∈ R ↔ P s := by
    rw [hsBase]
    exact sampled_bond_face_explored_iff_reached a w h u.val v.val A b hbounds false
  have atTarget : t ∈ R ↔ P t := by
    rw [htBase]
    exact sampled_bond_face_explored_iff_reached a w h u.val v.val A b hbounds true
  have hF (f : LatticeVertex) : f ∈ F ↔ f ∈ complementComponentLabels squareLattice R C := by
    change f ∈ (rawUnreachedFaceCells a w h u.val v.val A C : Set LatticeVertex) ↔ _
    rw [coe_rawUnreachedFaceCells]
  have outside (f : LatticeVertex) (hf : f ∈ F) : f ∉ R := by
    obtain ⟨g,hg,rfl⟩ := (hF f).mp hf
    exact g.property
  have hadj : squareLattice.Adj s t := (rectangleCrossingDualBond a w h e).adjacent
  have hlabels : (P s ∧ ¬P t) ∨ (P t ∧ ¬P s) := by
    by_cases hs : s ∈ F
    · have ht : t ∉ F := by
        intro ht
        exact he (propext (iff_of_true hs ht))
      have htR : t ∈ R := complementComponentLabels_attachment squareLattice R C
        (fun htC => ht ((hF t).mpr htC)) ((hF s).mp hs) hadj.symm
      exact Or.inr ⟨atTarget.mp htR,fun hsP => outside s hs (atSource.mpr hsP)⟩
    · have ht : t ∈ F := by
        by_contra ht
        exact he (propext (iff_of_false hs ht))
      have hsR : s ∈ R := complementComponentLabels_attachment squareLattice R C
        (fun hsC => hs ((hF s).mpr hsC)) ((hF t).mp ht) hadj
      exact Or.inl ⟨atSource.mp hsR,fun htP => outside t ht (atTarget.mpr htP)⟩
  have hqueried : e ∈ sourceMarkedRawReveal a w h u v A := by
    simp only [sourceMarkedRawReveal,sampledRawDualReveal,rawFaceRegionReveal,
      Finset.mem_filter,Finset.mem_univ,true_and]
    exact hlabels.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  refine ⟨?_,hqueried⟩
  by_contra heClosed
  have hsame := sampledDualSeedRegion_closed_iff a w h A S e heClosed
  rcases hlabels with ⟨hs,ht⟩ | ⟨ht,hs⟩
  · exact ht (hsame.mp hs)
  · exact hs (hsame.mpr ht)

end
end PottsContinuity.Thm3.Prop4
