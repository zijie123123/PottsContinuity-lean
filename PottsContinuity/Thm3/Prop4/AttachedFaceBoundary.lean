module

public import PottsContinuity.Thm3.Prop4.RawFaceBoundaryWiring

/-! # Mixed primal vertices attach to their own unreached face boundary -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section

/-- No face of an unreached component belongs to the raw explored exterior. -/
theorem rawUnreachedFaceCells_not_explored (a : LatticeVertex) (w h : ℕ)
    (u v : LatticeVertex) (A : Configuration (rectangleGraph a w h))
    (C : (squareLattice.induce (rawExploredExterior a w h u v A)ᶜ).ConnectedComponent)
    (f : LatticeVertex) (hf : f ∈ rawUnreachedFaceCells a w h u v A C) :
    f ∉ rawExploredExterior a w h u v A := by
  have hf' : f ∈ (rawUnreachedFaceCells a w h u v A C : Set LatticeVertex) := hf
  rw [coe_rawUnreachedFaceCells] at hf'
  obtain ⟨g,hg,rfl⟩ := hf'
  exact g.property

/-- A queried source bond cannot have both dual faces in one unreached component. -/
theorem sourceMarkedRaw_query_not_both_component_faces (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h))
    (C : (squareLattice.induce (rawExploredExterior a w h u.val v.val A)ᶜ).ConnectedComponent)
    (e : (rectangleGraph a w h).edgeSet) (he : e ∈ sourceMarkedRawReveal a w h u v A) :
    ¬((rectangleCrossingDualBond a w h e).source ∈ rawUnreachedFaceCells a w h u.val v.val A C ∧
      (rectangleCrossingDualBond a w h e).target ∈ rawUnreachedFaceCells a w h u.val v.val A C) := by
  classical
  simp only [sourceMarkedRawReveal,sampledRawDualReveal,rawFaceRegionReveal,
    Finset.mem_filter,Finset.mem_univ,true_and] at he
  intro hboth
  rcases he with hs | ht
  · exact rawUnreachedFaceCells_not_explored a w h u.val v.val A C _ hboth.1 (Or.inr hs)
  · exact rawUnreachedFaceCells_not_explored a w h u.val v.val A C _ hboth.2 (Or.inr ht)

/-- A queried/fresh primal attachment lies on the boundary of the SAME
unreached face component as its incident fresh edge. -/
theorem sourceMarkedRaw_mixed_vertex_on_component_boundary (a : LatticeVertex) (w h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) (u v x : RectangleVertex a w h)
    (A : Configuration (rectangleGraph a w h))
    (C : (squareLattice.induce (rawExploredExterior a w h u.val v.val A)ᶜ).ConnectedComponent)
    (e f : (rectangleGraph a w h).edgeSet)
    (heFaces : (rectangleCrossingDualBond a w h e).source ∈ rawUnreachedFaceCells a w h u.val v.val A C ∧
      (rectangleCrossingDualBond a w h e).target ∈ rawUnreachedFaceCells a w h u.val v.val A C)
    (hxe : x ∈ e.val) (hf : f ∈ sourceMarkedRawReveal a w h u v A) (hxf : x ∈ f.val) :
    ∃ g ∈ rawFaceRegionFrontier a w h (fun z => z ∈ rawUnreachedFaceCells a w h u.val v.val A C),
      x ∈ g.val := by
  classical
  let P := fun z => z ∈ rawUnreachedFaceCells a w h u.val v.val A C
  have heC : e ∈ rawFaceRegionReveal a w h P := by
    simpa only [rawFaceRegionReveal,Finset.mem_filter,Finset.mem_univ,true_and] using Or.inl heFaces.1
  by_cases hfront : P (rectangleCrossingDualBond a w h f).source ≠ P (rectangleCrossingDualBond a w h f).target
  · refine ⟨f,?_,hxf⟩
    simpa only [rawFaceRegionFrontier,Finset.mem_filter,Finset.mem_univ,true_and] using hfront
  · have hsame := not_not.mp hfront
    have hsame' : ((rectangleCrossingDualBond a w h f).source ∈ rawUnreachedFaceCells a w h u.val v.val A C) ↔
        ((rectangleCrossingDualBond a w h f).target ∈ rawUnreachedFaceCells a w h u.val v.val A C) := Iff.of_eq hsame
    have hfC : f ∉ rawFaceRegionReveal a w h P := by
      intro hfP
      have hboth := sourceMarkedRaw_query_not_both_component_faces a w h u v A C f hf
      simp only [rawFaceRegionReveal,Finset.mem_filter,Finset.mem_univ,true_and] at hfP
      rcases hfP with hs | ht
      · exact hboth ⟨hs,hsame'.mp hs⟩
      · exact hboth ⟨hsame'.mpr ht,ht⟩
    exact rawFaceRegion_mixed_vertex_on_frontier a w h hw hh P x e f heC hxe hfC hxf

end
end PottsContinuity.Thm3.Prop4
