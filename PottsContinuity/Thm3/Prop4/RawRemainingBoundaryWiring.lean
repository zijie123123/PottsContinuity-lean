module

public import PottsContinuity.Thm3.Prop4.RawRemainingFaceComponents
public import PottsContinuity.Thm3.Prop4.AttachedFaceBoundary

/-! # Actual boundary wiring on each remaining raw primal-edge component -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section

/-- Every two queried-adjacent active vertices in one remaining primal
component are joined by actual RAW recorded-open original bonds. -/
theorem sourceMarkedRaw_remaining_boundary_recorded_connected (a : LatticeVertex) (w h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) (u v : RectangleVertex a w h)
    (A : Configuration (rectangleGraph a w h)) (x y : RectangleVertex a w h)
    (hconn : (sourceMarkedRawDomain a w h u v A).Reachable x y)
    (e f r s : (rectangleGraph a w h).edgeSet)
    (he : e ∉ sourceMarkedRawReveal a w h u v A) (hf : f ∉ sourceMarkedRawReveal a w h u v A)
    (hxe : x ∈ e.val) (hyf : y ∈ f.val)
    (hr : r ∈ sourceMarkedRawReveal a w h u v A) (hs : s ∈ sourceMarkedRawReveal a w h u v A)
    (hxr : x ∈ r.val) (hys : y ∈ s.val) :
    ActualConnected (rectangleGraph a w h)
      (Exploration.revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A).val x y := by
  let H := squareLattice.induce (rawExploredExterior a w h u.val v.val A)ᶜ
  let root := sourceMarkedRawFreshFace a w h u v A e he false
  let C := H.connectedComponentMk root
  have member (p : {f : LatticeVertex // f ∉ rawExploredExterior a w h u.val v.val A}) (hp : H.Reachable root p) :
      p.val ∈ rawUnreachedFaceCells a w h u.val v.val A C := by
    change p.val ∈ (rawUnreachedFaceCells a w h u.val v.val A C : Set LatticeVertex)
    rw [coe_rawUnreachedFaceCells]
    refine ⟨p,?_,rfl⟩
    change H.connectedComponentMk p = C
    exact (SimpleGraph.ConnectedComponent.sound hp).symm
  have faces (g : (rectangleGraph a w h).edgeSet) (hg : g ∉ sourceMarkedRawReveal a w h u v A)
      (hgReach : H.Reachable root (sourceMarkedRawFreshFace a w h u v A g hg false)) :
      (rectangleCrossingDualBond a w h g).source ∈ rawUnreachedFaceCells a w h u.val v.val A C ∧
      (rectangleCrossingDualBond a w h g).target ∈ rawUnreachedFaceCells a w h u.val v.val A C := by
    have h₀ := member _ hgReach
    have h₁ := member _ (hgReach.trans (sourceMarkedRaw_fresh_face_pair_connected a w h u v A g hg))
    have hsource : (rectangleCrossingDualBond a w h g).source = (rectanglePrimalEdgeBond a w h g).faceBase false :=
      rectangleDualEdgeSource_faceBase a w h (rectanglePrimalDualEdgeEquiv a w h g)
    have htarget : (rectangleCrossingDualBond a w h g).target = (rectanglePrimalEdgeBond a w h g).faceBase true :=
      rectangleDualEdgeTarget_faceBase a w h (rectanglePrimalDualEdgeEquiv a w h g)
    constructor
    · rw [hsource]
      exact h₀
    · rw [htarget]
      exact h₁
  have hE := faces e he (SimpleGraph.Reachable.refl root)
  have hF := faces f hf (sourceMarkedRaw_remaining_path_faces_connected a w h hw hh u v A x y hconn e f he hf hxe hyf)
  obtain ⟨g,hg,hxg⟩ := sourceMarkedRaw_mixed_vertex_on_component_boundary a w h hw hh u v x A C e r hE hxe hr hxr
  obtain ⟨k,hk,hyk⟩ := sourceMarkedRaw_mixed_vertex_on_component_boundary a w h hw hh u v y A C f s hF hyf hs hys
  have normalize (j : (rectangleGraph a w h).edgeSet)
      (hj : j ∈ rawFaceRegionFrontier a w h (fun z => z ∈ rawUnreachedFaceCells a w h u.val v.val A C)) :
      ((rectanglePrimalEdgeBond a w h j).faceBase false ∈ rawUnreachedFaceCells a w h u.val v.val A C) ≠
      ((rectanglePrimalEdgeBond a w h j).faceBase true ∈ rawUnreachedFaceCells a w h u.val v.val A C) := by
    have hlabels : ((rectangleCrossingDualBond a w h j).source ∈ rawUnreachedFaceCells a w h u.val v.val A C) ≠
        ((rectangleCrossingDualBond a w h j).target ∈ rawUnreachedFaceCells a w h u.val v.val A C) := by
      simpa only [rawFaceRegionFrontier,Finset.mem_filter,Finset.mem_univ,true_and] using hj
    have hsource : (rectangleCrossingDualBond a w h j).source = (rectanglePrimalEdgeBond a w h j).faceBase false :=
      rectangleDualEdgeSource_faceBase a w h (rectanglePrimalDualEdgeEquiv a w h j)
    have htarget : (rectangleCrossingDualBond a w h j).target = (rectanglePrimalEdgeBond a w h j).faceBase true :=
      rectangleDualEdgeTarget_faceBase a w h (rectanglePrimalDualEdgeEquiv a w h j)
    rwa [hsource,htarget] at hlabels
  exact rawUnreachedFace_boundary_vertices_recorded_connected a w h u v A C
    (rectanglePrimalEdgeBond a w h g) (rectanglePrimalEdgeBond a w h k) (normalize g hg) (normalize k hk) x y
    (Sym2.mem_iff.mpr (rectangle_edge_vertex_normalized_endpoint a w h g x hxg))
    (Sym2.mem_iff.mpr (rectangle_edge_vertex_normalized_endpoint a w h k y hyk))

/-- The induced raw boundary has ONE class on the queried-adjacent active
vertices of each remaining original-edge component, for every original partition. -/
theorem sourceMarkedRaw_remaining_component_boundary_wired (a : LatticeVertex) (w h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) (u v : RectangleVertex a w h)
    (A : Configuration (rectangleGraph a w h)) (ξ : BoundaryCondition (RectangleVertex a w h))
    (x y : RectangleVertex a w h)
    (hconn : (sourceMarkedRawDomain a w h u v A).Reachable x y)
    (hxActive : ∃ e : (rectangleGraph a w h).edgeSet, e ∉ sourceMarkedRawReveal a w h u v A ∧ x ∈ e.val)
    (hyActive : ∃ e : (rectangleGraph a w h).edgeSet, e ∉ sourceMarkedRawReveal a w h u v A ∧ y ∈ e.val)
    (hxBoundary : ∃ e ∈ sourceMarkedRawReveal a w h u v A, x ∈ e.val)
    (hyBoundary : ∃ e ∈ sourceMarkedRawReveal a w h u v A, y ∈ e.val) :
    (frozenBoundary ξ (Exploration.revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A).val).partition.r x y := by
  obtain ⟨e,he,hxe⟩ := hxActive
  obtain ⟨f,hf,hyf⟩ := hyActive
  obtain ⟨r,hr,hxr⟩ := hxBoundary
  obtain ⟨s,hs,hys⟩ := hyBoundary
  exact actualConnected_component _ ξ _
    (sourceMarkedRaw_remaining_boundary_recorded_connected a w h hw hh u v A x y hconn e f r s
      he hf hxe hyf hr hs hxr hys)

end
end PottsContinuity.Thm3.Prop4
