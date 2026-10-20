module

public import PottsContinuity.Thm3.Prop4.FreshStarFaceConnectivity

/-! # Each remaining primal component has one actual unreached face component -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section

/-- A dual face of an actual fresh original bond, on the exact unreached carrier. -/
def sourceMarkedRawFreshFace (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h))
    (e : (rectangleGraph a w h).edgeSet) (he : e ∉ sourceMarkedRawReveal a w h u v A)
    (side : Bool) : {f : LatticeVertex // f ∉ rawExploredExterior a w h u.val v.val A} :=
  ⟨(rectanglePrimalEdgeBond a w h e).faceBase side,sourceMarkedRaw_fresh_face_unreached a w h u v A e he side⟩

/-- Both faces of a fresh original bond belong to the same actual unreached component. -/
theorem sourceMarkedRaw_fresh_face_pair_connected (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h))
    (e : (rectangleGraph a w h).edgeSet) (he : e ∉ sourceMarkedRawReveal a w h u v A) :
    (squareLattice.induce (rawExploredExterior a w h u.val v.val A)ᶜ).Reachable
      (sourceMarkedRawFreshFace a w h u v A e he false) (sourceMarkedRawFreshFace a w h u v A e he true) := by
  have hadj := (dualBondOfPrimal (rectanglePrimalEdgeBond a w h e)).adjacent
  have hstep : (squareLattice.induce (rawExploredExterior a w h u.val v.val A)ᶜ).Adj
      (sourceMarkedRawFreshFace a w h u v A e he false) (sourceMarkedRawFreshFace a w h u v A e he true) := by
    change squareLattice.Adj ((rectanglePrimalEdgeBond a w h e).faceBase false)
      ((rectanglePrimalEdgeBond a w h e).faceBase true)
    convert (show PD.FK.squareLattice.Adj ((rectanglePrimalEdgeBond a w h e).faceBase false)
      ((rectanglePrimalEdgeBond a w h e).faceBase true) from by
        simpa only [dualBondOfPrimal_source,dualBondOfPrimal_target] using hadj) using 1
    rfl
  exact hstep.reachable

/-- Any two fresh bonds attached to the same remaining primal component
have their face labels in the SAME actual unreached face component. -/
theorem sourceMarkedRaw_remaining_path_faces_connected (a : LatticeVertex) (w h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) (u v : RectangleVertex a w h)
    (A : Configuration (rectangleGraph a w h)) (x y : RectangleVertex a w h)
    (hconn : (sourceMarkedRawDomain a w h u v A).Reachable x y)
    (e f : (rectangleGraph a w h).edgeSet)
    (he : e ∉ sourceMarkedRawReveal a w h u v A) (hf : f ∉ sourceMarkedRawReveal a w h u v A)
    (hxe : x ∈ e.val) (hyf : y ∈ f.val) :
    (squareLattice.induce (rawExploredExterior a w h u.val v.val A)ᶜ).Reachable
      (sourceMarkedRawFreshFace a w h u v A e he false) (sourceMarkedRawFreshFace a w h u v A f hf false) := by
  obtain ⟨p⟩ := hconn
  revert e
  induction p with
  | nil =>
    intro e he hxe
    exact sourceMarkedRaw_fresh_incident_faces_connected a w h hw hh u v _ A e f he hf hxe hyf
  | @cons x z y hxz p ih =>
    intro e he hxe
    change (edgeRestriction (rectangleGraph a w h) (sourceMarkedRawReveal a w h u v A)).Adj x z at hxz
    obtain ⟨hG,hnot⟩ := SimpleGraph.deleteEdges_adj.mp hxz
    let g : (rectangleGraph a w h).edgeSet := ⟨s(x,z),(rectangleGraph a w h).mem_edgeSet.mpr hG⟩
    have hg : g ∉ sourceMarkedRawReveal a w h u v A := by
      intro hg
      exact hnot ⟨g,hg,rfl⟩
    have hxg : x ∈ g.val := Sym2.mem_iff.mpr (Or.inl rfl)
    have hzg : z ∈ g.val := Sym2.mem_iff.mpr (Or.inr rfl)
    have hfirst := sourceMarkedRaw_fresh_incident_faces_connected a w h hw hh u v x A e g he hg hxe hxg
    exact hfirst.trans (ih hyf g hg hzg)

end
end PottsContinuity.Thm3.Prop4
