module

public import PottsContinuity.Thm3.Prop4.ActualStarPortGraph
public import PottsContinuity.Thm3.Prop4.RawFaceBoundaryRetained

/-! # Fresh incident original edges belong to one unreached face component -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section

/-- Two actual incident star edges whose faces avoid a set have their face
ports connected while avoiding that set. No unused corner port is supplied. -/
theorem actualStar_unreached_faces_connected (a : LatticeVertex) (w h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) (z : RectangleVertex a w h) (P : Set LatticeVertex)
    (b c : RectanglePrimalBond a w h)
    (hb : b.val.source = z.val ∨ b.val.target = z.val)
    (hc : c.val.source = z.val ∨ c.val.target = z.val)
    (hb₀ : b.val.faceBase false ∉ P) (hb₁ : b.val.faceBase true ∉ P)
    (hc₀ : c.val.faceBase false ∉ P) (hc₁ : c.val.faceBase true ∉ P) :
    (squareLattice.induce Pᶜ).Reachable ⟨b.val.faceBase false,hb₀⟩ ⟨c.val.faceBase false,hc₀⟩ := by
  classical
  let T := sampledStarFacePorts a w h z
  let freshStarPortFT : Fintype T := (sampledStarFacePorts_finite a w h z).fintype
  let H := PlanarTopology.rectangleSampledClosedDualGraph a w h (actualStarClosedState a w h z)
  let J := H.induce T
  let U : Set T := {x | x.val ∉ P}
  let s : U := ⟨⟨b.val.faceBase false,⟨b,hb,Or.inl rfl⟩⟩,hb₀⟩
  let t : U := ⟨⟨b.val.faceBase true,⟨b,hb,Or.inr rfl⟩⟩,hb₁⟩
  let r : U := ⟨⟨c.val.faceBase false,⟨c,hc,Or.inl rfl⟩⟩,hc₀⟩
  let k : U := ⟨⟨c.val.faceBase true,⟨c,hc,Or.inr rfl⟩⟩,hc₁⟩
  have hB : (J.induce U).Adj s t := by
    change H.Adj (b.val.faceBase false) (b.val.faceBase true)
    have h := PlanarTopology.rectangleSampledClosedDualGraph_adj_of_closed_bond a w h
      (actualStarClosedState a w h z) b (actualStarClosedState_incident_closed a w h z b hb)
    simpa only [dualBondOfPrimal_source,dualBondOfPrimal_target] using h
  have hC : (J.induce U).Adj r k := by
    change H.Adj (c.val.faceBase false) (c.val.faceBase true)
    have h := PlanarTopology.rectangleSampledClosedDualGraph_adj_of_closed_bond a w h
      (actualStarClosedState a w h z) c (actualStarClosedState_incident_closed a w h z c hc)
    simpa only [dualBondOfPrimal_source,dualBondOfPrimal_target] using h
  have hreach := induced_four_port_edges_connected J (actualStarPortGraph_preconnected a w h hw hh z)
    (sampledStarFacePorts_card_le_four a w h z) U s t r k hB hC
  let f : J.induce U →g squareLattice.induce Pᶜ := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    map_rel' := fun hxy => (sampledClosedDualToFaceLattice a w h (actualStarClosedState a w h z)).map_rel' hxy }
  exact hreach.map f

/-- Both actual dual faces of every unqueried source bond lie outside the
explored geometric exterior. This preserves all original closed states. -/
theorem sourceMarkedRaw_fresh_face_unreached (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h))
    (e : (rectangleGraph a w h).edgeSet) (he : e ∉ sourceMarkedRawReveal a w h u v A)
    (side : Bool) :
    (rectanglePrimalEdgeBond a w h e).faceBase side ∉ rawExploredExterior a w h u.val v.val A := by
  let S := PlanarTopology.rectangleLowerDualArc a w h u.val v.val ∪
    PlanarTopology.rectangleUpperDualArc a w h u.val v.val
  have hnot := (not_mem_rawFaceRegionReveal_iff a w h (sampledDualSeedRegion a w h A S) e).mp he
  have hs : (rectangleCrossingDualBond a w h e).source = (rectanglePrimalEdgeBond a w h e).faceBase false :=
    rectangleDualEdgeSource_faceBase a w h (rectanglePrimalDualEdgeEquiv a w h e)
  have ht : (rectangleCrossingDualBond a w h e).target = (rectanglePrimalEdgeBond a w h e).faceBase true :=
    rectangleDualEdgeTarget_faceBase a w h (rectanglePrimalDualEdgeEquiv a w h e)
  intro hf
  have hreach := (sampled_bond_face_explored_iff_reached a w h u.val v.val A
    (rectanglePrimalEdgeBond a w h e) (rectanglePrimalEdgeBond_endpoints_mem_public a w h e) side).mp hf
  cases side
  · exact hnot.1 (hs.symm ▸ hreach)
  · exact hnot.2 (ht.symm ▸ hreach)

/-- Two fresh original bonds incident to the same primal vertex determine
the SAME actual unreached face component. This includes sides and corners. -/
theorem sourceMarkedRaw_fresh_incident_faces_connected (a : LatticeVertex) (w h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) (u v z : RectangleVertex a w h)
    (A : Configuration (rectangleGraph a w h))
    (e f : (rectangleGraph a w h).edgeSet)
    (he : e ∉ sourceMarkedRawReveal a w h u v A) (hf : f ∉ sourceMarkedRawReveal a w h u v A)
    (hze : z ∈ e.val) (hzf : z ∈ f.val) :
    (squareLattice.induce (rawExploredExterior a w h u.val v.val A)ᶜ).Reachable
      ⟨(rectanglePrimalEdgeBond a w h e).faceBase false,sourceMarkedRaw_fresh_face_unreached a w h u v A e he false⟩
      ⟨(rectanglePrimalEdgeBond a w h f).faceBase false,sourceMarkedRaw_fresh_face_unreached a w h u v A f hf false⟩ := by
  let b : RectanglePrimalBond a w h :=
    ⟨rectanglePrimalEdgeBond a w h e,rectanglePrimalEdgeBond_endpoints_mem_public a w h e⟩
  let c : RectanglePrimalBond a w h :=
    ⟨rectanglePrimalEdgeBond a w h f,rectanglePrimalEdgeBond_endpoints_mem_public a w h f⟩
  have hb := (rectangle_edge_vertex_normalized_endpoint a w h e z hze).imp Eq.symm Eq.symm
  have hc := (rectangle_edge_vertex_normalized_endpoint a w h f z hzf).imp Eq.symm Eq.symm
  exact actualStar_unreached_faces_connected a w h hw hh z _ b c hb hc
    (sourceMarkedRaw_fresh_face_unreached a w h u v A e he false)
    (sourceMarkedRaw_fresh_face_unreached a w h u v A e he true)
    (sourceMarkedRaw_fresh_face_unreached a w h u v A f hf false)
    (sourceMarkedRaw_fresh_face_unreached a w h u v A f hf true)

end
end PottsContinuity.Thm3.Prop4
