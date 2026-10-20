module

public import PottsContinuity.PlanarMixed.TiltedHalfHeight.ContractedCircuitGeometry

@[expose] public section

namespace PottsContinuity.PlanarMixed.TiltedHalfHeight
open PD.FK PD.FK.Medial PD.Duality
noncomputable section

/-- Every internal geometric edge of a cell hull avoids its own dual boundary. -/
def cellHullAvoidanceHom (C : Finset LatticeVertex) {z : LatticeVertex}
    (p : (latticeCellBoundaryGraph (vertexCellBases C)).Walk z z) :
    (squareLattice.induce (C : Set LatticeVertex)) →g
      circuitAvoidanceGraph (p.mapLe (latticeCellBoundaryGraph_le _)) where
  toFun := Subtype.val
  map_rel' := by
    intro u v huv
    refine ⟨huv,?_⟩
    intro b hb
    have he : (b.source=u.val ∧ b.target=v.val) ∨ (b.source=v.val ∧ b.target=u.val) :=
      Sym2.eq_iff.mp hb
    have hs : b.source ∈ C := by
      rcases he with h | h
      · exact h.1 ▸ u.property
      · exact h.1 ▸ v.property
    have ht : b.target ∈ C := by
      rcases he with h | h
      · exact h.2 ▸ v.property
      · exact h.2 ▸ u.property
    exact Lemma4Connectors.cellBoundary_walk_avoids_internal_bond C p b hs ht

/-- A finite connected primal hull containing the central lower segment has
an actual dual-boundary crosscut from above its top to below its bottom. -/
theorem finite_connected_hull_boundary_central_crosscut
    (C : Finset LatticeVertex) (n : ℕ) (hzero : (0,0) ∈ C) (hn : (0,(n:ℤ)) ∈ C)
    (hconn : ∀ x (hx : x ∈ C), (squareLattice.induce (C : Set LatticeVertex)).Reachable
      ⟨(0,0),hzero⟩ ⟨x,hx⟩) :
    ∃ yu yl : ℤ, (n:ℤ) ≤ yu ∧ yl < 0 ∧
      Nonempty ((latticeCellBoundaryGraph (vertexCellBases C)).Walk (0,yu) (0,yl)) := by
  classical
  obtain ⟨x,hx,z,p,_,hidx⟩ := cellBoundary_outer_cycle_nonzero (vertexCellBases C)
    (Finset.Nonempty.image ⟨(0,0),hzero⟩ _)
  let q := p.mapLe (latticeCellBoundaryGraph_le (vertexCellBases C))
  have hxC : (x.1+1,x.2+1) ∈ C := (mem_vertexCellBases C x).mp hx
  have hroot := (hconn _ hxC).map (cellHullAvoidanceHom C p)
  change (circuitAvoidanceGraph q).Reachable (0,0) (x.1+1,x.2+1) at hroot
  have hidx0 : rayIndex (0,0) q ≠ 0 := by
    rw [rayIndex_eq_of_avoidance_reachable q hroot]
    exact hidx
  have hnroot := (hconn _ hn).map (cellHullAvoidanceHom C p)
  change (circuitAvoidanceGraph q).Reachable (0,0) (0,(n:ℤ)) at hnroot
  have hidxn : rayIndex (0,(n:ℤ)) q ≠ 0 := by
    rw [←rayIndex_eq_of_avoidance_reachable q hnroot]
    exact hidx0
  obtain ⟨yu,hyu,heu⟩ := closedWalk_meets_central_upper_ray q (n:ℤ) hidxn
  obtain ⟨yl,hyl,hel⟩ := closedWalk_meets_central_lower_ray q 0 hidx0
  have hu : (0,yu) ∈ p.support := by
    simpa only [q,SimpleGraph.Walk.support_mapLe_eq_support] using q.snd_mem_support_of_mem_edges heu
  have hl : (0,yl) ∈ p.support := by
    simpa only [q,SimpleGraph.Walk.support_mapLe_eq_support] using q.snd_mem_support_of_mem_edges hel
  exact ⟨yu,yl,hyu,hyl,⟨(p.takeUntil (0,yu) hu).reverse.append (p.takeUntil (0,yl) hl)⟩⟩

end
end PottsContinuity.PlanarMixed.TiltedHalfHeight
