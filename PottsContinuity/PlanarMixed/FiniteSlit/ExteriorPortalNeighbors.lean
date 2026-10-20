module

public import PottsContinuity.PlanarMixed.FiniteSlit.ExteriorBoundaryEdges

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK
noncomputable section

/-- Every left portal has an actual original reference bond into the left
exterior, using one horizontal or vertical lattice step. -/
theorem left_portal_has_exterior_neighbor (M : ℕ) (x y : ℤ) (w h : ℕ)
    (hM : 2 ≤ M) (hx : 1 ≤ x) (_hxw : x ≤ (w:ℤ))
    (hleft : x-(M:ℤ) < 0) (hright : (w:ℤ) < x+(M:ℤ)-1) (hh : h < M)
    (u : RectangleVertex (0,0) w h) (hu : u ∈ sourceLeftPortal w h x) :
    ∃ b : Vertex M x,
      (graph M x y).Adj
        (rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega) u) b ∧
      exteriorProjection M x w h b = Sum.inr false := by
  have hub := (PD.FK.mem_latticeRectangle _ _ _ _).mp u.property
  dsimp at hub
  change u.val.1 = 0 ∨ (u.val.2 = (h:ℤ) ∧ u.val.1 < x) at hu
  rcases hu with hu | hu
  · let b : Vertex M x := ⟨(-1,u.val.2),by
      rw [mem_rectangle_iff M x (by omega)]
      dsimp
      omega⟩
    refine ⟨b,?_,?_⟩
    · rw [graph_adj_iff_retained]
      change (slitRetainedBondGraph x y).Adj u.val (-1,u.val.2)
      rw [slitRetainedBondGraph_adj_iff,PD.FK.squareLattice_adj_iff]
      dsimp
      omega
    · apply (exteriorProjection_eq_left_iff M x w h b).mpr
      refine ⟨(outside_source_iff M x w h (by omega) b).mpr ?_,?_⟩ <;>
        dsimp [b] <;> omega
  · let b : Vertex M x := ⟨(u.val.1,(h:ℤ)+1),by
      rw [mem_rectangle_iff M x (by omega)]
      dsimp
      omega⟩
    refine ⟨b,?_,?_⟩
    · rw [graph_adj_iff_retained]
      change (slitRetainedBondGraph x y).Adj u.val (u.val.1,(h:ℤ)+1)
      rw [slitRetainedBondGraph_adj_iff,PD.FK.squareLattice_adj_iff]
      dsimp
      omega
    · apply (exteriorProjection_eq_left_iff M x w h b).mpr
      refine ⟨(outside_source_iff M x w h (by omega) b).mpr ?_,?_⟩ <;>
        dsimp [b] <;> omega

/-- Every right portal likewise has an actual original exterior bond. -/
theorem right_portal_has_exterior_neighbor (M : ℕ) (x y : ℤ) (w h : ℕ)
    (hM : 2 ≤ M) (_hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
    (hleft : x-(M:ℤ) < 0) (hright : (w:ℤ) < x+(M:ℤ)-1) (hh : h < M)
    (u : RectangleVertex (0,0) w h) (hu : u ∈ sourceRightPortal w h x) :
    ∃ b : Vertex M x,
      (graph M x y).Adj
        (rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega) u) b ∧
      exteriorProjection M x w h b = Sum.inr true := by
  have hub := (PD.FK.mem_latticeRectangle _ _ _ _).mp u.property
  dsimp at hub
  change u.val.1 = (w:ℤ) ∨ (u.val.2 = (h:ℤ) ∧ x ≤ u.val.1) at hu
  rcases hu with hu | hu
  · let b : Vertex M x := ⟨((w:ℤ)+1,u.val.2),by
      rw [mem_rectangle_iff M x (by omega)]
      dsimp
      omega⟩
    refine ⟨b,?_,?_⟩
    · rw [graph_adj_iff_retained]
      change (slitRetainedBondGraph x y).Adj u.val ((w:ℤ)+1,u.val.2)
      rw [slitRetainedBondGraph_adj_iff,PD.FK.squareLattice_adj_iff]
      dsimp
      omega
    · apply (exteriorProjection_eq_right_iff M x w h b).mpr
      refine ⟨(outside_source_iff M x w h (by omega) b).mpr ?_,?_⟩ <;>
        dsimp [b] <;> omega
  · let b : Vertex M x := ⟨(u.val.1,(h:ℤ)+1),by
      rw [mem_rectangle_iff M x (by omega)]
      dsimp
      omega⟩
    refine ⟨b,?_,?_⟩
    · rw [graph_adj_iff_retained]
      change (slitRetainedBondGraph x y).Adj u.val (u.val.1,(h:ℤ)+1)
      rw [slitRetainedBondGraph_adj_iff,PD.FK.squareLattice_adj_iff]
      dsimp
      omega
    · apply (exteriorProjection_eq_right_iff M x w h b).mpr
      refine ⟨(outside_source_iff M x w h (by omega) b).mpr ?_,?_⟩ <;>
        dsimp [b] <;> omega

end
end PottsContinuity.PlanarMixed.FiniteSlit
