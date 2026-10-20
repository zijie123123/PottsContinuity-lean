module

public import PottsContinuity.PlanarTopology.RectangleCoreClamp
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial
noncomputable section

/-- The normalized bond of a true original rectangle edge has both original
endpoints in the rectangle. -/
theorem rectangle_primal_bond_endpoints_mem (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier a w h) :
    (rectanglePrimalEdgeBond a w h e).source ∈ latticeRectangle a w h ∧
      (rectanglePrimalEdgeBond a w h e).target ∈ latticeRectangle a w h := by
  have hb := pd_rectanglePrimalEdgeBond_toSym2 a w h e
  constructor
  · have hm : (rectanglePrimalEdgeBond a w h e).source ∈ Sym2.map Subtype.val e.val := by
      rw [← hb]
      exact Sym2.mem_mk_left _ _
    obtain ⟨z,_,hz⟩ := Sym2.mem_map.mp hm
    exact hz ▸ z.property
  · have hm : (rectanglePrimalEdgeBond a w h e).target ∈ Sym2.map Subtype.val e.val := by
      rw [← hb]
      exact Sym2.mem_mk_right _ _
    obtain ⟨z,_,hz⟩ := Sym2.mem_map.mp hm
    exact hz ▸ z.property

/-- Contracting an exterior dual-port edge never changes an edge into a new
bond: it either disappears or retains both original endpoints. -/
theorem rectangleDualCoreClamp_step (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (u v : RectangleDualVertex a w h) (huv : (rectangleDualGraph a w h).Adj u v) :
    rectangleCoreClamp a w h hw hh u.val = rectangleCoreClamp a w h hw hh v.val ∨
      (rectangleCoreClamp a w h hw hh u.val = u.val ∧
        rectangleCoreClamp a w h hw hh v.val = v.val) := by
  obtain ⟨e,he⟩ := (rectangleDualGraph_adj_iff a w h u v).mp huv
  have hp := rectangle_primal_bond_endpoints_mem a w h e.primalEdge
  have hc := rectangleCoreClamp_face_pair a w h hw hh
    (rectanglePrimalEdgeBond a w h e.primalEdge) hp.1 hp.2
  have he' := congrArg (Sym2.map (fun z : RectangleDualVertex a w h => z.val)) he
  change s(u.val,v.val) = s((rectangleDualEdgeSource a w h e).val,
    (rectangleDualEdgeTarget a w h e).val) at he'
  rw [rectangleDualEdgeSource_faceBase,rectangleDualEdgeTarget_faceBase] at he'
  rcases Sym2.eq_iff.mp he' with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · rw [hu,hv]
    exact hc
  · rw [hu,hv]
    rcases hc with hc | ⟨h0,h1⟩
    · exact Or.inl hc.symm
    · exact Or.inr ⟨h1,h0⟩

/-- The clamped integer face base is a genuine interior face, including
rectangles with just one row or column of faces. -/
theorem rectangleCoreClamp_mem_interior (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (z : LatticeVertex) : rectangleCoreClamp a w h hw hh z ∈ rectangleDualInterior a w h := by
  have hb := rectangleCoreClamp_bounds a w h hw hh z
  apply Finset.mem_filter.mpr
  refine ⟨?_,hb⟩
  rw [rectangleDualExpanded,mem_latticeRectangle]
  push_cast
  exact ⟨⟨by omega,by omega⟩,by omega,by omega⟩

end
end PottsContinuity.PlanarTopology
