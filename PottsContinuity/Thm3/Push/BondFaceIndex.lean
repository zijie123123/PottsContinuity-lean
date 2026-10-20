module

public import PottsContinuity.Thm3.Push.RayIndexCutGradient
public import PottsContinuity.PD.Duality.LatticePorts
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Medial
open PottsContinuity.PD.Duality

/-- Convert a face-base label to the primal mark used by the established ray
index convention. The shift is exactly (1,1) for both bond orientations. -/
def faceIndexMark (v : LatticeVertex) : LatticeVertex := (v.1+1,v.2+1)

/-- Across an untraversed original bond the closed walk's face indices agree. -/
theorem rayIndex_bond_faces_eq_of_not_mem {z : LatticeVertex}
    (p : squareLattice.Walk z z) (b : LatticeBond) (hb : b.toSym2 ∉ p.edges) :
    rayIndex (faceIndexMark (b.faceBase false)) p =
      rayIndex (faceIndexMark (b.faceBase true)) p := by
  rcases b with ⟨⟨x,y⟩,axis⟩
  cases axis with
  | horizontal =>
    have hidx := rayIndex_vertical_difference (x+1) y p (by simpa [LatticeBond.toSym2,
      LatticeBond.source,LatticeBond.target] using hb)
    simp only [faceIndexMark,LatticeBond.faceBase,sub_add_cancel]
    omega
  | vertical =>
    have hidx := rayIndex_horizontal_invariant x (y+1) p (by simpa [LatticeBond.toSym2,
      LatticeBond.source,LatticeBond.target] using hb)
    simpa [faceIndexMark,LatticeBond.faceBase] using hidx

/-- Across a once-traversed original bond the two face indices differ. -/
theorem rayIndex_bond_faces_ne_of_mem {z : LatticeVertex}
    (p : squareLattice.Walk z z) (hn : p.edges.Nodup) (b : LatticeBond)
    (hb : b.toSym2 ∈ p.edges) :
    rayIndex (faceIndexMark (b.faceBase false)) p ≠
      rayIndex (faceIndexMark (b.faceBase true)) p := by
  rcases b with ⟨⟨x,y⟩,axis⟩
  cases axis with
  | horizontal =>
    have hidx := rayIndex_vertical_jump_ne_zero (x+1) y p hn (by simpa [LatticeBond.toSym2,
      LatticeBond.source,LatticeBond.target] using hb)
    simpa [faceIndexMark,LatticeBond.faceBase,ne_comm] using hidx
  | vertical =>
    have hidx := rayIndex_horizontal_jump_ne_zero x (y+1) p hn (by simpa [LatticeBond.toSym2,
      LatticeBond.source,LatticeBond.target] using hb)
    simpa [faceIndexMark,LatticeBond.faceBase] using hidx

end PottsContinuity.Push
