module

public import PottsContinuity.Thm3.Push.FilledFaceBoundaryRows
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Medial
noncomputable section

/-- Literal horizontal cell-boundary adjacency. Proof adapted from the private
boundaryAdj_right in PD/Duality/LatticeCellBoundaryParity.lean. -/
theorem cellBoundary_adj_right_iff (S : Finset LatticeVertex) (x y : ℤ) :
    (latticeCellBoundaryGraph S).Adj (x,y) (x+1,y) ↔
      ((x,y) ∈ S) ≠ ((x,y-1) ∈ S) := by
  rw [latticeCellBoundaryGraph_adj_iff]
  constructor
  · rintro ⟨_,e,he,hfaces⟩
    rcases e with ⟨⟨a,b⟩,axis⟩
    cases axis with
    | horizontal =>
      simp [LatticeBond.toSym2,LatticeBond.source,LatticeBond.target] at he
      have hab : a=x ∧ b=y := by omega
      rcases hab with ⟨rfl,rfl⟩
      simpa [LatticeBond.faceBase] using hfaces
    | vertical =>
      simp [LatticeBond.toSym2,LatticeBond.source,LatticeBond.target] at he
      omega
  · intro hcut
    refine ⟨?_,⟨⟨(x,y),.horizontal⟩,?_,?_⟩⟩
    · simp [squareLattice_adj_iff]
    · simp [LatticeBond.toSym2,LatticeBond.source,LatticeBond.target]
    · simpa [LatticeBond.faceBase] using hcut

/-- A primal vertex with no cell-boundary neighbor sees one constant label
on all four incident faces. -/
theorem cellBoundary_no_adj_four_face_labels (S : Finset LatticeVertex) (x y : ℤ)
    (hno : ∀ v, ¬ (latticeCellBoundaryGraph S).Adj (x,y) v) :
    (((x,y) ∈ S) = ((x-1,y) ∈ S)) ∧
      (((x,y) ∈ S) = ((x,y-1) ∈ S)) ∧
      (((x,y) ∈ S) = ((x-1,y-1) ∈ S)) := by
  classical
  have hup : ((x,y) ∈ S)=((x-1,y) ∈ S) := by
    by_contra hne
    exact hno (x,y+1) ((cellBoundary_adj_up_iff S x y).mpr hne)
  have hright : ((x,y) ∈ S)=((x,y-1) ∈ S) := by
    by_contra hne
    exact hno (x+1,y) ((cellBoundary_adj_right_iff S x y).mpr hne)
  have hleft : ((x-1,y) ∈ S)=((x-1,y-1) ∈ S) := by
    by_contra hne
    have ha := (cellBoundary_adj_right_iff S (x-1) y).mpr hne
    have ha' : (latticeCellBoundaryGraph S).Adj (x,y) (x-1,y) := by
      simpa only [sub_add_cancel] using ha.symm
    exact hno (x-1,y) ha'
  exact ⟨hup,hright,hup.trans hleft⟩

/-- Either face of any bond incident to a vertex is one of its four literal
incident cells; orientation and endpoint choices are handled explicitly. -/
theorem incident_bond_face_cases (b : LatticeBond) (v : LatticeVertex)
    (hv : v ∈ b.toSym2) (side : Bool) :
    b.faceBase side = v ∨ b.faceBase side = (v.1-1,v.2) ∨
      b.faceBase side = (v.1,v.2-1) ∨ b.faceBase side = (v.1-1,v.2-1) := by
  rcases b with ⟨⟨x,y⟩,axis⟩
  rcases v with ⟨a,c⟩
  cases axis <;> cases side <;>
    simp only [LatticeBond.toSym2,LatticeBond.source,LatticeBond.target,
      LatticeBond.faceBase,Sym2.mem_iff,Prod.mk.injEq] at * <;> omega

/-- Under absence of a boundary edge, every incident-bond face has the
canonical northeast label. -/
theorem cellBoundary_no_adj_incident_face_label (S : Finset LatticeVertex)
    (v : LatticeVertex) (hno : ∀ t, ¬ (latticeCellBoundaryGraph S).Adj v t)
    (b : LatticeBond) (hb : v ∈ b.toSym2) (side : Bool) :
    (b.faceBase side ∈ S) ↔ v ∈ S := by
  obtain ⟨hNW,hSE,hSW⟩ := cellBoundary_no_adj_four_face_labels S v.1 v.2 hno
  rcases incident_bond_face_cases b v hb side with he | he | he | he
  · rw [he]
  · rw [he]
    exact Iff.of_eq hNW.symm
  · rw [he]
    exact Iff.of_eq hSE.symm
  · rw [he]
    exact Iff.of_eq hSW.symm

/-- An active vertex incident to both a revealed bond (one upper face) and
an unrevealed bond (two lower faces) is a real frontier vertex. This is the
local geometric input for the active-carrier FK comparison. -/
theorem cellBoundary_mixed_incidence_has_adj (S : Finset LatticeVertex)
    (v : LatticeVertex) (b c : LatticeBond) (hb : v ∈ b.toSym2) (hc : v ∈ c.toSym2)
    (hupper : b.faceBase false ∈ S ∨ b.faceBase true ∈ S)
    (hlower : c.faceBase false ∉ S ∧ c.faceBase true ∉ S) :
    ∃ t, (latticeCellBoundaryGraph S).Adj v t := by
  classical
  by_contra hno
  have hno' : ∀ t, ¬ (latticeCellBoundaryGraph S).Adj v t := by simpa only [not_exists] using hno
  have hvS : v ∈ S := by
    rcases hupper with hf | ht
    · exact (cellBoundary_no_adj_incident_face_label S v hno' b hb false).mp hf
    · exact (cellBoundary_no_adj_incident_face_label S v hno' b hb true).mp ht
  exact hlower.1 ((cellBoundary_no_adj_incident_face_label S v hno' c hc false).mpr hvS)

end
end PottsContinuity.Push
