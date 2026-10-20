module

public import PottsContinuity.Thm3.Push.BondFaceIndex
public import PottsContinuity.PD.Duality.CircuitEnclosure
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Index constancy in the two face regions of a cell boundary -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial PD.Duality Push
noncomputable section

/-- Every adjacent pair of face labels is crossed by a genuine lattice bond. -/
theorem adjacent_faces_crossed_by_lattice_bond {x y : LatticeVertex}
    (hxy : squareLattice.Adj x y) :
    ∃ b : LatticeBond, (b.faceBase false = x ∧ b.faceBase true = y) ∨
      (b.faceBase false = y ∧ b.faceBase true = x) := by
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  rcases (squareLattice_adj_iff _ _).mp hxy with ⟨h|h,hy⟩ | ⟨hx,h|h⟩
  · refine ⟨⟨(y₁,x₂),.vertical⟩,Or.inl ?_⟩
    constructor <;> apply Prod.ext <;> dsimp [LatticeBond.faceBase] <;> omega
  · refine ⟨⟨(x₁,x₂),.vertical⟩,Or.inr ?_⟩
    constructor <;> apply Prod.ext <;> dsimp [LatticeBond.faceBase] <;> omega
  · refine ⟨⟨(x₁,y₂),.horizontal⟩,Or.inl ?_⟩
    constructor <;> apply Prod.ext <;> dsimp [LatticeBond.faceBase] <;> omega
  · refine ⟨⟨(x₁,x₂),.horizontal⟩,Or.inr ?_⟩
    constructor <;> apply Prod.ext <;> dsimp [LatticeBond.faceBase] <;> omega

/-- Equal-label adjacent faces see the same index of any boundary-supported
closed walk. The face-label shift is the established literal (1,1) shift. -/
theorem cell_boundary_same_label_index_eq (S : Finset LatticeVertex)
    {z : LatticeVertex} (p : squareLattice.Walk z z)
    (hp : ∀ b : LatticeBond, b.toSym2 ∈ p.edges →
      (b.faceBase false ∈ S) ≠ (b.faceBase true ∈ S))
    {x y : LatticeVertex} (hxy : squareLattice.Adj x y) (hlabel : (x ∈ S) = (y ∈ S)) :
    rayIndex (faceIndexMark x) p = rayIndex (faceIndexMark y) p := by
  obtain ⟨b,hfaces | hfaces⟩ := adjacent_faces_crossed_by_lattice_bond hxy
  · obtain ⟨hb₀,hb₁⟩ := hfaces
    have hnot : b.toSym2 ∉ p.edges := by
      intro he
      apply hp b he
      rwa [hb₀,hb₁]
    simpa only [hb₀,hb₁] using rayIndex_bond_faces_eq_of_not_mem p b hnot
  · obtain ⟨hb₀,hb₁⟩ := hfaces
    have hnot : b.toSym2 ∉ p.edges := by
      intro he
      apply hp b he
      rw [hb₀,hb₁]
      exact hlabel.symm
    have hidx := rayIndex_bond_faces_eq_of_not_mem p b hnot
    rw [hb₀,hb₁] at hidx
    exact hidx.symm

/-- The index has one value on every connected fixed-label face region. -/
theorem cell_boundary_constant_region_index_eq (S : Finset LatticeVertex)
    {z : LatticeVertex} (p : squareLattice.Walk z z)
    (hp : ∀ b : LatticeBond, b.toSym2 ∈ p.edges →
      (b.faceBase false ∈ S) ≠ (b.faceBase true ∈ S))
    (R : Set LatticeVertex) (hlabel : ∀ x y : R, (x.val ∈ S) = (y.val ∈ S))
    {x y : R} (hxy : (squareLattice.induce R).Reachable x y) :
    rayIndex (faceIndexMark x.val) p = rayIndex (faceIndexMark y.val) p := by
  obtain ⟨q⟩ := hxy
  induction q with
  | nil => rfl
  | cons hadj q ih =>
    exact (cell_boundary_same_label_index_eq S p hp hadj (hlabel _ _)).trans ih

end
end PottsContinuity.Thm3.Prop4
