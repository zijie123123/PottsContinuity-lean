module

public import PottsContinuity.Thm3.Push.BondFaceIndex
public import PottsContinuity.PlanarTopology.SampledStarPortRealization
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PD.FK.Medial PD.Duality PlanarTopology

/-- At a vertex off the closed walk, the mark of every incident bond face
has the same ray index as the vertex itself. The unit mark shifts are exact. -/
theorem rayIndex_incident_face_eq_of_off_support
    {z : LatticeVertex} (p : squareLattice.Walk z z)
    (v : LatticeVertex) (hv : v ∉ p.support) (b : LatticeBond)
    (hb : b.source = v ∨ b.target = v) (f : LatticeVertex)
    (hf : f = b.faceBase false ∨ f = b.faceBase true) :
    rayIndex (faceIndexMark f) p = rayIndex v p := by
  have hnot (c : LatticeBond) (hc : c.source = v ∨ c.target = v) : c.toSym2 ∉ p.edges := by
    intro he
    apply hv
    apply SimpleGraph.Walk.mem_support_of_mem_edges he
    change v ∈ s(c.source,c.target)
    exact (Sym2.mem_iff').mpr (hc.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm))
  have hbelow := rayIndex_bond_faces_eq_of_not_mem p
    (⟨(v.1,v.2-1),.vertical⟩ : LatticeBond) (hnot _ (Or.inr (by
      apply Prod.ext
      · rfl
      · change v.2-1+1 = v.2
        omega)))
  have hleft := rayIndex_bond_faces_eq_of_not_mem p
    (⟨(v.1-1,v.2),.horizontal⟩ : LatticeBond) (hnot _ (Or.inr (by
      apply Prod.ext
      · change v.1-1+1 = v.1
        omega
      · rfl)))
  have hright := rayIndex_bond_faces_eq_of_not_mem p
    (⟨v,.horizontal⟩ : LatticeBond) (hnot _ (Or.inl rfl))
  simp only [faceIndexMark,LatticeBond.faceBase,sub_add_cancel] at hbelow hleft hright
  rcases latticeBond_incident_cases b v hb with rfl | rfl | rfl | rfl <;>
    rcases hf with rfl | rfl <;>
    simp only [faceIndexMark,LatticeBond.faceBase,sub_add_cancel]
  · exact hbelow.symm
  · exact hright.symm.trans hbelow.symm
  · exact hleft.symm
  · exact hleft.symm
  · exact hright.symm.trans hbelow.symm
  · exact hbelow.symm

end PottsContinuity.Push
