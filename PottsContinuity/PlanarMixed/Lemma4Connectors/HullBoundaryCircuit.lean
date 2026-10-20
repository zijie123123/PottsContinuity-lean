module

public import PottsContinuity.PD.Duality.CircuitEnclosure
public import PottsContinuity.Thm3.RSW.BoxRayIndex
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.FK.Medial PD.Duality RSW
noncomputable section

private theorem cell_false_center (d : LatticeBond) :
    ((d.faceBase false).1+1,(d.faceBase false).2+1)=(primalBondOfDual d).source := by
  rcases d with ⟨⟨x,y⟩,axis⟩
  cases axis <;> simp [LatticeBond.faceBase,primalBondOfDual,LatticeBond.source]

private theorem cell_true_center (d : LatticeBond) :
    ((d.faceBase true).1+1,(d.faceBase true).2+1)=(primalBondOfDual d).target := by
  rcases d with ⟨⟨x,y⟩,axis⟩
  cases axis <;> simp [LatticeBond.faceBase,primalBondOfDual,LatticeBond.target]

/-- A cell-boundary walk cannot cross any primal bond whose two endpoints
belong to the selected finite hull, including all geometric core bonds. -/
theorem cellBoundary_walk_avoids_internal_bond (C : Finset LatticeVertex)
    {z w : LatticeVertex} (p : (latticeCellBoundaryGraph (vertexCellBases C)).Walk z w)
    (b : LatticeBond) (hs : b.source ∈ C) (ht : b.target ∈ C) :
    (dualBondOfPrimal b).toSym2 ∉ (p.mapLe (latticeCellBoundaryGraph_le _)).edges := by
  intro he
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at he
  obtain ⟨_,d,hd,hfaces⟩ := (latticeCellBoundaryGraph_adj_iff _ _ _).mp (p.adj_of_mem_edges he)
  have heq : d=dualBondOfPrimal b := LatticeBond.toSym2_injective hd
  subst d
  rw [mem_vertexCellBases,mem_vertexCellBases,cell_true_center,cell_false_center,
    primalBondOfDual_dualBondOfPrimal] at hfaces
  exact hfaces (propext (iff_of_true ht hs))

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
