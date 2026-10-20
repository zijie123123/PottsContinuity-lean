module

public import PottsContinuity.Thm3.Push.BondFaceIndex
public import PottsContinuity.FKC.Domains.LatticePolygonCellExteriorConnectivity
public import PottsContinuity.FKC.Medial.WholePlaneDualGraph
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality
noncomputable section

/-- The identity on lattice vertices, preserving actual nearest-neighbor edges. -/
def polygonRayLatticeHom : PD.FK.squareLattice →g FKC.squareLattice where
  toFun := id
  map_rel' := fun h => (FKC.squareLattice_adj_iff _ _).mpr
    ((PD.FK.squareLattice_adj_iff _ _).mp h)

/-- A primal bond on the cycle separates exactly one interior cell from one
exterior cell in the actual bounded Jordan domain. -/
theorem polygonRay_bond_mem_iff_cell_difference {z : LatticeVertex}
    (p : PD.FK.squareLattice.Walk z z) (hp : p.IsCycle)
    (b : FKC.Medial.LatticeBond) (δ : FKC.PositiveMesh) :
    b.toSym2 ∈ p.edges ↔
      (b.faceBase true ∈ (FKC.latticePolygonOfCycle
        ((p.isCycle_map_iff_of_injective (show Function.Injective polygonRayLatticeHom from
          fun _ _ h => h)).mpr hp)).interiorCellBases δ) ≠
      (b.faceBase false ∈ (FKC.latticePolygonOfCycle
        ((p.isCycle_map_iff_of_injective (show Function.Injective polygonRayLatticeHom from
          fun _ _ h => h)).mpr hp)).interiorCellBases δ) := by
  classical
  let r := p.map polygonRayLatticeHom
  have hr : r.IsCycle := (p.isCycle_map_iff_of_injective
    (show Function.Injective polygonRayLatticeHom from fun _ _ h => h)).mpr hp
  let P := FKC.latticePolygonOfCycle hr
  have hmap : r.edges = p.edges := by
    rw [SimpleGraph.Walk.edges_map]
    change List.map (Sym2.map id) p.edges = p.edges
    simp only [Sym2.map_id, List.map_id]
  rw [← hmap]
  constructor
  · intro hb
    obtain ⟨i, hi⟩ := (FKC.latticePolygonOfCycle_edge_iff hr b.toSym2).mp hb
    have heq : b = P.boundaryBond i := FKC.Medial.LatticeBond.toSym2_injective
      (hi.trans (P.boundaryBond_toSym2 i).symm)
    have hmem := (FKC.LatticePolygon.mem_latticeCellBoundaryBonds_interiorCellBases_iff_boundaryBond
      P δ b).mpr ⟨i, heq⟩
    exact (FKC.mem_latticeCellBoundaryBonds _ _).mp hmem
  · intro hd
    have hmem := (FKC.mem_latticeCellBoundaryBonds _ _).mpr hd
    obtain ⟨i, hi⟩ :=
      (FKC.LatticePolygon.mem_latticeCellBoundaryBonds_interiorCellBases_iff_boundaryBond
        P δ b).mp hmem
    apply (FKC.latticePolygonOfCycle_edge_iff hr b.toSym2).mpr
    exact ⟨i, congrArg FKC.Medial.LatticeBond.toSym2 hi |>.trans
      (P.boundaryBond_toSym2 i)⟩

/-- The ray index is constant across two neighboring exterior cells. The
mark for a face base c is c+(1,1), matching the discrete ray convention. -/
theorem polygonRay_exterior_cell_adjacent {z : LatticeVertex}
    (p : PD.FK.squareLattice.Walk z z) (hp : p.IsCycle)
    (δ : FKC.PositiveMesh) {u v : FKC.LatticeVertex}
    (hadj : FKC.squareLattice.Adj u v)
    (hu : u ∉ (FKC.latticePolygonOfCycle
      ((p.isCycle_map_iff_of_injective (show Function.Injective polygonRayLatticeHom from
        fun _ _ h => h)).mpr hp)).interiorCellBases δ)
    (hv : v ∉ (FKC.latticePolygonOfCycle
      ((p.isCycle_map_iff_of_injective (show Function.Injective polygonRayLatticeHom from
        fun _ _ h => h)).mpr hp)).interiorCellBases δ) :
    rayIndex (Push.faceIndexMark u) p = rayIndex (Push.faceIndexMark v) p := by
  obtain ⟨d, hd⟩ := FKC.Medial.LatticeBond.exists_of_adj hadj
  let b := FKC.Medial.primalBondOfDual d
  have hs : b.faceBase false = d.source := by
    rw [← FKC.Medial.dualBondOfPrimal_source,
      FKC.Medial.dualBondOfPrimal_primalBondOfDual]
  have ht : b.faceBase true = d.target := by
    rw [← FKC.Medial.dualBondOfPrimal_target,
      FKC.Medial.dualBondOfPrimal_primalBondOfDual]
  have hnot : b.toSym2 ∉ p.edges := by
    intro hb
    have hdiff := (polygonRay_bond_mem_iff_cell_difference p hp b δ).mp hb
    rw [hs, ht] at hdiff
    have heq : s(d.source,d.target) = s(u,v) := hd
    rcases Sym2.eq_iff.mp heq with ⟨h₁,h₂⟩ | ⟨h₂,h₁⟩
    · rw [h₁,h₂] at hdiff
      exact hdiff (by simp only [hu,hv])
    · rw [h₁,h₂] at hdiff
      exact hdiff (by simp only [hu,hv])
  have hindex : rayIndex (Push.faceIndexMark (b.faceBase false)) p =
      rayIndex (Push.faceIndexMark (b.faceBase true)) p := by
    rcases b with ⟨c, axis⟩
    cases axis with
    | horizontal =>
      exact Push.rayIndex_bond_faces_eq_of_not_mem p
        ⟨c, .horizontal⟩ hnot
    | vertical =>
      exact Push.rayIndex_bond_faces_eq_of_not_mem p
        ⟨c, .vertical⟩ hnot
  rw [hs, ht] at hindex
  have heq : s(d.source,d.target) = s(u,v) := hd
  rcases Sym2.eq_iff.mp heq with ⟨h₁,h₂⟩ | ⟨h₂,h₁⟩
  · simpa only [h₁,h₂] using hindex
  · simpa only [h₁,h₂] using hindex.symm

end
end PottsContinuity.RSW
