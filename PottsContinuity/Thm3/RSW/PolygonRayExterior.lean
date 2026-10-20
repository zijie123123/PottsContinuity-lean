module

public import PottsContinuity.Thm3.RSW.PolygonRayCell
public import PottsContinuity.PD.Duality.RayIndexSeparation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality
noncomputable section

/-- Every exterior cell has zero ray index, using connectedness of the actual
exterior cell graph and finiteness of the nonzero-index set. -/
theorem polygonRay_exterior_cell_zero {z : LatticeVertex}
    (p : PD.FK.squareLattice.Walk z z) (hp : p.IsCycle)
    (δ : FKC.PositiveMesh) (u : FKC.LatticeVertex)
    (hu : u ∉ (FKC.latticePolygonOfCycle
      ((p.isCycle_map_iff_of_injective (show Function.Injective polygonRayLatticeHom from
        fun _ _ h => h)).mpr hp)).interiorCellBases δ) :
    rayIndex (Push.faceIndexMark u) p = 0 := by
  classical
  let r := p.map polygonRayLatticeHom
  have hr : r.IsCycle := (p.isCycle_map_iff_of_injective
    (show Function.Injective polygonRayLatticeHom from fun _ _ h => h)).mpr hp
  let P := FKC.latticePolygonOfCycle hr
  let S := P.interiorCellBases δ
  have hmark : Function.Injective Push.faceIndexMark := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    simp only [Push.faceIndexMark, Prod.mk.injEq] at h ⊢
    omega
  have hfinite : {c : LatticeVertex | rayIndex (Push.faceIndexMark c) p ≠ 0}.Finite :=
    Set.Finite.preimage hmark.injOn (finite_nonzero_rayIndex p)
  obtain ⟨a, ha⟩ := (S.finite_toSet.union hfinite).exists_notMem
  have haS : a ∉ S := fun h => ha (Or.inl h)
  have haZero : rayIndex (Push.faceIndexMark a) p = 0 := by
    by_contra h
    exact ha (Or.inr h)
  let G := FKC.squareLattice.induce {c : LatticeVertex | c ∉ S}
  have hconn : G.Connected :=
    FKC.Domains.squareLattice_induce_latticePolygon_exteriorCellBases_connected hr δ
  obtain ⟨w⟩ := hconn.preconnected (⟨u,hu⟩ : {c : LatticeVertex // c ∉ S}) ⟨a,haS⟩
  have hinvariant : ∀ {v w : {c : LatticeVertex // c ∉ S}}, (G.Walk v w) →
      rayIndex (Push.faceIndexMark v.val) p = rayIndex (Push.faceIndexMark w.val) p := by
    intro v w q
    induction q with
    | nil => rfl
    | @cons v w t hadj q ih =>
      exact (polygonRay_exterior_cell_adjacent p hp δ hadj v.property w.property).trans ih
  exact (hinvariant w).trans haZero

/-- A nonzero ray index at the correctly shifted mark places the corresponding
cell center in the actual bounded Jordan domain. -/
theorem polygonRay_cellCenter_mem_domain_of_ne_zero {z : LatticeVertex}
    (p : PD.FK.squareLattice.Walk z z) (hp : p.IsCycle)
    (δ : FKC.PositiveMesh) (u : FKC.LatticeVertex)
    (hu : rayIndex (Push.faceIndexMark u) p ≠ 0) :
    FKC.latticeCellCenter δ u ∈ (FKC.latticePolygonOfCycle
      ((p.isCycle_map_iff_of_injective (show Function.Injective polygonRayLatticeHom from
        fun _ _ h => h)).mpr hp)).domain δ := by
  apply (FKC.LatticePolygon.mem_interiorCellBases_iff _ δ u).mp
  by_contra h
  exact hu (polygonRay_exterior_cell_zero p hp δ u h)

end
end PottsContinuity.RSW
