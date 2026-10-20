-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticeCellIntersectionExteriorConnectivity.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.LatticePolygonCellExteriorConnectivity
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Domains

open PottsContinuity.FKC
open PottsContinuity.FKC.LatticePolygon
open SimpleGraph

def exteriorCellsGraph (S : Finset LatticeVertex) :
    SimpleGraph {z : LatticeVertex // z ∉ S} :=
  squareLattice.induce {z | z ∉ S}

private theorem exists_vertex_outside_union (S T : Finset LatticeVertex) :
    ∃ z : LatticeVertex, z ∉ S ∧ z ∉ T := by
  classical
  let X := (S ∪ T).image fun z : LatticeVertex => z.1
  have hcard : X.card < ENat.card ℤ := by simp
  obtain ⟨x,hx⟩ := Finset.exists_not_mem_of_card_lt_enatCard hcard
  refine ⟨(x,0), ?_, ?_⟩
  · intro hS
    have : x ∈ X := Finset.mem_image.mpr ⟨(x,0), Finset.mem_union_left T hS, rfl⟩
    exact hx this
  · intro hT
    have : x ∈ X := Finset.mem_image.mpr ⟨(x,0), Finset.mem_union_right S hT, rfl⟩
    exact hx this

theorem squareLattice_induce_compl_inter_connected_of_compl_connected
    (S T : Finset LatticeVertex)
    (hS : (squareLattice.induce {z : LatticeVertex | z ∉ S}).Connected)
    (hT : (squareLattice.induce {z : LatticeVertex | z ∉ T}).Connected) :
    (squareLattice.induce {z : LatticeVertex | z ∉ S ∩ T}).Connected := by
  classical
  let I := S ∩ T
  obtain ⟨a,haS,haT⟩ := exists_vertex_outside_union S T
  let anchor : {z : LatticeVertex // z ∉ I} := ⟨a, by
    intro haI
    exact haS (Finset.mem_inter.mp haI).1⟩
  let liftS : exteriorCellsGraph S →g exteriorCellsGraph I :=
    { toFun := fun z => ⟨z.1, by
        intro hzI
        exact z.2 ((Finset.mem_inter.mp hzI).1)⟩
      map_rel' := by intro x y h; exact h }
  let liftT : exteriorCellsGraph T →g exteriorCellsGraph I :=
    { toFun := fun z => ⟨z.1, by
        intro hzI
        exact z.2 ((Finset.mem_inter.mp hzI).2)⟩
      map_rel' := by intro x y h; exact h }
  rw [connected_iff_exists_forall_reachable]
  refine ⟨anchor, ?_⟩
  intro z
  by_cases hzS : z.1 ∉ S
  · have hCS := hS
    rw [connected_iff_exists_forall_reachable] at hCS
    obtain ⟨q,hq⟩ := hCS
    have hreachS : (exteriorCellsGraph S).Reachable ⟨a,haS⟩ ⟨z.1,hzS⟩ := by
      exact (hq ⟨a,haS⟩).symm.trans (hq ⟨z.1,hzS⟩)
    have hreachI := hreachS.map liftS
    have hstart : liftS ⟨a,haS⟩ = anchor := by
      apply Subtype.ext
      rfl
    have hend : liftS ⟨z.1,hzS⟩ = z := by
      apply Subtype.ext
      rfl
    exact hstart ▸ (hend ▸ hreachI)
  · have hzT : z.1 ∉ T := by
      intro hz
      have hzS' : z.1 ∈ S := by
        by_contra h
        exact hzS h
      exact z.2 (Finset.mem_inter.mpr ⟨hzS', hz⟩)
    have hCT := hT
    rw [connected_iff_exists_forall_reachable] at hCT
    obtain ⟨q,hq⟩ := hCT
    have hreachT : (exteriorCellsGraph T).Reachable ⟨a,haT⟩ ⟨z.1,hzT⟩ := by
      exact (hq ⟨a,haT⟩).symm.trans (hq ⟨z.1,hzT⟩)
    have hreachI := hreachT.map liftT
    have hstart : liftT ⟨a,haT⟩ = anchor := by
      apply Subtype.ext
      rfl
    have hend : liftT ⟨z.1,hzT⟩ = z := by
      apply Subtype.ext
      rfl
    exact hstart ▸ (hend ▸ hreachI)

theorem squareLattice_induce_compl_inter_cycleInteriorBases_connected
    {v w : LatticeVertex} {p : squareLattice.Walk v v} {q : squareLattice.Walk w w}
    (hp : p.IsCycle) (hq : q.IsCycle) (δ : PositiveMesh) :
    (squareLattice.induce
      {z : LatticeVertex | z ∉
        (latticePolygonOfCycle hp).interiorCellBases δ ∩
          (latticePolygonOfCycle hq).interiorCellBases δ}).Connected := by
  apply squareLattice_induce_compl_inter_connected_of_compl_connected
  · exact squareLattice_induce_latticePolygon_exteriorCellBases_connected hp δ
  · exact squareLattice_induce_latticePolygon_exteriorCellBases_connected hq δ

end PottsContinuity.FKC.Domains
