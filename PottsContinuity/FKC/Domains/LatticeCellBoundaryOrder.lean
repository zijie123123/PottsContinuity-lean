-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticeCellBoundaryOrder.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.LatticeCellBoundary
public import PottsContinuity.FKC.Medial.WholePlaneDualGraph
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Domains

open PottsContinuity.FKC
open PottsContinuity.FKC.Medial
open SimpleGraph

private theorem cell_membership_agrees_across_complement_edge
    (S T : Finset LatticeVertex)
    (hboundary : latticeCellBoundaryBonds S ⊆ latticeCellBoundaryBonds T)
    {a b : LatticeVertex} (hadj : squareLattice.Adj a b)
    (haT : a ∉ T) (hbT : b ∉ T) :
    (a ∈ S ↔ b ∈ S) := by
  obtain ⟨d, hd⟩ := LatticeBond.exists_of_adj hadj
  let e := primalBondOfDual d
  have hfalse : e.faceBase false = d.source := by
    simpa [e] using (dualBondOfPrimal_source (primalBondOfDual d)).symm
  have htrue : e.faceBase true = d.target := by
    simpa [e] using (dualBondOfPrimal_target (primalBondOfDual d)).symm
  have hendpoints :
      (e.faceBase false = a ∧ e.faceBase true = b) ∨
      (e.faceBase false = b ∧ e.faceBase true = a) := by
    rw [hfalse, htrue]
    exact Sym2.eq_iff.mp hd
  have heT : e ∉ latticeCellBoundaryBonds T := by
    intro he
    rw [mem_latticeCellBoundaryBonds] at he
    rcases hendpoints with ⟨hfa,hfb⟩ | ⟨hfb,hfa⟩
    · rw [hfa,hfb] at he
      exact he (by simp [haT, hbT])
    · rw [hfb,hfa] at he
      exact he (by simp [haT, hbT])
  have heS : e ∉ latticeCellBoundaryBonds S := fun he => heT (hboundary he)
  have hcolors : (e.faceBase true ∈ S) ↔ (e.faceBase false ∈ S) := by
    rw [mem_latticeCellBoundaryBonds] at heS
    exact Iff.of_eq (not_ne_iff.mp heS)
  rcases hendpoints with ⟨hfa,hfb⟩ | ⟨hfb,hfa⟩
  · simpa [hfa,hfb] using hcolors.symm
  · simpa [hfb,hfa] using hcolors

private theorem membership_preserved_along_complement_walk
    (S T : Finset LatticeVertex)
    (hboundary : latticeCellBoundaryBonds S ⊆ latticeCellBoundaryBonds T)
    {a b : {z : LatticeVertex // z ∉ T}}
    (w : (squareLattice.induce {z : LatticeVertex | z ∉ T}).Walk a b)
    (haS : (a : LatticeVertex) ∉ S) : (b : LatticeVertex) ∉ S := by
  induction w with
  | nil => exact haS
  | @cons x y z hxy tail ih =>
      apply ih
      have hadj : squareLattice.Adj (x : LatticeVertex) (y : LatticeVertex) := hxy
      have hagree := cell_membership_agrees_across_complement_edge S T hboundary
        hadj x.property y.property
      exact fun hyS => haS (hagree.mpr hyS)

private theorem exists_cell_outside_finset (U : Finset LatticeVertex) :
    ∃ c : LatticeVertex, c ∉ U := by
  classical
  by_cases hnonempty : U.Nonempty
  · obtain ⟨c, hc, hmax⟩ := U.exists_max_image (fun x => x.1) hnonempty
    refine ⟨(c.1 + 1, c.2), ?_⟩
    intro heast
    have hle := hmax (c.1 + 1, c.2) heast
    omega
  · have hEq : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    exact ⟨(0, 0), by simp [hEq]⟩

theorem latticeCellBoundaryBonds_subset_of_complement_connected
    (S T : Finset LatticeVertex)
    (hconnected : (squareLattice.induce
      {z : LatticeVertex | z ∉ T}).Connected)
    (hboundary : latticeCellBoundaryBonds S ⊆ latticeCellBoundaryBonds T) :
    S ⊆ T := by
  classical
  intro c hcS
  by_contra hcT
  obtain ⟨far, hfar⟩ := exists_cell_outside_finset (S ∪ T)
  have hfarS : far ∉ S := by
    intro h
    exact hfar (Finset.mem_union.mpr (Or.inl h))
  have hfarT : far ∉ T := by
    intro h
    exact hfar (Finset.mem_union.mpr (Or.inr h))
  obtain ⟨root⟩ := hconnected.nonempty
  let G := squareLattice.induce {z : LatticeVertex | z ∉ T}
  have hfromRootC : G.Reachable root ⟨c,hcT⟩ := hconnected.preconnected root ⟨c,hcT⟩
  have hfromRootFar : G.Reachable root ⟨far,hfarT⟩ := hconnected.preconnected root ⟨far,hfarT⟩
  have hwalk : G.Reachable ⟨c,hcT⟩ ⟨far,hfarT⟩ := hfromRootC.symm.trans hfromRootFar
  rcases hwalk.symm with ⟨w⟩
  have hcNotS := membership_preserved_along_complement_walk S T hboundary w hfarS
  exact hcNotS hcS

end PottsContinuity.FKC.Domains
