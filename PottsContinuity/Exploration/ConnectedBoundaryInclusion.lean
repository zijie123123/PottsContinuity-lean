module

public import PottsContinuity.FKC.Domains.LatticeCellBoundaryOrder

/-! A connected set of lattice cells is determined in the inclusion order by
its boundary bonds and one marked cell. -/

@[expose] public section

namespace PottsContinuity.Exploration

open PottsContinuity.FKC.Medial
open SimpleGraph

private theorem adjacent_cell_membership_iff
    (S T : Finset PottsContinuity.FKC.LatticeVertex)
    (hboundary : PottsContinuity.FKC.latticeCellBoundaryBonds T ⊆
      PottsContinuity.FKC.latticeCellBoundaryBonds S)
    {a b : PottsContinuity.FKC.LatticeVertex}
    (haS : a ∈ S) (hbS : b ∈ S)
    (hadj : PottsContinuity.FKC.squareLattice.Adj a b) :
    (a ∈ T ↔ b ∈ T) := by
  obtain ⟨d, hd⟩ := LatticeBond.exists_of_adj hadj
  let e := primalBondOfDual d
  have hfalse : e.faceBase false = d.source := by
    simpa [e] using (dualBondOfPrimal_source (primalBondOfDual d)).symm
  have htrue : e.faceBase true = d.target := by
    simpa [e] using (dualBondOfPrimal_target (primalBondOfDual d)).symm
  have heS : e ∉ PottsContinuity.FKC.latticeCellBoundaryBonds S := by
    intro he
    have hdiff := (PottsContinuity.FKC.mem_latticeCellBoundaryBonds S e).mp he
    rw [hfalse, htrue] at hdiff
    rcases Sym2.eq_iff.mp hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hdiff (by simp [haS, hbS])
    · exact hdiff (by simp [haS, hbS])
  have heT : e ∉ PottsContinuity.FKC.latticeCellBoundaryBonds T :=
    fun he => heS (hboundary he)
  have hcolors : (e.faceBase true ∈ T) ↔ (e.faceBase false ∈ T) := by
    rw [PottsContinuity.FKC.mem_latticeCellBoundaryBonds] at heT
    exact Iff.of_eq (not_ne_iff.mp heT)
  rcases Sym2.eq_iff.mp hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa [hfalse, htrue] using hcolors.symm
  · simpa [hfalse, htrue] using hcolors

/-- The union of two connected finite cell sets is connected when they share
a marked cell. -/
theorem induced_cell_union_connected
    (S T : Finset PottsContinuity.FKC.LatticeVertex)
    (hS : (PottsContinuity.FKC.squareLattice.induce
      (↑S : Set PottsContinuity.FKC.LatticeVertex)).Connected)
    (hT : (PottsContinuity.FKC.squareLattice.induce
      (↑T : Set PottsContinuity.FKC.LatticeVertex)).Connected)
    (u : PottsContinuity.FKC.LatticeVertex)
    (huS : u ∈ S) (huT : u ∈ T) :
    (PottsContinuity.FKC.squareLattice.induce
      (↑(S ∪ T) : Set PottsContinuity.FKC.LatticeVertex)).Connected := by
  classical
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨u, Finset.mem_union_left T huS⟩, ?_⟩
  intro z
  rcases Finset.mem_union.mp z.property with hzS | hzT
  · obtain ⟨w⟩ := hS.preconnected ⟨u, huS⟩ ⟨z.val, hzS⟩
    let f :
        PottsContinuity.FKC.squareLattice.induce
          (↑S : Set PottsContinuity.FKC.LatticeVertex) →g
        PottsContinuity.FKC.squareLattice.induce
          (↑(S ∪ T) : Set PottsContinuity.FKC.LatticeVertex) :=
      { toFun := fun x => ⟨x.val, Finset.mem_union_left T x.property⟩
        map_rel' := fun h => h }
    have hstart : f ⟨u, huS⟩ = ⟨u, Finset.mem_union_left T huS⟩ := by
      apply Subtype.ext
      rfl
    have hend : f ⟨z.val, hzS⟩ = z := by
      apply Subtype.ext
      rfl
    rw [← hstart, ← hend]
    exact ⟨w.map f⟩
  · obtain ⟨w⟩ := hT.preconnected ⟨u, huT⟩ ⟨z.val, hzT⟩
    let f :
        PottsContinuity.FKC.squareLattice.induce
          (↑T : Set PottsContinuity.FKC.LatticeVertex) →g
        PottsContinuity.FKC.squareLattice.induce
          (↑(S ∪ T) : Set PottsContinuity.FKC.LatticeVertex) :=
      { toFun := fun x => ⟨x.val, Finset.mem_union_right S x.property⟩
        map_rel' := fun h => h }
    have hstart : f ⟨u, huT⟩ = ⟨u, Finset.mem_union_left T huS⟩ := by
      apply Subtype.ext
      rfl
    have hend : f ⟨z.val, hzT⟩ = z := by
      apply Subtype.ext
      rfl
    rw [← hstart, ← hend]
    exact ⟨w.map f⟩

/-- Boundary inclusion propagates a marked-cell inclusion across a connected
finite cell set. -/
theorem latticeCellSet_subset_of_connected_of_boundary_inclusion
    (S T : Finset PottsContinuity.FKC.LatticeVertex)
    (hS : (PottsContinuity.FKC.squareLattice.induce
      (↑S : Set PottsContinuity.FKC.LatticeVertex)).Connected)
    (u : PottsContinuity.FKC.LatticeVertex)
    (huS : u ∈ S) (huT : u ∈ T)
    (hboundary : PottsContinuity.FKC.latticeCellBoundaryBonds T ⊆
      PottsContinuity.FKC.latticeCellBoundaryBonds S) :
    S ⊆ T := by
  classical
  intro x hxS
  obtain ⟨w⟩ := hS.preconnected ⟨u, huS⟩ ⟨x, hxS⟩
  have hwalk : ∀ {a b : {z : PottsContinuity.FKC.LatticeVertex // z ∈ S}}
      (p : (PottsContinuity.FKC.squareLattice.induce
        (↑S : Set PottsContinuity.FKC.LatticeVertex)).Walk a b),
      (a : PottsContinuity.FKC.LatticeVertex) ∈ T →
      (b : PottsContinuity.FKC.LatticeVertex) ∈ T := by
    intro a b p
    induction p with
    | nil => exact fun h => h
    | @cons a b c hab tail ih =>
      intro haT
      apply ih
      exact (adjacent_cell_membership_iff S T hboundary a.property b.property hab).mp haT
  exact hwalk w huT

end PottsContinuity.Exploration
