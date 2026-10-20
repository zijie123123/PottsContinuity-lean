-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/ExteriorBranches.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.RCInfinite.ExteriorClusters
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

open Set

namespace PottsContinuity.PD.RCInfinite
open FK
noncomputable section
open scoped Classical

/-- The square-lattice neighbors of a vertex form a finite set. -/
theorem squareLattice_neighborSet_finite (x : LatticeVertex) :
    (squareLattice.neighborSet x).Finite := by
  let N : Finset LatticeVertex :=
    {(x.1 + 1, x.2), (x.1 - 1, x.2), (x.1, x.2 + 1), (x.1, x.2 - 1)}
  apply N.finite_toSet.subset
  intro y hy
  rw [SimpleGraph.mem_neighborSet] at hy
  rw [squareLattice_adj_iff] at hy
  simp only [Finset.mem_coe, N, Finset.mem_insert, Finset.mem_singleton]
  rcases hy with ⟨h, h'⟩ | ⟨h, h'⟩
  · rcases h with h | h
    · exact Or.inl (Prod.ext h.symm h'.symm)
    · right
      left
      exact Prod.ext (by omega) h'.symm
  · rcases h' with hstep | hstep
    · right
      right
      left
      exact Prod.ext h.symm hstep.symm
    · right
      right
      right
      exact Prod.ext h.symm (by omega)

/-- In a locally finite graph, an infinite component has a neighbor whose
component remains infinite after deleting the base vertex. -/
theorem infinite_component_has_infinite_deleted_neighbor
    {V : Type*} (G : SimpleGraph V) (y : V)
    (hN : (G.neighborSet y).Finite)
    (hinf : {z | G.Reachable y z}.Infinite) :
    ∃ z, G.Adj y z ∧
      {w | (G.deleteIncidenceSet y).Reachable z w}.Infinite := by
  classical
  by_contra hnone
  have hfinite (z : G.neighborSet y) :
      ({w | (G.deleteIncidenceSet y).Reachable z.val w}).Finite := by
    by_contra hz
    exact hnone ⟨z.val, z.property,
      Set.infinite_coe_iff.mp (not_finite_iff_infinite.mp hz)⟩
  have hcover : {z | G.Reachable y z} ⊆
      {y} ∪ ⋃ z : G.neighborSet y,
        {w | (G.deleteIncidenceSet y).Reachable z.val w} := by
    intro z hyz
    by_cases hzy : z = y
    · simp [hzy]
    · obtain ⟨p, hp⟩ := hyz.exists_isPath
      obtain ⟨u, hyu, q, rfl⟩ := p.exists_eq_cons_of_ne (Ne.symm hzy)
      have havoid : y ∉ q.support :=
        (SimpleGraph.Walk.cons_isPath_iff hyu q).mp hp |>.2
      have hdel : (G.deleteIncidenceSet y).Reachable u z :=
        walk_reachable_deleteIncidenceSet q havoid
      right
      exact mem_iUnion.mpr ⟨⟨u, hyu⟩, hdel⟩
  have hfiniteCover :
      ({y} ∪ ⋃ z : G.neighborSet y,
        {w | (G.deleteIncidenceSet y).Reachable z.val w}).Finite := by
    let : Finite (G.neighborSet y) := hN.to_subtype
    exact (finite_singleton y).union (Set.finite_iUnion hfinite)
  exact hinf.not_finite (hfiniteCover.subset hcover)

/-- An infinite exterior component has an open branch which remains infinite
after its exit vertex is removed. -/
theorem exteriorInfiniteAt_has_deleted_neighbor (ω : LatticeConfiguration)
    (n : ℕ) (y : LatticeVertex) (hinf : ω ∈ exteriorInfiniteAt n y) :
    ∃ z, (exteriorOpenGraph ω n).Adj y z ∧
      {w | ((exteriorOpenGraph ω n).deleteIncidenceSet y).Reachable z w}.Infinite := by
  have hinf' : {z | (exteriorOpenGraph ω n).Reachable y z}.Infinite :=
    (exteriorInfiniteAt_iff_infinite ω n y).mp hinf
  have hsub : (exteriorOpenGraph ω n).neighborSet y ⊆ squareLattice.neighborSet y := by
    intro z hz
    change (exteriorOpenGraph ω n).Adj y z at hz
    change squareLattice.Adj y z
    obtain ⟨he, _⟩ := (rcInfiniteOpenGraph_adj ω y z).mp
      ((exteriorOpenGraph_le ω n) hz)
    exact squareLattice.mem_edgeSet.mp he
  exact infinite_component_has_infinite_deleted_neighbor
    (exteriorOpenGraph ω n) y
    ((squareLattice_neighborSet_finite y).subset hsub) hinf'

end
end PottsContinuity.PD.RCInfinite
