-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Duality/LatticeCellBoundaryFiniteEdges.lean`, with
-- module and namespace relocated and declarations not used here removed.
/- That file was itself adapted from FKconvergence, an earlier formalization by the same author that is not publicly accessible, file `Domains/LatticeCellBoundaryFiniteEdges.lean`.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsContinuity.PD.Duality.LatticeCellBoundary
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.PD.FK

open Medial

/-- The graph edge set is exactly the image of the finite set of normalized
boundary bonds under their primal Sym2 representation. -/
theorem latticeCellBoundaryGraph_edgeSet_eq_image (S : Finset LatticeVertex) :
    (latticeCellBoundaryGraph S).edgeSet =
      LatticeBond.toSym2 '' (↑(latticeCellBoundaryBonds S) : Set LatticeBond) := by
  classical
  ext edge
  obtain ⟨⟨u, v⟩, hEdge⟩ := Sym2.mk_surjective edge
  subst edge
  change s(u, v) ∈ (latticeCellBoundaryGraph S).edgeSet ↔
    s(u, v) ∈ LatticeBond.toSym2 '' (↑(latticeCellBoundaryBonds S) : Set LatticeBond)
  simp only [SimpleGraph.mem_edgeSet, Set.mem_image]
  rw [latticeCellBoundaryGraph_adj_iff]
  constructor
  · rintro ⟨hadj, e, heq, hfaces⟩
    exact ⟨e, (mem_latticeCellBoundaryBonds S e).mpr hfaces, heq⟩
  · rintro ⟨e, he, hEq⟩
    have hsq : squareLattice.Adj u v := by
      have hedge := LatticeBond.toSym2_mem_edgeSet e
      rw [hEq] at hedge
      exact squareLattice.mem_edgeSet.mp hedge
    exact ⟨hsq, e, hEq, (mem_latticeCellBoundaryBonds S e).mp he⟩

theorem latticeCellBoundaryGraph_edgeSet_finite (S : Finset LatticeVertex) :
    ((latticeCellBoundaryGraph S).edgeSet : Set (Sym2 LatticeVertex)).Finite := by
  rw [latticeCellBoundaryGraph_edgeSet_eq_image]
  exact (latticeCellBoundaryBonds_finite S).image LatticeBond.toSym2

end PottsContinuity.PD.FK
