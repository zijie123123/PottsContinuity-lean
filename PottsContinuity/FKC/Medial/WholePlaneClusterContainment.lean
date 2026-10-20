-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/WholePlaneClusterContainment.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.WholePlaneTraversalEvents
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Pigeonhole

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK

noncomputable section

/-- The literal open primal graph read from the existing unordered edge-state
carrier. -/
def wholePlaneOpenPrimalGraph (ω : LatticeConfiguration) : SimpleGraph LatticeVertex where
  Adj u v := ∃ h : squareLattice.Adj u v,
    ω ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ = true
  symm := ⟨by
    intro u v h
    rcases h with ⟨h, hopen⟩
    refine ⟨h.symm, ?_⟩
    have hedge : (⟨s(v, u), squareLattice.mem_edgeSet.mpr h.symm⟩ : squareLattice.edgeSet) =
        ⟨s(u, v), squareLattice.mem_edgeSet.mpr h⟩ := by
      apply Subtype.ext
      exact Sym2.eq_swap
    rw [hedge]
    exact hopen⟩
  loopless := ⟨by
    intro u h
    rcases h with ⟨h, _⟩
    exact squareLattice.loopless.irrefl u h⟩

def wholePlaneOpenCluster (ω : LatticeConfiguration) (u : LatticeVertex) : Set LatticeVertex :=
  {v | Relation.EqvGen (wholePlaneOpenPrimalGraph ω).Adj u v}

theorem wholePlaneOpenPrimalGraph_adj_bond (ω : LatticeConfiguration) (b : LatticeBond) :
    (wholePlaneOpenPrimalGraph ω).Adj b.source b.target ↔
      latticeConfigurationBondState ω b = true := by
  constructor
  · rintro ⟨_, h⟩
    simpa [latticeConfigurationBondState, latticeBondEdge, LatticeBond.toSym2] using h
  · intro h
    exact ⟨b.adjacent, by simpa [latticeConfigurationBondState, latticeBondEdge,
      LatticeBond.toSym2] using h⟩

end
end PottsContinuity.FKC.Medial
