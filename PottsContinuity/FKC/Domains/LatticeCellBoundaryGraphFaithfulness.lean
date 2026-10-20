-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticeCellBoundaryGraphFaithfulness.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.LatticeCellBoundary

@[expose] public section

namespace PottsContinuity.FKC

open PottsContinuity.FKC.Medial

theorem latticeCellBoundaryGraph_le_iff (S T : Finset LatticeVertex) :
    latticeCellBoundaryGraph S ≤ latticeCellBoundaryGraph T ↔
      latticeCellBoundaryBonds S ⊆ latticeCellBoundaryBonds T := by
  constructor
  · intro hle e heS
    have hS : (latticeCellBoundaryGraph S).Adj e.source e.target :=
      (latticeCellBoundaryGraph_adj_iff S e.source e.target).2
        ⟨e.adjacent, e, rfl, (mem_latticeCellBoundaryBonds S e).mp heS⟩
    obtain ⟨_, f, hEq, hfT⟩ :=
      (latticeCellBoundaryGraph_adj_iff T e.source e.target).mp (hle hS)
    have hSame : f.toSym2 = e.toSym2 := by
      simpa [LatticeBond.toSym2] using hEq
    have hfe : f = e := LatticeBond.toSym2_injective hSame
    have hf : f ∈ latticeCellBoundaryBonds T :=
      (mem_latticeCellBoundaryBonds T f).mpr hfT
    simpa [hfe] using hf
  · intro hsub u v huv
    obtain ⟨hadj, e, hedge, heS⟩ :=
      (latticeCellBoundaryGraph_adj_iff S u v).mp huv
    have he : e ∈ latticeCellBoundaryBonds S :=
      (mem_latticeCellBoundaryBonds S e).mpr heS
    have heT : e ∈ latticeCellBoundaryBonds T := hsub he
    exact (latticeCellBoundaryGraph_adj_iff T u v).2
      ⟨hadj, e, hedge, (mem_latticeCellBoundaryBonds T e).mp heT⟩

theorem latticeCellBoundaryGraph_eq_iff (S T : Finset LatticeVertex) :
    latticeCellBoundaryGraph S = latticeCellBoundaryGraph T ↔
      latticeCellBoundaryBonds S = latticeCellBoundaryBonds T := by
  constructor
  · intro h
    apply Finset.Subset.antisymm
    · exact (latticeCellBoundaryGraph_le_iff S T).mp (by rw [h])
    · exact (latticeCellBoundaryGraph_le_iff T S).mp (by rw [h])
  · intro h
    apply le_antisymm
    · exact (latticeCellBoundaryGraph_le_iff S T).2 (by simp [h])
    · exact (latticeCellBoundaryGraph_le_iff T S).2 (by simp [h])

theorem latticeCellBoundaryGraph_empty :
    latticeCellBoundaryGraph (∅ : Finset LatticeVertex) = ⊥ := by
  have hb : latticeCellBoundaryBonds (∅ : Finset LatticeVertex) = ∅ := by
    ext e
    simp [mem_latticeCellBoundaryBonds]
  apply le_antisymm
  · intro u v huv
    obtain ⟨_, e, _, hfaces⟩ :=
      (latticeCellBoundaryGraph_adj_iff (∅ : Finset LatticeVertex) u v).mp huv
    have he : e ∈ latticeCellBoundaryBonds (∅ : Finset LatticeVertex) :=
      (mem_latticeCellBoundaryBonds _ _).mpr hfaces
    rw [hb] at he
    simp at he
  · exact bot_le

end PottsContinuity.FKC
