-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverFaceTransverseFilling.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceTransverseEdge
public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceCrossing
public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceEdgeIncidence
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC
open SimpleGraph

private theorem cover_rawMappedEdge_iff {n : ℕ}
    {u₀ : ParafermionicCoverBoxVertex n}
    (C : (parafermionicCoverBoxGraph n).Walk u₀ u₀)
    (a b : ParafermionicCoverBoxVertex n) :
    s(a.1,b.1) ∈ C.edges.map (Sym2.map Subtype.val) ↔ s(a,b) ∈ C.edges := by
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨e, he, hEq⟩
    have hmap : Sym2.map Subtype.val e = Sym2.map Subtype.val (s(a,b)) := by
      simpa [Sym2.map_mk] using hEq
    have heq := Sym2.map.injective Subtype.val_injective hmap
    simpa [heq] using he
  · intro h
    exact List.mem_map.mpr ⟨s(a,b), h, by simp [Sym2.map_mk]⟩

theorem parafermionicCoverSimpleCycleFillingSet_east_disagree_iff_rawMappedEdge
    {n : ℕ} (hn : 1 ≤ n) {u₀ : ParafermionicCoverBoxVertex n}
    (C : (parafermionicCoverBoxGraph n).Walk u₀ u₀) (hC : C.IsCycle)
    (i j : ParafermionicCoverFiniteFaceTopIndex n)
    (h : j.1 = parafermionicCoverCompassNeighbor i.1 0) :
    ¬ (i ∈ parafermionicCoverSimpleCycleFillingSet hn C hC ↔
       j ∈ parafermionicCoverSimpleCycleFillingSet hn C hC) ↔
      s(j.1, parafermionicCoverCompassNeighbor j.1 1) ∈
        C.edges.map (Sym2.map Subtype.val) := by
  obtain ⟨hforward, hbackward⟩ := parafermionicCoverFaceTransverseEdge_east i j h
  let a : ParafermionicCoverBoxVertex n :=
    ⟨j.1, (parafermionicCoverFiniteFaceDart_endpoints_mem n i.1 i.2 hforward).1⟩
  let b : ParafermionicCoverBoxVertex n :=
    ⟨parafermionicCoverCompassNeighbor j.1 1,
      (parafermionicCoverFiniteFaceDart_endpoints_mem n i.1 i.2 hforward).2⟩
  have hab : a.1 = j.1 ∧ b.1 = parafermionicCoverCompassNeighbor j.1 1 := by
    exact ⟨rfl,rfl⟩
  have hcrit := parafermionicCoverSimpleCycleFillingSet_adjacent_owner_disagree_iff_edge_mem
    hn C hC (parafermionicCoverSimpleCycleFillingSet hn C hC) i j a b
    (by simpa [a,b] using hforward) (by simpa [a,b] using hbackward) rfl
  simpa [a, b] using hcrit.trans (cover_rawMappedEdge_iff C a b).symm

theorem parafermionicCoverSimpleCycleFillingSet_north_disagree_iff_rawMappedEdge
    {n : ℕ} (hn : 1 ≤ n) {u₀ : ParafermionicCoverBoxVertex n}
    (C : (parafermionicCoverBoxGraph n).Walk u₀ u₀) (hC : C.IsCycle)
    (i j : ParafermionicCoverFiniteFaceTopIndex n)
    (h : j.1 = parafermionicCoverCompassNeighbor i.1 1) :
    ¬ (i ∈ parafermionicCoverSimpleCycleFillingSet hn C hC ↔
       j ∈ parafermionicCoverSimpleCycleFillingSet hn C hC) ↔
      s(parafermionicCoverCompassNeighbor j.1 0, j.1) ∈
        C.edges.map (Sym2.map Subtype.val) := by
  obtain ⟨hforward, hbackward⟩ := parafermionicCoverFaceTransverseEdge_north i j h
  let a : ParafermionicCoverBoxVertex n :=
    ⟨parafermionicCoverCompassNeighbor j.1 0,
      (parafermionicCoverFiniteFaceDart_endpoints_mem n i.1 i.2 hforward).1⟩
  let b : ParafermionicCoverBoxVertex n :=
    ⟨j.1, (parafermionicCoverFiniteFaceDart_endpoints_mem n i.1 i.2 hforward).2⟩
  have hab : a.1 = parafermionicCoverCompassNeighbor j.1 0 ∧ b.1 = j.1 := by
    exact ⟨rfl,rfl⟩
  have hcrit := parafermionicCoverSimpleCycleFillingSet_adjacent_owner_disagree_iff_edge_mem
    hn C hC (parafermionicCoverSimpleCycleFillingSet hn C hC) i j a b
    (by simpa [a,b] using hforward) (by simpa [a,b] using hbackward) rfl
  simpa [a, b] using hcrit.trans (cover_rawMappedEdge_iff C a b).symm

end PottsContinuity.FKC.Medial
