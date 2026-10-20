module

public import PottsContinuity.BD12.AdaptiveRevealStrategy
public import PottsContinuity.FKC.FiniteFK.MultiSeedClusterExploration

/-! The boundary-seed exploration frontier and its literal least-ranked fresh
edge. Reachability uses only the actually known open edges H intersect R. -/

@[expose] public section

namespace PottsContinuity.BD12
open FKC.FiniteFK
noncomputable section

/-- The unique least-ranked element of a nonempty finite set, for a supplied
edge ordering. The definition uses the minimum, not a choice of a witness. -/
def finiteRankMinimum {E : Type*} [Fintype E] [DecidableEq E]
    (rank : E ≃ Fin (Fintype.card E)) (s : Finset E) (hs : s.Nonempty) : {e : E // e ∈ s} := by
  let r := (s.image rank).min' (hs.image rank)
  refine ⟨rank.symm r, ?_⟩
  obtain ⟨e, he, heq⟩ := Finset.mem_image.mp (Finset.min'_mem (s.image rank) (hs.image rank))
  change rank e = r at heq
  rw [← heq, rank.symm_apply_apply]
  exact he

variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance clusterFrontierEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance clusterFrontierEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Fresh edges incident to the clusters already connected to the seed set
using the known open edges. Empty frontier means exploration is complete. -/
def seedClusterFrontier (S : Finset V) (R H : Configuration G) : Configuration G :=
  actualMultiClusterReveal G S (H ∩ R) \ R

theorem seedClusterFrontier_mem_iff (S : Finset V) (R H : Configuration G) (e : G.edgeSet) :
    e ∈ seedClusterFrontier G S R H ↔
      (∃ u : V, u ∈ e.val ∧ ∃ s, s ∈ S ∧ ActualConnected G (H ∩ R) s u) ∧ e ∉ R := by
  classical
  simp only [seedClusterFrontier, Finset.mem_sdiff, actualMultiClusterReveal_mem_iff]

/-- Select the least-ranked frontier edge; once the frontier is empty, complete
the reveal tree by the least-ranked remaining edge. That completion will lie
after stopping for a seed-cluster observable, as proved separately. -/
def seedClusterSelect (rank : G.edgeSet ≃ Fin (Fintype.card G.edgeSet))
    (S : Finset V) (R H : Configuration G) (hR : R ≠ Finset.univ) : {e : G.edgeSet // e ∉ R} := by
  classical
  by_cases hf : (seedClusterFrontier G S R H).Nonempty
  · let e := finiteRankMinimum rank (seedClusterFrontier G S R H) hf
    exact ⟨e.val, (Finset.mem_sdiff.mp e.property).2⟩
  · have hrem : (Finset.univ \ R).Nonempty := Finset.sdiff_nonempty.mpr (by
      intro hsub
      exact hR (Finset.eq_univ_of_forall (fun e => hsub (Finset.mem_univ e))))
    let e := finiteRankMinimum rank (Finset.univ \ R) hrem
    exact ⟨e.val, (Finset.mem_sdiff.mp e.property).2⟩

/-- While the actual frontier is nonempty, the selected edge lies in it. -/
theorem seedClusterSelect_mem_frontier
    (rank : G.edgeSet ≃ Fin (Fintype.card G.edgeSet)) (S : Finset V)
    (R H : Configuration G) (hR : R ≠ Finset.univ)
    (hf : (seedClusterFrontier G S R H).Nonempty) :
    (seedClusterSelect G rank S R H hR).val ∈ seedClusterFrontier G S R H := by
  classical
  simpa only [seedClusterSelect, dite_eq_left hf] using
    (finiteRankMinimum rank (seedClusterFrontier G S R H) hf).property

end
end PottsContinuity.BD12
