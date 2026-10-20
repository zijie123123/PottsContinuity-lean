module

public import PottsContinuity.BD12.SeedClusterRevealTree
public import PottsContinuity.BD12.SeedMediatedConnection
public import PottsContinuity.BD12.ActiveOriginalQuery

/-! Every active query of the concrete seed exploration touches an actual seed
cluster in the final sampled configuration. No revealment bound is assumed. -/

@[expose] public section

namespace PottsContinuity.BD12
open FKC.FiniteFK
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance seedSupportEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance seedSupportEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Pathwise support of active queries for the actual constructed exploration.
The seed-mediated observable is determined before the arbitrary completion
phase, so every active query has an endpoint in a final actual seed cluster. -/
theorem seedClusterRevealTree_active_query_support
    (rank : G.edgeSet ≃ Fin (Fintype.card G.edgeSet)) (S B : Finset V) (o : V)
    (w : Configuration G → Set.Ioi (0 : ℝ)) (U : ℕ → ℝ) (t : ℕ)
    (R H : Configuration G) (e : G.edgeSet)
    (hquery : finiteActiveOriginalQueryAt w (seedMediatedIndicator G S B o) U t
      (seedClusterRevealTree G rank S R H) H = some e) :
    e ∈ actualMultiClusterReveal G S
      (finiteOriginalEval w U (seedClusterRevealTree G rank S R H) H) := by
  classical
  by_cases hR : R = Finset.univ
  · subst R
    rw [seedClusterRevealTree] at hquery
    simp only at hquery
    cases hquery
  let a := seedClusterSelect G rank S R H hR
  let next := fun b => seedClusterRevealTree G rank S (insert a.val R) (finiteRevealPattern H a.val b)
  have htree : seedClusterRevealTree G rank S R H = FiniteRevealTree.query a.val a.property next := by
    rw [seedClusterRevealTree, dite_eq_right hR]
  rw [htree] at hquery ⊢
  by_cases hlt : t < R.card
  · simp only [finiteActiveOriginalQueryAt, ite_eq_left hlt] at hquery
    cases hquery
  by_cases hd : finiteDetermines (seedMediatedIndicator G S B o) R H
  · simp only [finiteActiveOriginalQueryAt, ite_eq_right hlt, ite_eq_left hd] at hquery
    cases hquery
  by_cases ht : t = R.card
  · simp only [finiteActiveOriginalQueryAt, ite_eq_right hlt, ite_eq_right hd, ite_eq_left ht] at hquery
    have hae : a.val = e := Option.some.inj hquery
    have hfront : (seedClusterFrontier G S R H).Nonempty := by
      by_contra hn
      exact hd (seedMediatedIndicator_determined_of_frontier_empty G S B o R H
        (Finset.not_nonempty_iff_eq_empty.mp hn))
    have haF := seedClusterSelect_mem_frontier G rank S R H hR hfront
    obtain ⟨⟨u, hu, s, hs, hsu⟩, _⟩ := (seedClusterFrontier_mem_iff G S R H a.val).mp haF
    have hsub : H ∩ R ⊆ finiteOriginalEval w U (FiniteRevealTree.query a.val a.property next) H := by
      intro d hdR
      have hinter := finiteOriginalEval_inter w U (FiniteRevealTree.query a.val a.property next) H
      exact (Finset.mem_inter.mp ((Finset.ext_iff.mp hinter d).mpr hdR)).1
    rw [actualMultiClusterReveal_mem_iff]
    exact ⟨u, hae ▸ hu, s, hs, actualConnected_mono hsub hsu⟩
  simp only [finiteActiveOriginalQueryAt, ite_eq_right hlt, ite_eq_right hd, ite_eq_right ht] at hquery
  simp only [finiteOriginalEval]
  exact seedClusterRevealTree_active_query_support rank S B o w U t _ _ e hquery
termination_by Fintype.card G.edgeSet - R.card
decreasing_by exact remaining_card_insert_lt _ _ a.property

end
end PottsContinuity.BD12
