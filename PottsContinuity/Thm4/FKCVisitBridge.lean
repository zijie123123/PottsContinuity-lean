module

public import PottsContinuity.Thm4.FKCExplorationBridge
public import PottsContinuity.Thm4.RoutingPortVisits
public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutRoutingVisits
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverTwoReturnNonconnection

@[expose] public section

namespace PottsContinuity.Thm4.FKCBridge
open PottsContinuity.Thm4.Medial PottsContinuity.PD.FK
noncomputable section

private theorem sourceFlag (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : Fin 3) (hi : i ≠ 0) :
    parafermionicCoverIncomingPrimalLeft
      (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1.1 = false := by
  fin_cases i
  · exact (hi rfl).elim
  · exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closed_incoming_false
  · exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).open_incoming_false

private theorem sinkFlag (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : Fin 3) (hi : i ≠ 0) :
    parafermionicCoverIncomingPrimalLeft
      (parafermionicCoverFiniteEdgeCutSinkLabels n hn e i).1.1.1 = true := by
  fin_cases i
  · exact (hi rfl).elim
  · exact (parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e).2
  · exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosed_incoming_true

/-- A two-segment route has exactly two actual queried false-layer port visits. -/
theorem falseVisits_card_twoSegments (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (h0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) = 0) :
    (parafermionicCoverFiniteEdgeFalseVisits n hn A e).card = 2 := by
  classical
  let i := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0
  let k := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0
  have hk : k ≠ 0 := by
    intro hz
    apply h0
    by_cases he : e ∈ A <;>
      simp [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he,
        show parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 = 0 from hz,
        openRoutingSuccessor_apply, threeTerminalSwap_zero]
  let s := (parafermionicCoverFiniteEdgeCutSinkLabels n hn e k).1.1.1
  let t := (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1.1
  have hne : s ≠ t := by
    intro h
    have hf := congrArg (fun c : ParafermionicCoverFinitePort n =>
      parafermionicCoverIncomingPrimalLeft c.1) h
    have hs := sinkFlag n hn e k hk
    have ht := sourceFlag n hn e i h0
    change parafermionicCoverIncomingPrimalLeft s.1 = true at hs
    change parafermionicCoverIncomingPrimalLeft t.1 = false at ht
    rw [hs, ht] at hf
    cases hf
  have hset : parafermionicCoverFiniteEdgeFalseVisits n hn A e = {s, t} := by
    ext c
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact queried_visit_two_segment_iff n hn A e h0 h1 c
  rw [hset]
  exact Finset.card_pair hne

@[simp] theorem finiteEdgeEmbedding_eq (n : ℕ)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    PottsContinuity.FKC.Medial.parafermionicCoverFiniteEdgeEmbedding n (fkcEdgeEquiv n e) =
      fkcWholeEdgeEquiv (parafermionicCoverFiniteEdgeEmbedding n e) := by
  apply Subtype.ext
  rfl

/-- The full actual queried-visit set is carried bijectively, independent of seed labels. -/
theorem falseVisits_map (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteEdgeFalseVisits n hn (fkcConfiguration n A) (fkcEdgeEquiv n e) =
      (parafermionicCoverFiniteEdgeFalseVisits n hn A e).map (finitePortEquiv n).toEmbedding := by
  classical
  ext d
  obtain ⟨c, rfl⟩ := (finitePortEquiv n).surjective d
  rw [Finset.mem_map_equiv]
  simp only [PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteEdgeFalseVisits,
    parafermionicCoverFiniteEdgeFalseVisits, Finset.mem_filter, Finset.mem_univ, true_and]
  change (PottsContinuity.FKC.Medial.parafermionicCoverPortEdge (coverPortEquiv c.1) =
      PottsContinuity.FKC.Medial.parafermionicCoverFiniteEdgeEmbedding n (fkcEdgeEquiv n e) ∧ _) ↔ _
  rw [edge_eq, finiteEdgeEmbedding_eq, (fkcWholeEdgeEquiv).injective.eq_iff,
    exploration_visit_iff]
  simp only [Equiv.symm_apply_apply]

/-- A closed two-return class in our actual exploration is also a closed
FKC two-return class; the equivalence uses actual visits, not seed equality. -/
theorem fkc_closed_two_return (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (he : e ∉ A)
    (h0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) = 0) :
    let π := PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteEdgeCutTerminalPermutation n hn
      (fkcConfiguration n A) (fkcEdgeEquiv n e)
    π 0 ≠ 0 ∧ π (π 0) = 0 := by
  classical
  have hcard := falseVisits_card_twoSegments n hn A e
    (by simpa [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he] using h0)
    (by simpa [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he] using h1)
  have hcardF : (PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteEdgeFalseVisits n hn (fkcConfiguration n A)
      (fkcEdgeEquiv n e)).card = 2 := by
    rw [falseVisits_map, Finset.card_map]
    exact hcard
  have hformula := PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteEdgeFalseVisits_card_eq_two_mul_routingLength_sub_one
    n hn (fkcConfiguration n A) (fkcEdgeEquiv n e)
  have hclosedF : fkcEdgeEquiv n e ∉ fkcConfiguration n A := by simpa using he
  rw [PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteEdgeCutRoutingLength,
    PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteEdgeCutRoutingSuccessor, ite_eq_right hclosedF] at hformula
  dsimp only
  unfold PottsContinuity.FKC.Medial.firstPositiveReturnLength at hformula
  split_ifs at hformula with hzero hone
  · rw [hcardF] at hformula
    norm_num [PottsContinuity.FKC.Medial.firstPositiveReturnLength, hzero] at hformula
  · exact ⟨hzero, hone⟩
  · rw [hcardF] at hformula
    norm_num [PottsContinuity.FKC.Medial.firstPositiveReturnLength, hzero, hone] at hformula

end
end PottsContinuity.Thm4.FKCBridge
