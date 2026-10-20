module

public import PottsContinuity.Thm4.WindingDefectVisits
public import PottsContinuity.Thm4.RoutingPortVisits

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
noncomputable section

private theorem fin3_nonzero_cases (x : Fin 3) (hx : x ≠ 0) : x = 1 ∨ x = 2 := by
  fin_cases x <;> simp_all

private theorem fin3_distinct_nonzero_cases (x y : Fin 3) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x ≠ y) : (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) := by
  fin_cases x <;> fin_cases y <;> simp_all

private theorem incomingPort_ne_sourceLabel (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) (c : ParafermionicCoverFinitePort n)
    (hc : parafermionicCoverIncomingPrimalLeft c.1 = true)
    (i : Fin 3) (hi : i ≠ 0) :
    c ≠ (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1.1 := by
  fin_cases i
  · exact (hi rfl).elim
  · intro h
    have hf := congrArg (fun p : ParafermionicCoverFinitePort n =>
      parafermionicCoverIncomingPrimalLeft p.1) h
    change parafermionicCoverIncomingPrimalLeft c.1 =
      parafermionicCoverIncomingPrimalLeft
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closedPort.1 at hf
    rw [hc, (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closed_incoming_false] at hf
    cases hf
  · intro h
    have hf := congrArg (fun p : ParafermionicCoverFinitePort n =>
      parafermionicCoverIncomingPrimalLeft p.1) h
    change parafermionicCoverIncomingPrimalLeft c.1 =
      parafermionicCoverIncomingPrimalLeft
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort.1 at hf
    rw [hc, (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).open_incoming_false] at hf
    cases hf

private theorem queried_mem_visits_iff (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (c : ParafermionicCoverFinitePort n)
    (hc : c ∈ parafermionicCoverFiniteEdgeCutQueriedPorts n e) :
    c ∈ parafermionicCoverFiniteEdgeFalseVisits n hn A e ↔
      (c, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support := by
  classical
  have he := (Finset.mem_filter.mp hc).2
  simp only [parafermionicCoverFiniteEdgeFalseVisits, Finset.mem_filter,
    Finset.mem_univ, true_and, he]

/-- A two-segment actual route visits exactly one of the queried incoming strands. -/
theorem windingIncomingVisitCount_two_segments (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (h0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) = 0) :
    windingIncomingVisitCount n hn A e = 1 := by
  classical
  let seed := parafermionicCoverFiniteEdgeCutSeedPort n hn e
  let o := parafermionicCoverFiniteEdgeCutSeedOrbit n hn e
  let i := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0
  let k := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0
  have hk0 : k ≠ 0 := by
    intro hk
    apply h0
    by_cases he : e ∈ A <;>
      simp [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he,
        openRoutingSuccessor_apply, show parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 = 0 from hk,
        threeTerminalSwap_zero]
  have hs := queried_visit_two_segment_iff n hn A e h0 h1 seed
  have ho := queried_visit_two_segment_iff n hn A e h0 h1 o.openClosedPort
  rw [queried_mem_visits_iff n hn A e seed
    (parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e).1] at hs
  rw [queried_mem_visits_iff n hn A e o.openClosedPort o.openClosed_queried] at ho
  have hsne := incomingPort_ne_sourceLabel n hn e seed
    (parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e).2 i h0
  have hone := incomingPort_ne_sourceLabel n hn e o.openClosedPort
    o.openClosed_incoming_true i h0
  change _ ↔ seed = (parafermionicCoverFiniteEdgeCutSinkLabels n hn e k).1.1.1 ∨
    seed = (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1.1 at hs
  change _ ↔ o.openClosedPort = (parafermionicCoverFiniteEdgeCutSinkLabels n hn e k).1.1.1 ∨
    o.openClosedPort = (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1.1 at ho
  simp only [hsne, hone, or_false] at hs ho
  have hk : k = 1 ∨ k = 2 := fin3_nonzero_cases k hk0
  change (if (seed, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support
    then 1 else 0) + (if (o.openClosedPort, false) ∈
    (parafermionicCoverFiniteOriginExplorationPath n hn A).support then 1 else 0) = (1 : ℕ)
  rcases hk with hk | hk
  · rw [hk] at hs ho
    change _ ↔ seed = seed at hs
    change _ ↔ o.openClosedPort = seed at ho
    have hvs := hs.2 rfl
    have hno : (o.openClosedPort, false) ∉
        (parafermionicCoverFiniteOriginExplorationPath n hn A).support :=
      fun h => o.distinct_seed_openClosed (ho.1 h).symm
    simp only [hvs, hno,
      ↓reduceIte, add_zero]
  · rw [hk] at hs ho
    change _ ↔ seed = o.openClosedPort at hs
    change _ ↔ o.openClosedPort = o.openClosedPort at ho
    have hno : (seed, false) ∉
        (parafermionicCoverFiniteOriginExplorationPath n hn A).support :=
      fun h => o.distinct_seed_openClosed (hs.1 h)
    have hvo := ho.2 rfl
    simp only [hno, hvo,
      ↓reduceIte, zero_add]

/-- A three-segment actual route visits both of the queried incoming strands. -/
theorem windingIncomingVisitCount_three_segments (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (h0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) ≠ 0) :
    windingIncomingVisitCount n hn A e = 2 := by
  classical
  let seed := parafermionicCoverFiniteEdgeCutSeedPort n hn e
  let o := parafermionicCoverFiniteEdgeCutSeedOrbit n hn e
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
  let i := r 0
  let j := r i
  let k := π 0
  let l := π i
  have nonzero (x : Fin 3) (hx : r x ≠ 0) : π x ≠ 0 := by
    intro hz
    apply hx
    by_cases he : e ∈ A <;>
      simp [r, π, parafermionicCoverFiniteEdgeCutRoutingSuccessor, he,
        openRoutingSuccessor_apply, hz, threeTerminalSwap_zero]
  have hk0 : k ≠ 0 := nonzero 0 h0
  have hl0 : l ≠ 0 := nonzero i h1
  have hkl : k ≠ l := fun h => h0 (π.injective h).symm
  have hs := queried_visit_three_segment_iff n hn A e h0 h1 seed
  have ho := queried_visit_three_segment_iff n hn A e h0 h1 o.openClosedPort
  rw [queried_mem_visits_iff n hn A e seed
    (parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e).1] at hs
  rw [queried_mem_visits_iff n hn A e o.openClosedPort o.openClosed_queried] at ho
  have hsni := incomingPort_ne_sourceLabel n hn e seed
    (parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e).2 i h0
  have hsnj := incomingPort_ne_sourceLabel n hn e seed
    (parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e).2 j h1
  have honi := incomingPort_ne_sourceLabel n hn e o.openClosedPort o.openClosed_incoming_true i h0
  have honj := incomingPort_ne_sourceLabel n hn e o.openClosedPort o.openClosed_incoming_true j h1
  change _ ↔ seed = (parafermionicCoverFiniteEdgeCutSinkLabels n hn e k).1.1.1 ∨
    seed = (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1.1 ∨
    seed = (parafermionicCoverFiniteEdgeCutSinkLabels n hn e l).1.1.1 ∨
    seed = (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1.1 at hs
  change _ ↔ o.openClosedPort = (parafermionicCoverFiniteEdgeCutSinkLabels n hn e k).1.1.1 ∨
    o.openClosedPort = (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1.1 ∨
    o.openClosedPort = (parafermionicCoverFiniteEdgeCutSinkLabels n hn e l).1.1.1 ∨
    o.openClosedPort = (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1.1 at ho
  simp only [hsni, hsnj, honi, honj, false_or, or_false] at hs ho
  have hcases := fin3_distinct_nonzero_cases k l hk0 hl0 hkl
  have hvs : (seed, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support := by
    apply hs.2
    rcases hcases with ⟨hk, hl⟩ | ⟨hk, hl⟩
    · left; rw [hk]; rfl
    · right; rw [hl]; rfl
  have hvo : (o.openClosedPort, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support := by
    apply ho.2
    rcases hcases with ⟨hk, hl⟩ | ⟨hk, hl⟩
    · right; rw [hl]; rfl
    · left; rw [hk]; rfl
  change (if (seed, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support
    then 1 else 0) + (if (o.openClosedPort, false) ∈
    (parafermionicCoverFiniteOriginExplorationPath n hn A).support then 1 else 0) = (2 : ℕ)
  simp only [hvs, hvo, ↓reduceIte]

end
end PottsContinuity.Thm4
