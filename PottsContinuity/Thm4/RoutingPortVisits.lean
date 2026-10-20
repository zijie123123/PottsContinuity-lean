/- Actual queried-visit characterizations adapted from FKconvergence, an earlier formalization
by the same author that is not publicly accessible (see `related_formalizations` in
formalization.yaml): file `Medial/ParafermionicCoverEdgeCutRoutingVisits.lean`; the false-visit
definition is from its file `Medial/ParafermionicCoverEdgeVisitClassification.lean`.
Adaptation: namespace relocation; omit unused phase, toggle-case, and zero-return imports.
-/
module

public import PottsContinuity.Thm4.EdgeCutRoutingWalk
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
noncomputable section

/-- False-layer ports on the actual chosen origin exploration path that query
one specified embedded finite edge. -/
def parafermionicCoverFiniteEdgeFalseVisits (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    Finset (ParafermionicCoverFinitePort n) :=
  Finset.univ.filter fun c =>
    parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e ∧
      (c, false) ∈
        (parafermionicCoverFiniteOriginExplorationPath n hn A).support

private theorem cornerCutSourcePath_support_eq (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal) :
    (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i).support =
      (parafermionicCoverFiniteEdgeCutSourcePath n hn A e i).support := by
  simp [parafermionicCoverFiniteEdgeCutSourcePath_cornerCut,
    SimpleGraph.Walk.support_copy]

private theorem queried_visit_in_cutPath_endpoints
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal)
    (c : ParafermionicCoverFinitePort n)
    (hc : parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e)
    (hvisit : (c, false) ∈
      (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i).support) :
    (c, false) = (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 ∨
      (c, false) = (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1 := by
  have hqueried : c ∈ parafermionicCoverFiniteEdgeCutQueriedPorts n e := by
    simp [parafermionicCoverFiniteEdgeCutQueriedPorts, hc]
  let t := parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse n hn e c hqueried
  have hpoint : t.1 = (c, false) := rfl
  have htvisit : t.1 ∈
      (parafermionicCoverFiniteEdgeCutSourcePath n hn A e i).support := by
    rw [cornerCutSourcePath_support_eq] at hvisit
    rw [hpoint]
    exact hvisit
  rcases parafermionicCoverFiniteEdgeCutSourcePath_terminals n hn A e i t htvisit with hs | ht
  · left
    simpa [parafermionicCoverFiniteEdgeCutSourceLabelsEquiv] using hpoint.symm.trans hs
  · right
    have hend := parafermionicCoverFiniteEdgeCutSourcePath_end_eq_sinkLabel n hn A e i
    simpa [parafermionicCoverFiniteEdgeCutSinkLabelsEquiv] using hpoint.symm.trans (ht.trans hend)

private theorem queried_visit_iff_cutPath_endpoint
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal)
    (c : ParafermionicCoverFinitePort n)
    (hc : parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e) :
    (c, false) ∈
      (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i).support ↔
    (c, false) = (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 ∨
      (c, false) = (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1 := by
  constructor
  · exact queried_visit_in_cutPath_endpoints n hn A e i c hc
  · intro h
    rcases h with hs | ht
    · rw [hs]
      exact (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i).start_mem_support
    · rw [ht]
      exact (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i).end_mem_support

private theorem source_label_nonzero_queried (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal) (hi : i ≠ 0) :
    (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1.1 ∈
      parafermionicCoverFiniteEdgeCutQueriedPorts n e := by
  have hcases : i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
  rcases hcases with rfl | rfl
  · exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closed_queried
  · exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).open_queried

private theorem sink_label_nonzero_queried (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal) (hi : i ≠ 0) :
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e i).1.1.1 ∈
      parafermionicCoverFiniteEdgeCutQueriedPorts n e := by
  have hcases : i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
  rcases hcases with rfl | rfl
  · exact (parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e).1
  · exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosed_queried

private theorem source_label_point_one (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSourceLabels n hn e 1).1.1 =
      ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closedPort, false) := rfl

private theorem source_label_point_two (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSourceLabels n hn e 2).1.1 =
      ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort, false) := rfl

private theorem sink_label_point_one (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e 1).1.1 =
      (parafermionicCoverFiniteEdgeCutSeedPort n hn e, false) := rfl

private theorem sink_label_point_two (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e 2).1.1 =
      ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosedPort, false) := rfl

private theorem routing_successor_zero_iff_terminal_zero
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal) :
    parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i = 0 ↔
      parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i = 0 := by
  constructor
  · exact parafermionicCoverFiniteEdgeCutRoutingSuccessor_zero_terminal n hn A e i
  · intro hp
    by_cases he : e ∈ A
    · simp [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he,
        openRoutingSuccessor_apply, hp, threeTerminalSwap_zero]
    · simp [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he, hp]

private theorem source_sink_label_ports_ne (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) (i j : ThreeTerminal)
    (hi : i ≠ 0) (hj : j ≠ 0) :
    (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1.1 ≠
      (parafermionicCoverFiniteEdgeCutSinkLabels n hn e j).1.1.1 := by
  have hicases : i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
  have hjcases : j = 1 ∨ j = 2 := by fin_cases j <;> simp_all
  rcases hicases with rfl | rfl <;> rcases hjcases with rfl | rfl
  · intro h
    have h' : parafermionicCoverFiniteEdgeCutSeedPort n hn e =
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closedPort := by
      simpa [source_label_point_one, sink_label_point_one,
        parafermionicCoverFiniteEdgeCutSourceClosedLabel,
        parafermionicCoverFiniteEdgeCutSinkSeedLabel,
        parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using h.symm
    exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).distinct_seed_closed h'
  · intro h
    exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).distinct_closed_openClosed
      (by simpa [source_label_point_one, sink_label_point_two,
        parafermionicCoverFiniteEdgeCutSourceClosedLabel,
        parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel,
        parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using h)
  · intro h
    have h' : parafermionicCoverFiniteEdgeCutSeedPort n hn e =
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort := by
      simpa [source_label_point_two, sink_label_point_one,
        parafermionicCoverFiniteEdgeCutSourceOpenLabel,
        parafermionicCoverFiniteEdgeCutSinkSeedLabel,
        parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using h.symm
    exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).distinct_seed_open h'
  · intro h
    exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).distinct_open_openClosed
      (by simpa [source_label_point_two, sink_label_point_two,
        parafermionicCoverFiniteEdgeCutSourceOpenLabel,
        parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel,
        parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using h)

private theorem source_label_point_nonzero (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal) (hi : i ≠ 0) :
    (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 =
      ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1.1, false) := by
  have hcases : i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
  rcases hcases with rfl | rfl
  · simp [parafermionicCoverFiniteEdgeCutSourceClosedLabel,
      parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse]
  · simp [parafermionicCoverFiniteEdgeCutSourceOpenLabel,
      parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse]

private theorem sink_label_point_nonzero (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal) (hi : i ≠ 0) :
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e i).1.1 =
      ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e i).1.1.1, false) := by
  have hcases : i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
  rcases hcases with rfl | rfl
  · simp [parafermionicCoverFiniteEdgeCutSinkSeedLabel,
      parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse]
  · simp [parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel,
      parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse]

private theorem source_label_ports_ne_of_ne (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) (i j : ThreeTerminal)
    (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1.1 ≠
      (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1.1 := by
  have hicases : i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
  have hjcases : j = 1 ∨ j = 2 := by fin_cases j <;> simp_all
  rcases hicases with rfl | rfl <;> rcases hjcases with rfl | rfl
  · exact (hij rfl).elim
  · intro h
    exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).distinct_open_closed.symm
      (by simpa [source_label_point_one, source_label_point_two,
        parafermionicCoverFiniteEdgeCutSourceClosedLabel,
        parafermionicCoverFiniteEdgeCutSourceOpenLabel,
        parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using h)
  · intro h
    exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).distinct_open_closed
      (by simpa [source_label_point_one, source_label_point_two,
        parafermionicCoverFiniteEdgeCutSourceClosedLabel,
        parafermionicCoverFiniteEdgeCutSourceOpenLabel,
        parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using h)
  · exact (hij rfl).elim

private theorem sink_label_ports_ne_of_ne (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) (i j : ThreeTerminal)
    (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e i).1.1.1 ≠
      (parafermionicCoverFiniteEdgeCutSinkLabels n hn e j).1.1.1 := by
  have hicases : i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
  have hjcases : j = 1 ∨ j = 2 := by fin_cases j <;> simp_all
  rcases hicases with rfl | rfl <;> rcases hjcases with rfl | rfl
  · exact (hij rfl).elim
  · intro h
    exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).distinct_seed_openClosed
      (by simpa [sink_label_point_one, sink_label_point_two,
        parafermionicCoverFiniteEdgeCutSinkSeedLabel,
        parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel,
        parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using h)
  · intro h
    exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).distinct_seed_openClosed.symm
      (by simpa [sink_label_point_one, sink_label_point_two,
        parafermionicCoverFiniteEdgeCutSinkSeedLabel,
        parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel,
        parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using h)
  · exact (hij rfl).elim

theorem queried_visit_two_segment_iff (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (h0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) = 0)
    (c : ParafermionicCoverFinitePort n) :
    c ∈ parafermionicCoverFiniteEdgeFalseVisits n hn A e ↔
      c = (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0)).1.1.1 ∨
      c = (parafermionicCoverFiniteEdgeCutSourceLabels n hn e
        (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0)).1.1.1 := by
  classical
  let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
  let i := r 0
  have hi : i ≠ 0 := by simpa [i, r] using h0
  have hpi0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0 := by
    intro hp
    have hr : r 0 = 0 := (routing_successor_zero_iff_terminal_zero n hn A e 0).2 hp
    exact h0 (by simpa [r] using hr)
  let k := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0
  have hk : k ≠ 0 := by simpa [k] using hpi0
  have hterminal : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i = 0 :=
    parafermionicCoverFiniteEdgeCutRoutingSuccessor_zero_terminal n hn A e i (by
      simpa [i, r] using h1)
  have hsource0 : (parafermionicCoverFiniteEdgeCutSourceLabels n hn e 0).1.1.2 = true := by
    simp [parafermionicCoverFiniteEdgeCutSourceLabels_zero,
      parafermionicCoverFiniteEdgeCutSourceCorner]
  have hsinkLast : (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1.2 = true := by
    rw [hterminal]
    simp [parafermionicCoverFiniteEdgeCutSinkLabels_zero,
      parafermionicCoverFiniteEdgeCutSinkCorner]
  have hroute := parafermionicCoverFiniteEdgeCutRoutingWalk_twoSegments n hn A e h0 h1
  have hsupport (x : ParafermionicCoverFinitePort n) :
      (x, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support ↔
      (x, false) ∈
        (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e 0).support ∨
      (x, false) ∈
        (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i).support := by
    rw [← parafermionicCoverFiniteEdgeCutRoutingWalk_eq_originExploration n hn A e]
    rw [hroute]
    simp [i, r, SimpleGraph.Walk.support_copy,
      parafermionicCoverFiniteEdgeCutRoutingSplice_support, List.mem_append]
  constructor
  · intro hc
    have hmem := (Finset.mem_filter.mp hc).2.2
    have hedge := (Finset.mem_filter.mp hc).2.1
    rw [hsupport] at hmem
    rcases hmem with hleft | hright
    · rcases (queried_visit_iff_cutPath_endpoint n hn A e 0 c hedge).mp hleft with hs | ht
      · have hh : (parafermionicCoverFiniteEdgeCutSourceLabels n hn e 0).1.1.2 = false :=
          (congrArg Prod.snd hs).symm
        rw [hsource0] at hh
        cases hh
      · exact Or.inl (congrArg Prod.fst ht)
    · rcases (queried_visit_iff_cutPath_endpoint n hn A e i c hedge).mp hright with hs | ht
      · exact Or.inr (congrArg Prod.fst hs)
      · have hh : (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
          (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1.2 = false :=
          (congrArg Prod.snd ht).symm
        rw [hsinkLast] at hh
        cases hh
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases h with h | h
    · subst c
      refine ⟨?_, ?_⟩
      · simpa [parafermionicCoverFiniteEdgeCutQueriedPorts] using
          sink_label_nonzero_queried n hn e k hk
      · apply (hsupport _).mpr
        left
        apply (queried_visit_iff_cutPath_endpoint n hn A e 0 _ ?_).mpr
        · exact Or.inr (by simpa using (sink_label_point_nonzero n hn e k hk).symm)
        · simpa [parafermionicCoverFiniteEdgeCutQueriedPorts] using
            sink_label_nonzero_queried n hn e k hk
    · subst c
      refine ⟨?_, ?_⟩
      · simpa [parafermionicCoverFiniteEdgeCutQueriedPorts] using
          source_label_nonzero_queried n hn e i hi
      · apply (hsupport _).mpr
        right
        apply (queried_visit_iff_cutPath_endpoint n hn A e i _ ?_).mpr
        · exact Or.inl (by simpa using (source_label_point_nonzero n hn e i hi).symm)
        · simpa [parafermionicCoverFiniteEdgeCutQueriedPorts] using
            source_label_nonzero_queried n hn e i hi

theorem queried_visit_three_segment_iff (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (h0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) ≠ 0)
    (c : ParafermionicCoverFinitePort n) :
    c ∈ parafermionicCoverFiniteEdgeFalseVisits n hn A e ↔
      c = (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0)).1.1.1 ∨
      c = (parafermionicCoverFiniteEdgeCutSourceLabels n hn e
        (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0)).1.1.1 ∨
      c = (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
          (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0))).1.1.1 ∨
      c = (parafermionicCoverFiniteEdgeCutSourceLabels n hn e
        (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
          (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0))).1.1.1 := by
  classical
  let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
  let i := r 0
  let j := r i
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let k := π 0
  let l := π i
  have hi : i ≠ 0 := by simpa [i, r] using h0
  have hj : j ≠ 0 := by simpa [j, i, r] using h1
  have hk : k ≠ 0 := by
    intro hz
    have hz' := (routing_successor_zero_iff_terminal_zero n hn A e 0).2 hz
    exact h0 (by simpa [r] using hz')
  have hl : l ≠ 0 := by
    intro hz
    have hz' := (routing_successor_zero_iff_terminal_zero n hn A e i).2 hz
    exact h1 (by simpa [r, i] using hz')
  have hreturn : r j = 0 := by
    exact parafermionicCoverFiniteEdgeCutRoutingSuccessor_three_return r
      (by simpa [i, r] using h0) (by simpa [i, r] using h1)
  have hlast : π j = 0 := by
    exact (routing_successor_zero_iff_terminal_zero n hn A e j).1 (by simpa [r] using hreturn)
  have hsource0 : (parafermionicCoverFiniteEdgeCutSourceLabels n hn e 0).1.1.2 = true := by
    simp [parafermionicCoverFiniteEdgeCutSourceLabels_zero,
      parafermionicCoverFiniteEdgeCutSourceCorner]
  have hsinkLast : (parafermionicCoverFiniteEdgeCutSinkLabels n hn e (π j)).1.1.2 = true := by
    rw [hlast]
    simp [parafermionicCoverFiniteEdgeCutSinkLabels_zero,
      parafermionicCoverFiniteEdgeCutSinkCorner]
  have hroute := parafermionicCoverFiniteEdgeCutRoutingWalk_threeSegments n hn A e h0 h1
  have hsupport (x : ParafermionicCoverFinitePort n) :
      (x, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support ↔
      (x, false) ∈ (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e 0).support ∨
      (x, false) ∈ (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i).support ∨
      (x, false) ∈ (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e j).support := by
    rw [← parafermionicCoverFiniteEdgeCutRoutingWalk_eq_originExploration n hn A e]
    rw [hroute]
    simp [i, j, r, SimpleGraph.Walk.support_copy,
      parafermionicCoverFiniteEdgeCutRoutingSplice_support, List.mem_append]
  constructor
  · intro hc
    have hmem := (Finset.mem_filter.mp hc).2.2
    have hedge := (Finset.mem_filter.mp hc).2.1
    rw [hsupport] at hmem
    rcases hmem with hp0 | hrest
    · rcases (queried_visit_iff_cutPath_endpoint n hn A e 0 c hedge).mp hp0 with hs | ht
      · have hh : (parafermionicCoverFiniteEdgeCutSourceLabels n hn e 0).1.1.2 = false :=
          (congrArg Prod.snd hs).symm
        rw [hsource0] at hh
        cases hh
      · exact Or.inl (congrArg Prod.fst ht)
    · rcases hrest with hpi | hpj
      · rcases (queried_visit_iff_cutPath_endpoint n hn A e i c hedge).mp hpi with hs | ht
        · exact Or.inr (Or.inl (congrArg Prod.fst hs))
        · exact Or.inr (Or.inr (Or.inl (congrArg Prod.fst ht)))
      · rcases (queried_visit_iff_cutPath_endpoint n hn A e j c hedge).mp hpj with hs | ht
        · exact Or.inr (Or.inr (Or.inr (congrArg Prod.fst hs)))
        · have hh : (parafermionicCoverFiniteEdgeCutSinkLabels n hn e (π j)).1.1.2 = false :=
            (congrArg Prod.snd ht).symm
          rw [hsinkLast] at hh
          cases hh
  · intro h
    rcases h with h | h | h | h
    · subst c
      have hpt := sink_label_point_nonzero n hn e k hk
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      refine ⟨?_, ?_⟩
      · simpa [parafermionicCoverFiniteEdgeCutQueriedPorts] using
          sink_label_nonzero_queried n hn e k hk
      · apply (hsupport _).mpr
        left
        apply (queried_visit_iff_cutPath_endpoint n hn A e 0 _ ?_).mpr
        · exact Or.inr hpt.symm
        · simpa [parafermionicCoverFiniteEdgeCutQueriedPorts] using
            sink_label_nonzero_queried n hn e k hk
    · subst c
      have hpt := source_label_point_nonzero n hn e i hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      refine ⟨?_, ?_⟩
      · simpa [parafermionicCoverFiniteEdgeCutQueriedPorts] using
          source_label_nonzero_queried n hn e i hi
      · apply (hsupport _).mpr
        right
        left
        apply (queried_visit_iff_cutPath_endpoint n hn A e i _ ?_).mpr
        · exact Or.inl hpt.symm
        · simpa [parafermionicCoverFiniteEdgeCutQueriedPorts] using
            source_label_nonzero_queried n hn e i hi
    · subst c
      have hpt := sink_label_point_nonzero n hn e l hl
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      refine ⟨?_, ?_⟩
      · simpa [parafermionicCoverFiniteEdgeCutQueriedPorts] using
          sink_label_nonzero_queried n hn e l hl
      · apply (hsupport _).mpr
        right
        left
        apply (queried_visit_iff_cutPath_endpoint n hn A e i _ ?_).mpr
        · exact Or.inr hpt.symm
        · simpa [parafermionicCoverFiniteEdgeCutQueriedPorts] using
            sink_label_nonzero_queried n hn e l hl
    · subst c
      have hpt := source_label_point_nonzero n hn e j hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      refine ⟨?_, ?_⟩
      · simpa [parafermionicCoverFiniteEdgeCutQueriedPorts] using
          source_label_nonzero_queried n hn e j hj
      · apply (hsupport _).mpr
        right
        right
        apply (queried_visit_iff_cutPath_endpoint n hn A e j _ ?_).mpr
        · exact Or.inl hpt.symm
        · simpa [parafermionicCoverFiniteEdgeCutQueriedPorts] using
            source_label_nonzero_queried n hn e j hj

end
end PottsContinuity.Thm4
