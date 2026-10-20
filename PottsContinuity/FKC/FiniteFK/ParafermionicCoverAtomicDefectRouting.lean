-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverAtomicDefectRouting.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverAtomicDefectPorts
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverEdgeCutSinkPhase
public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutRoutingVisits
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial
noncomputable section

private theorem source_point_one (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSourceLabels n hn e 1).1.1 =
      ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closedPort, false) := rfl

private theorem source_point_two (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSourceLabels n hn e 2).1.1 =
      ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort, false) := rfl

private theorem sink_point_one (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e 1).1.1 =
      (parafermionicCoverFiniteEdgeCutSeedPort n hn e, false) := rfl

private theorem sink_point_two (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e 2).1.1 =
      ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosedPort, false) := rfl

private theorem source_label_port_ne (n : ℕ) (hn : 1 ≤ n)
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
      (by simpa [source_point_one, source_point_two,
        parafermionicCoverFiniteEdgeCutSourceClosedLabel,
        parafermionicCoverFiniteEdgeCutSourceOpenLabel,
        parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using h)
  · intro h
    exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).distinct_open_closed
      (by simpa [source_point_one, source_point_two,
        parafermionicCoverFiniteEdgeCutSourceClosedLabel,
        parafermionicCoverFiniteEdgeCutSourceOpenLabel,
        parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using h)
  · exact (hij rfl).elim

private theorem sink_label_port_ne (n : ℕ) (hn : 1 ≤ n)
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
      (by simpa [sink_point_one, sink_point_two,
        parafermionicCoverFiniteEdgeCutSinkSeedLabel,
        parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel,
        parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using h)
  · intro h
    exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).distinct_seed_openClosed.symm
      (by simpa [sink_point_one, sink_point_two,
        parafermionicCoverFiniteEdgeCutSinkSeedLabel,
        parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel,
        parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using h)
  · exact (hij rfl).elim

private theorem source_sink_label_port_ne (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) (i j : ThreeTerminal)
    (hi : i ≠ 0) (hj : j ≠ 0) :
    (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1.1 ≠
      (parafermionicCoverFiniteEdgeCutSinkLabels n hn e j).1.1.1 := by
  have hicases : i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
  have hjcases : j = 1 ∨ j = 2 := by fin_cases j <;> simp_all
  rcases hicases with rfl | rfl <;> rcases hjcases with rfl | rfl
  · intro h
    exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).distinct_seed_closed
      (by simpa [source_point_one, sink_point_one,
        parafermionicCoverFiniteEdgeCutSourceClosedLabel,
        parafermionicCoverFiniteEdgeCutSinkSeedLabel,
        parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using h.symm)
  · intro h
    exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).distinct_closed_openClosed
      (by simpa [source_point_one, sink_point_two,
        parafermionicCoverFiniteEdgeCutSourceClosedLabel,
        parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel,
        parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using h)
  · intro h
    exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).distinct_seed_open
      (by simpa [source_point_two, sink_point_one,
        parafermionicCoverFiniteEdgeCutSourceOpenLabel,
        parafermionicCoverFiniteEdgeCutSinkSeedLabel,
        parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using h.symm)
  · intro h
    exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).distinct_open_openClosed
      (by simpa [source_point_two, sink_point_two,
        parafermionicCoverFiniteEdgeCutSourceOpenLabel,
        parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel,
        parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using h)

private theorem source_label_queried (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal) (hi : i ≠ 0) :
    (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1.1 ∈
      parafermionicCoverFiniteEdgeCutQueriedPorts n e := by
  have hcases : i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
  rcases hcases with rfl | rfl
  · simpa [source_point_one, parafermionicCoverFiniteEdgeCutSourceClosedLabel,
      parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using
      (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closed_queried
  · simpa [source_point_two, parafermionicCoverFiniteEdgeCutSourceOpenLabel,
      parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using
      (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).open_queried

private theorem sink_label_queried (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal) (hi : i ≠ 0) :
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e i).1.1.1 ∈
      parafermionicCoverFiniteEdgeCutQueriedPorts n e := by
  have hcases : i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
  rcases hcases with rfl | rfl
  · simpa [sink_point_one, parafermionicCoverFiniteEdgeCutSinkSeedLabel,
      parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using
      (parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e).1
  · simpa [sink_point_two, parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel,
      parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using
      (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosed_queried

private theorem phaseAtom_eq_zero_of_not_falseVisit
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (c : ParafermionicCoverFinitePort n)
    (hc : c ∈ parafermionicCoverFiniteEdgeCutQueriedPorts n e)
    (hnot : c ∉ parafermionicCoverFiniteEdgeFalseVisits n hn A e) :
    parafermionicCoverPathPhaseAtom q n hn A (c, false) = 0 := by
  have hedge : parafermionicCoverPortEdge c.1 =
      parafermionicCoverFiniteEdgeEmbedding n e :=
    (Finset.mem_filter.mp hc).2
  have hsupp : (c, false) ∉
      (parafermionicCoverFiniteOriginExplorationPath n hn A).support := by
    intro hmem
    apply hnot
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hedge, hmem⟩
  simp [parafermionicCoverPathPhaseAtom, hsupp]

private theorem routing_zero_iff_terminal_zero
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

def otherRoutingIndex (i : ThreeTerminal) : ThreeTerminal :=
  if i = 1 then 2 else 1

private theorem otherRoutingIndex_ne_zero (i : ThreeTerminal) (hi : i ≠ 0) :
    otherRoutingIndex i ≠ 0 := by
  fin_cases i <;> simp_all [otherRoutingIndex]

private theorem otherRoutingIndex_ne (i : ThreeTerminal) (hi : i ≠ 0) :
    otherRoutingIndex i ≠ i := by
  fin_cases i <;> simp_all [otherRoutingIndex]

private theorem sink_atoms_reindex
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (i : ThreeTerminal) (hi : i ≠ 0) :
    parafermionicCoverPathPhaseAtom q n hn A
        ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e 1).1.1) +
      parafermionicCoverPathPhaseAtom q n hn A
        ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e 2).1.1) =
    parafermionicCoverPathPhaseAtom q n hn A
        ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e i).1.1) +
      parafermionicCoverPathPhaseAtom q n hn A
        ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e
          (otherRoutingIndex i)).1.1) := by
  have hcases : i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
  rcases hcases with h | h
  · subst i
    simp [otherRoutingIndex]
  · subst i
    simp [otherRoutingIndex, add_comm]

private theorem source_atoms_reindex
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (i : ThreeTerminal) (hi : i ≠ 0) :
    parafermionicCoverPathPhaseAtom q n hn A
        ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e 1).1.1) +
      parafermionicCoverPathPhaseAtom q n hn A
        ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e 2).1.1) =
    parafermionicCoverPathPhaseAtom q n hn A
        ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1) +
      parafermionicCoverPathPhaseAtom q n hn A
        ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e
          (otherRoutingIndex i)).1.1) := by
  have hcases : i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
  rcases hcases with h | h
  · subst i
    simp [otherRoutingIndex]
  · subst i
    simp [otherRoutingIndex, add_comm]

private theorem fin3_nonzero_pair_sum (f : ThreeTerminal → ℂ)
    (i j : ThreeTerminal) (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    f 1 + f 2 = f i + f j := by
  have hicases : i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
  have hjcases : j = 1 ∨ j = 2 := by fin_cases j <;> simp_all
  rcases hicases with rfl | rfl <;> rcases hjcases with rfl | rfl
  · exact (hij rfl).elim
  · rfl
  · simp [add_comm]
  · exact (hij rfl).elim

private theorem source_label_false_point (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (i : ThreeTerminal) (hi : i ≠ 0) :
    (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 =
      ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1.1, false) := by
  have hcases : i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
  rcases hcases with rfl | rfl
  · rw [source_point_one]
  · rw [source_point_two]

private theorem sink_label_false_point (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (i : ThreeTerminal) (hi : i ≠ 0) :
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e i).1.1 =
      ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e i).1.1.1, false) := by
  have hcases : i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
  rcases hcases with rfl | rfl
  · rw [sink_point_one]
  · rw [sink_point_two]

private theorem twoRouting_no_other_sinkVisit
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (h0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) = 0) :
    let _r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
    let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e (otherRoutingIndex (π 0))).1.1.1 ∉
      parafermionicCoverFiniteEdgeFalseVisits n hn A e := by
  dsimp
  let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := r 0
  let k := π 0
  have hi : i ≠ 0 := by simpa [r, i] using h0
  have hk : k ≠ 0 := by
    intro h
    exact h0 (by simpa [r] using
      (routing_zero_iff_terminal_zero n hn A e 0).2 h)
  have hk' := otherRoutingIndex_ne_zero k hk
  have hkk' := otherRoutingIndex_ne k hk
  intro hc
  rcases (queried_visit_two_segment_iff n hn A e h0 h1
    ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e (otherRoutingIndex k)).1.1.1)).mp hc with hs | ht
  · exact (sink_label_port_ne n hn e (otherRoutingIndex k) k hk' hk hkk') hs
  · exact (source_sink_label_port_ne n hn e i (otherRoutingIndex k) hi hk') ht.symm

private theorem twoRouting_no_other_sourceVisit
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (h0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) = 0) :
    let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
    (parafermionicCoverFiniteEdgeCutSourceLabels n hn e
      (otherRoutingIndex (r 0))).1.1.1 ∉
      parafermionicCoverFiniteEdgeFalseVisits n hn A e := by
  dsimp
  let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := r 0
  let k := π 0
  have hi : i ≠ 0 := by simpa [r, i] using h0
  have hk : k ≠ 0 := by
    intro h
    exact h0 (by simpa [r] using
      (routing_zero_iff_terminal_zero n hn A e 0).2 h)
  have hi' := otherRoutingIndex_ne_zero i hi
  have hii' := otherRoutingIndex_ne i hi
  intro hc
  rcases (queried_visit_two_segment_iff n hn A e h0 h1
    ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e (otherRoutingIndex i)).1.1.1)).mp hc with hs | ht
  · exact (source_sink_label_port_ne n hn e (otherRoutingIndex i) k hi' hk) hs
  · exact (source_label_port_ne n hn e (otherRoutingIndex i) i hi' hi hii') ht

/-- In the two-segment routing, the actual atomic defect is the restored turn
factor minus one times the sole nonzero source phase. -/
theorem parafermionicCoverContourFiniteEdgeAtomicDefect_two_routing_factor
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (h0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) = 0) :
    let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
    let E := Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
      ((if e ∈ A then -1 else 1 : ℤ) : ℝ)))
    parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A =
      (E - 1) * parafermionicCoverPathPhaseAtom q n hn A
        (parafermionicCoverFiniteEdgeCutSourceLabels n hn e (r 0)).1.1 := by
  let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := r 0
  let k := π 0
  let k' := otherRoutingIndex k
  let i' := otherRoutingIndex i
  let E := Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
    ((if e ∈ A then -1 else 1 : ℤ) : ℝ)))
  have hi : i ≠ 0 := by simpa [r, i] using h0
  have hk : k ≠ 0 := by
    intro h
    exact h0 (by simpa [r] using
      (routing_zero_iff_terminal_zero n hn A e 0).2 h)
  have hi' := otherRoutingIndex_ne_zero i hi
  have hk' := otherRoutingIndex_ne_zero k hk
  have hii' := otherRoutingIndex_ne i hi
  have hkk' := otherRoutingIndex_ne k hk
  have hqSink := sink_label_queried n hn e k' hk'
  have hqSource := source_label_queried n hn e i' hi'
  have hzeroSink := phaseAtom_eq_zero_of_not_falseVisit q n hn A e _ hqSink
    (twoRouting_no_other_sinkVisit n hn A e h0 h1)
  have hzeroSource := phaseAtom_eq_zero_of_not_falseVisit q n hn A e _ hqSource
    (twoRouting_no_other_sourceVisit n hn A e h0 h1)
  have hsumSink := sink_atoms_reindex q n hn A e k hk
  have hsumSource := source_atoms_reindex q n hn A e i hi
  have hzeroSink' : parafermionicCoverPathPhaseAtom q n hn A
      ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e k').1.1) = 0 := by
    rw [sink_label_false_point n hn e k' hk']
    exact hzeroSink
  have hzeroSource' : parafermionicCoverPathPhaseAtom q n hn A
      ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e i').1.1) = 0 := by
    rw [source_label_false_point n hn e i' hi']
    exact hzeroSource
  have hphase := parafermionicCoverPathPhaseAtom_routing_two_sink q n hn A e h0 h1
  have hphase' : parafermionicCoverPathPhaseAtom q n hn A
      ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e k).1.1) =
      E * parafermionicCoverPathPhaseAtom q n hn A
        ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1) := by
    simpa [r, π, i, k, E] using hphase
  rw [parafermionicCoverContourFiniteEdgeAtomicDefect_eq_terminalLabels]
  calc
    _ = (parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e 1).1.1) +
        parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e 2).1.1)) -
        (parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e 1).1.1) +
        parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e 2).1.1)) := by ring
    _ = (parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e k).1.1) +
        parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e k').1.1)) -
        (parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1) +
        parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e i').1.1)) := by
      rw [hsumSink, hsumSource]
    _ = (E - 1) * parafermionicCoverPathPhaseAtom q n hn A
        ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1) := by
      rw [hzeroSink', hzeroSource', hphase']
      ring

/-- In a three-segment routing, both source ports contribute the same restored
turn factor to the actual signed atomic defect. -/
theorem parafermionicCoverContourFiniteEdgeAtomicDefect_three_routing_factor
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (h0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) ≠ 0) :
    let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
    let E := Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
      ((if e ∈ A then -1 else 1 : ℤ) : ℝ)))
    parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A =
      (E - 1) * (parafermionicCoverPathPhaseAtom q n hn A
        (parafermionicCoverFiniteEdgeCutSourceLabels n hn e (r 0)).1.1 +
      parafermionicCoverPathPhaseAtom q n hn A
        (parafermionicCoverFiniteEdgeCutSourceLabels n hn e (r (r 0))).1.1) := by
  let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := r 0
  let j := r i
  let k := π 0
  let l := π i
  let E := Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
    ((if e ∈ A then -1 else 1 : ℤ) : ℝ)))
  have hi : i ≠ 0 := by simpa [r, i] using h0
  have hj : j ≠ 0 := by simpa [r, i, j] using h1
  have hreturn := parafermionicCoverFiniteEdgeCutRoutingSuccessor_three_return r hi hj
  have hk : k ≠ 0 := by
    intro h
    exact h0 (by simpa [r, k] using
      (routing_zero_iff_terminal_zero n hn A e 0).2 h)
  have hl : l ≠ 0 := by
    intro h
    exact h1 (by simpa [r, i, l] using
      (routing_zero_iff_terminal_zero n hn A e i).2 h)
  have hij : i ≠ j := by
    intro h
    apply hj
    calc
      j = r i := rfl
      _ = r j := congrArg r h
      _ = 0 := hreturn
  have hkl : k ≠ l := by
    intro h
    exact hi ((parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e).injective
      (by simpa [k, l] using h)).symm
  have hsumSink :
      parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e 1).1.1) +
        parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e 2).1.1) =
      parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e k).1.1) +
        parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e l).1.1) :=
    fin3_nonzero_pair_sum (fun t => parafermionicCoverPathPhaseAtom q n hn A
      ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e t).1.1)) k l hk hl hkl
  have hsumSource :
      parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e 1).1.1) +
        parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e 2).1.1) =
      parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1) +
        parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1) :=
    fin3_nonzero_pair_sum (fun t => parafermionicCoverPathPhaseAtom q n hn A
      ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e t).1.1)) i j hi hj hij
  obtain ⟨hphase0, hphase1⟩ :=
    parafermionicCoverPathPhaseAtom_routing_three_sinks q n hn A e h0 h1
  have hphase0' : parafermionicCoverPathPhaseAtom q n hn A
      ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e k).1.1) =
      E * parafermionicCoverPathPhaseAtom q n hn A
        ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1) := by
    simpa [r, π, i, k, E] using hphase0
  have hphase1' : parafermionicCoverPathPhaseAtom q n hn A
      ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e l).1.1) =
      E * parafermionicCoverPathPhaseAtom q n hn A
        ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1) := by
    simpa [r, π, i, j, l, E] using hphase1
  rw [parafermionicCoverContourFiniteEdgeAtomicDefect_eq_terminalLabels]
  calc
    _ = (parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e 1).1.1) +
        parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e 2).1.1)) -
        (parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e 1).1.1) +
        parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e 2).1.1)) := by ring
    _ = (parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e k).1.1) +
        parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e l).1.1)) -
        (parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1) +
        parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1)) := by
      rw [hsumSink, hsumSource]
    _ = (E - 1) * (parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1) +
        parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1)) := by
      rw [hphase0', hphase1']
      ring

end
end PottsContinuity.FKC.FiniteFK
