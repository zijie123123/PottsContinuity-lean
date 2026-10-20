-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverEdgeCutFixedLoop.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutRoutingTurn
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
open SimpleGraph
noncomputable section

local instance fixedLoopPortFintype (n : ℕ) : Fintype (ParafermionicCoverFinitePort n) :=
  parafermionicCoverFinitePortFintype n

local instance fixedLoopCornerGraphDecidableRel (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    DecidableRel (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj := Classical.decRel _

local instance fixedLoopCutGraphDecidableRel (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    DecidableRel (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj := Classical.decRel _

private theorem fixedLoop_source_query
    (n : ℕ) (hn : 1 ≤ n) (e : (ParafermionicAmbientGraph n).edgeSet)
    (i : ThreeTerminal) (hi : i ≠ 0) :
    (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1.2 = false ∧
      parafermionicCoverPortEdge
        (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1.1 =
        parafermionicCoverFiniteEdgeEmbedding n e := by
  have hc : i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
  rcases hc with rfl | rfl
  · change (parafermionicCoverFiniteEdgeCutSourceClosedLabel n hn e).1.1.2 = false ∧
      parafermionicCoverPortEdge
        (parafermionicCoverFiniteEdgeCutSourceClosedLabel n hn e).1.1.1 =
        parafermionicCoverFiniteEdgeEmbedding n e
    constructor
    · rfl
    · exact (Finset.mem_filter.mp
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closed_queried).2
  · change (parafermionicCoverFiniteEdgeCutSourceOpenLabel n hn e).1.1.2 = false ∧
      parafermionicCoverPortEdge
        (parafermionicCoverFiniteEdgeCutSourceOpenLabel n hn e).1.1.1 =
        parafermionicCoverFiniteEdgeEmbedding n e
    constructor
    · rfl
    · exact (Finset.mem_filter.mp
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).open_queried).2

private theorem fixedLoop_sink_query
    (n : ℕ) (hn : 1 ≤ n) (e : (ParafermionicAmbientGraph n).edgeSet)
    (i : ThreeTerminal) (hi : i ≠ 0) :
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e i).1.1.2 = false ∧
      parafermionicCoverPortEdge
        (parafermionicCoverFiniteEdgeCutSinkLabels n hn e i).1.1.1 =
        parafermionicCoverFiniteEdgeEmbedding n e := by
  have hc : i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
  rcases hc with rfl | rfl
  · change (parafermionicCoverFiniteEdgeCutSinkSeedLabel n hn e).1.1.2 = false ∧
      parafermionicCoverPortEdge
        (parafermionicCoverFiniteEdgeCutSinkSeedLabel n hn e).1.1.1 =
        parafermionicCoverFiniteEdgeEmbedding n e
    constructor
    · rfl
    · exact (Finset.mem_filter.mp
        (parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e).1).2
  · change (parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel n hn e).1.1.2 = false ∧
      parafermionicCoverPortEdge
        (parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel n hn e).1.1.1 =
        parafermionicCoverFiniteEdgeEmbedding n e
    constructor
    · rfl
    · exact (Finset.mem_filter.mp
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosed_queried).2

def parafermionicCoverFiniteEdgeCutFixedLoop
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal)
    (hi : i ≠ 0)
    (hfix : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i = i) :
    (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk
      (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1
      (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 := by
  let p := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i
  have hadj : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj
      ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1)
      ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1) := by
    simpa [hfix] using
      parafermionicCoverFiniteEdgeCutRoutingAdj n hn A e i (by simpa [hfix] using hi)
  exact p.concat hadj


private theorem fixedLoop_path_avoids_restored_edge
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal)
    (hi : i ≠ 0)
    (hfix : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i = i) :
    Sym2.mk ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1)
      ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1) ∉
      (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i).edges := by
  have hπ : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i ≠ 0 := by
    intro hzero
    have hrzero : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i = 0 := by
      by_cases he : e ∈ A
      · simp [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he,
          openRoutingSuccessor_apply, threeTerminalSwap_zero, hzero]
      · simp [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he, hzero]
    exact hi (hfix.symm.trans hrzero)
  have hsrc := fixedLoop_source_query n hn e i hi
  have hsnk := fixedLoop_sink_query n hn e
    (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i) hπ
  have hnotAdj : ¬ (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj
      ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1)
      ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1) := by
    intro hadj
    have hcut := (parafermionicCoverFiniteEdgeCutGraph_adj_iff n hn A e _ _).mp hadj
    exact hcut.2 ⟨hsrc.1, hsnk.1, hsrc.2, hsnk.2⟩
  intro hmem
  let p := parafermionicCoverFiniteEdgeCutSourcePath n hn A e i
  have hs : (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1.1 =
      (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 := rfl
  have ht : (parafermionicCoverFiniteEdgeCutPartner n hn A e
      (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1).1 =
      (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1 := by
    simpa [parafermionicCoverFiniteEdgeCutSinkLabelsEquiv] using
      parafermionicCoverFiniteEdgeCutSourcePath_end_eq_sinkLabel n hn A e i
  have hmemCut : Sym2.mk ((parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1.1)
      ((parafermionicCoverFiniteEdgeCutPartner n hn A e
        (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1).1) ∈ p.edges := by
    have heq : (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i).edges = p.edges := by
      simp [p, parafermionicCoverFiniteEdgeCutSourcePath_cornerCut,
]
    rw [← heq]
    simpa [hs, ht] using hmem
  have hcutAdj := p.adj_of_mem_edges hmemCut
  exact hnotAdj (by simpa [hs, ht] using hcutAdj)

theorem parafermionicCoverFiniteEdgeCutFixedLoop_isCycle
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal)
    (hi : i ≠ 0)
    (hfix : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i = i) :
    (parafermionicCoverFiniteEdgeCutFixedLoop n hn A e i hi hfix).IsCycle := by
  let p := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i
  have hadj : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj
      ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1)
      ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1) := by
    simpa [hfix] using
      parafermionicCoverFiniteEdgeCutRoutingAdj n hn A e i (by simpa [hfix] using hi)
  have hnot := fixedLoop_path_avoids_restored_edge n hn A e i hi hfix
  have hrot : ((p.concat hadj).reverse).IsCycle := by
    rw [SimpleGraph.Walk.reverse_concat]
    exact (Walk.cons_isCycle_iff p.reverse hadj.symm).mpr
      ⟨(parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_isPath n hn A e i).reverse,
        by simpa [Walk.edges_reverse] using hnot⟩
  have hrev : (p.concat hadj).reverse.reverse.IsCycle := hrot.reverse
  simpa [parafermionicCoverFiniteEdgeCutFixedLoop, p, Walk.concat_eq_append] using hrev

theorem parafermionicCoverFiniteEdgeCutFixedLoop_turn
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal)
    (hi : i ≠ 0)
    (hfix : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i = i) :
    parafermionicCoverFinitePairingWalkTurn n hn A
      (parafermionicCoverFiniteEdgeCutFixedLoop n hn A e i hi hfix) =
      parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e i +
        (if e ∈ A then -1 else 1) := by
  unfold parafermionicCoverFiniteEdgeCutFixedLoop
  dsimp only
  rw [Walk.concat_eq_append]
  rw [parafermionicCoverFinitePairingWalkTurn_append]
  rw [parafermionicCoverFiniteEdgeCutSourceCornerTurn_eq_segment]
  simp only [parafermionicCoverFinitePairingWalkTurn,
    SimpleGraph.Walk.darts_cons, SimpleGraph.Walk.darts_nil,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simpa [hfix] using parafermionicCoverFiniteEdgeCutRoutingRestoredTurn n hn A e i
    (by simpa [hfix] using hi)

end
end PottsContinuity.FKC.FiniteFK
