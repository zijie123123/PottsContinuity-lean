-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverFixedLoopCapEdge.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverFixedLoopPrimalIntersection
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedClosedCapEdges
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPortPrimalCrossing
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph PottsContinuity.FKC.FiniteFK
noncomputable section

private theorem fixedLoopCap_source_false_query
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
        (parafermionicCoverFiniteEdgeCutSourceClosedLabel n hn e).1.1.1 = _
    constructor
    · rfl
    · exact (Finset.mem_filter.mp
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closed_queried).2
  · change (parafermionicCoverFiniteEdgeCutSourceOpenLabel n hn e).1.1.2 = false ∧
      parafermionicCoverPortEdge
        (parafermionicCoverFiniteEdgeCutSourceOpenLabel n hn e).1.1.1 = _
    constructor
    · rfl
    · exact (Finset.mem_filter.mp
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).open_queried).2

private theorem fixedLoopCap_sink_false_query
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
        (parafermionicCoverFiniteEdgeCutSinkSeedLabel n hn e).1.1.1 = _
    constructor
    · rfl
    · exact (Finset.mem_filter.mp
        (parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e).1).2
  · change (parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel n hn e).1.1.2 = false ∧
      parafermionicCoverPortEdge
        (parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel n hn e).1.1.1 = _
    constructor
    · rfl
    · exact (Finset.mem_filter.mp
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosed_queried).2

/-- The closed queried edge contributes its actual restored sink-to-source
false-layer dart, with the queried port genuinely closed in the extension. -/
theorem parafermionicCoverFiniteEdgeCutFixedLoop_restoredClosedDart
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal)
    (hi : i ≠ 0)
    (hfix : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i = i)
    (he : e ∉ A) :
    ∃ d : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Dart,
      d ∈ (parafermionicCoverFiniteEdgeCutFixedLoop n hn A e i hi hfix).darts ∧
      d.fst = (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1 ∧
      d.snd = (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 ∧
      d.fst.2 = false ∧ d.snd.2 = false ∧
      parafermionicCoverPortEdge d.fst.1.1 = parafermionicCoverFiniteEdgeEmbedding n e ∧
      parafermionicCoverPortBondState
        (parafermionicCoverConfigurationExtensionState n A) d.fst.1.1 = false := by
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let j := π i
  let sink := parafermionicCoverFiniteEdgeCutSinkLabels n hn e j
  let src := parafermionicCoverFiniteEdgeCutSourceLabels n hn e i
  let p := parafermionicCoverFiniteEdgeCutFixedLoop n hn A e i hi hfix
  have hj : j = i := by
    dsimp [j, π]
    simpa [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he] using hfix
  have hsucc : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i ≠ 0 := by
    simpa [hfix] using hi
  have hadj := parafermionicCoverFiniteEdgeCutRoutingAdj n hn A e i hsucc
  rw [hfix] at hadj
  have hsnkFacts := fixedLoopCap_sink_false_query n hn e j (by simpa [hj] using hi)
  have hsrcFacts := fixedLoopCap_source_false_query n hn e i hi
  have hsinkFalse : sink.1.1.2 = false := by simpa [sink] using hsnkFacts.1
  have hsourceFalse : src.1.1.2 = false := by simpa [src] using hsrcFacts.1
  have hquery : parafermionicCoverPortEdge sink.1.1.1 =
      parafermionicCoverFiniteEdgeEmbedding n e := by
    simpa [sink] using hsnkFacts.2
  have hstate : parafermionicCoverPortBondState
      (parafermionicCoverConfigurationExtensionState n A) sink.1.1.1 = false := by
    have hnotext : parafermionicCoverFiniteEdgeEmbedding n e ∉
        parafermionicCoverConfigurationExtension n A := by
      intro hm
      exact he ((parafermionicCoverConfigurationExtension_inside n A e).mp hm)
    change parafermionicCoverConfigurationExtensionState n A
      (parafermionicCoverPortEdge sink.1.1.1) = false
    rw [hquery]
    simp [parafermionicCoverConfigurationExtensionState, hnotext]
  have hπeq : π i = i := by simpa [j] using hj
  have hrouteAdj : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj
      sink.1.1 src.1.1 := by
    simpa [sink, src, j] using hadj
  have hloop : p =
      (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i).concat hrouteAdj := by
    simp [p, parafermionicCoverFiniteEdgeCutFixedLoop, src,
      ]
  let d : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Dart :=
    ⟨(sink.1.1, src.1.1), hrouteAdj⟩
  have hd : d ∈ p.darts := by
    rw [hloop, Walk.darts_concat, List.concat_eq_append]
    simp only [List.mem_append, List.mem_singleton]
    right
    rfl
  refine ⟨d, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [p] using hd
  · rfl
  · rfl
  · exact hsinkFalse
  · exact hsourceFalse
  · exact hquery
  · exact hstate

/-- For an actual closed queried edge fixed by the terminal routing, the
positive perpendicular half-edge of its restored cap occurs in the unchanged
refined fixed-loop walk. -/
theorem parafermionicCoverFiniteEdgeCutFixedLoop_positive_capHalfEdge_mem_edges
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal)
    (hi : i ≠ 0)
    (hfix : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i = i)
    (he : e ∉ A) :
    let c : ParafermionicCoverPort := (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1.1.1
    s(parafermionicCoverRefinedClosedCapMiddle c,
      parafermionicCoverCompassNeighbor
        (parafermionicCoverRefinedClosedCapMiddle c)
        (if c.1.bond.axis = LatticeAxis.horizontal then 1 else 0)) ∈
      (parafermionicCoverRefinedPairingWalk n hn A
        (parafermionicCoverFiniteEdgeCutFixedLoop n hn A e i hi hfix)).edges := by
  let c : ParafermionicCoverPort := (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
    (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1.1.1
  change s(parafermionicCoverRefinedClosedCapMiddle c,
    parafermionicCoverCompassNeighbor (parafermionicCoverRefinedClosedCapMiddle c)
      (if c.1.bond.axis = LatticeAxis.horizontal then 1 else 0)) ∈ _
  obtain ⟨d, hd, hdSink, hdSource, hfst, hsnd, hquery, hstate⟩ :=
    parafermionicCoverFiniteEdgeCutFixedLoop_restoredClosedDart n hn A e i hi hfix he
  have hcapEdges := parafermionicCoverRefinedClosedCapWalk_edges_subset_pairingWalk
    n hn A (parafermionicCoverFiniteEdgeCutFixedLoop n hn A e i hi hfix)
    d hd hfst hsnd hstate
  have hc : d.fst.1.1 = c := by
    simpa [c] using congrArg (fun x : ParafermionicCoverFinitePort n × Bool => x.1.1) hdSink
  have hpositive := parafermionicCoverRefinedClosedCap_positivePerpendicularEdge_mem c
  rw [← hc] at hpositive
  rw [← hc]
  exact hcapEdges hpositive

end
end PottsContinuity.FKC.Medial
