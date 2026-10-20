-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverFixedLoopPrimalIntersection.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPrimalEdgeIntersections
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedGridRouteClassification
public import PottsContinuity.FKC.Medial.ParafermionicCoverFixedLoopQueriedDart
public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutRoutingWalk
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPairingSimplicity
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverConfigurationExtension
public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutTerminals
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
open SimpleGraph
noncomputable section

private theorem graphWalkSubstitute_support_tail_local {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (route : ∀ {u v : V}, G.Adj u v → H.Walk (f u) (f v))
    {u v : V} (p : G.Walk u v) :
    (graphWalkSubstitute G H f route p).support.tail =
      p.darts.flatMap fun d => (route d.adj).support.tail := by
  induction p with
  | nil => simp [graphWalkSubstitute]
  | cons h p ih =>
      rw [graphWalkSubstitute_cons, Walk.tail_support_append,
        Walk.darts_cons, List.flatMap_cons, ih]

private theorem fixedLoop_source_edge_query
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

private theorem fixedLoop_sink_edge_query
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

/-- A point shared by the actual refined fixed loop and an actual primal-edge
walk is the cap midpoint at the loop's actual sink terminal. -/
theorem parafermionicCoverFiniteEdgeCutFixedLoop_primalWalk_intersection
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal)
    (hi : i ≠ 0)
    (hfix : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i = i)
    (u : ParafermionicCoverVertex) (d : Fin 4)
    (hcoarse : (⟨s(u, parafermionicCoverCompassNeighbor u d), by
          apply parafermionicCoverGraph.mem_edgeSet.mpr
          exact ⟨(parafermionicCoverCompassNeighbor_adj u d).1, rfl⟩⟩ :
          parafermionicCoverGraph.edgeSet) = parafermionicCoverFiniteEdgeEmbedding n e)
    {z : ParafermionicCoverVertex}
    (hzLoop : z ∈ (parafermionicCoverRefinedPairingWalk n hn A
      (parafermionicCoverFiniteEdgeCutFixedLoop n hn A e i hi hfix)).support)
    (hzPrimal : z ∈ (parafermionicCoverRefinedPrimalEdgeWalk u d).support) :
    z = parafermionicCoverRefinedClosedCapMiddle
      ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1.1) := by
  have hgrid := parafermionicCoverRefinedPrimalEdgeWalk_support_modulus u d z hzPrimal
  obtain ⟨w, hw, hwfalse, hwfalse', hwstate, hwz⟩ :=
    parafermionicCoverRefinedPairingWalk_grid_support_classification n hn A
      (parafermionicCoverFiniteEdgeCutFixedLoop n hn A e i hi hfix) hgrid hzLoop
  have hcapPrimal : parafermionicCoverRefinedClosedCapMiddle w.fst.1.1 ∈
      (parafermionicCoverRefinedPrimalEdgeWalk u d).support := by
    simpa [hwz] using hzPrimal
  have hcapEdge := parafermionicCoverRefinedClosedCapMiddle_walk_portEdge u d
    w.fst.1.1 hcapPrimal
  have hquery : parafermionicCoverPortEdge w.fst.1.1 =
      parafermionicCoverFiniteEdgeEmbedding n e := by
    exact hcapEdge.trans hcoarse
  have hlabels := parafermionicCoverFiniteEdgeCutFixedLoop_queried_false_false_dart
    n hn A e i hi hfix hw hwfalse hwfalse' hquery
  calc
    z = parafermionicCoverRefinedClosedCapMiddle w.fst.1.1 := hwz
    _ = parafermionicCoverRefinedClosedCapMiddle
        ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e
          (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1.1) := by
      rw [hlabels.1]

/-- When the queried actual edge is closed, its restored cap midpoint is
present in the unchanged refined fixed loop. -/
theorem parafermionicCoverFiniteEdgeCutFixedLoop_closed_capMiddle_mem_support
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal)
    (hi : i ≠ 0)
    (hfix : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i = i)
    (he : e ∉ A) :
    parafermionicCoverRefinedClosedCapMiddle
      ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1.1) ∈
      (parafermionicCoverRefinedPairingWalk n hn A
        (parafermionicCoverFiniteEdgeCutFixedLoop n hn A e i hi hfix)).support := by
  let j := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i
  let sink := parafermionicCoverFiniteEdgeCutSinkLabels n hn e j
  let src := parafermionicCoverFiniteEdgeCutSourceLabels n hn e i
  let p := parafermionicCoverFiniteEdgeCutFixedLoop n hn A e i hi hfix
  have hsucc : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i ≠ 0 := by
    intro hz
    exact hi (hfix.symm.trans hz)
  have hadj := parafermionicCoverFiniteEdgeCutRoutingAdj n hn A e i hsucc
  have hfalse : e ∉ A := he
  have hj : j = i := by
    dsimp [j]
    simpa [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he] using hfix
  have hsrcFacts := fixedLoop_source_edge_query n hn e i hi
  have hsucc_pi : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i ≠ 0 := by
    simpa [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he] using hsucc
  have hsnkFacts := fixedLoop_sink_edge_query n hn e
    (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i) hsucc_pi
  have hiLabel : src.1.1.2 = false := by simpa [src] using hsrcFacts.1
  have hjLabel : sink.1.1.2 = false := by simpa [sink, j] using hsnkFacts.1
  have hquery : parafermionicCoverPortEdge sink.1.1.1 =
      parafermionicCoverFiniteEdgeEmbedding n e := by
    simpa [sink, j] using hsnkFacts.2
  have hstate : parafermionicCoverPortBondState
      (parafermionicCoverConfigurationExtensionState n A) sink.1.1.1 = false := by
    have hnotext : parafermionicCoverFiniteEdgeEmbedding n e ∉
        parafermionicCoverConfigurationExtension n A := by
      intro hm
      exact he ((parafermionicCoverConfigurationExtension_inside n A e).mp hm)
    change parafermionicCoverConfigurationExtensionState n A
      (parafermionicCoverPortEdge
        (parafermionicCoverFiniteEdgeCutSinkLabels n hn e j).1.1.1) = false
    rw [hquery]
    simp [parafermionicCoverConfigurationExtensionState, hnotext]
  have hrouteAdj : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj
      sink.1.1 src.1.1 := by
    rw [hfix] at hadj
    simpa [sink, src, j, hj] using hadj
  have hloop : p =
      (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i).concat
        hrouteAdj := by
    simp [p, parafermionicCoverFiniteEdgeCutFixedLoop, src,
      ]
  let d : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Dart :=
    ⟨(sink.1.1, src.1.1), hrouteAdj⟩
  have hd : d ∈ p.darts := by
    rw [hloop, Walk.darts_concat, List.concat_eq_append]
    simp only [List.mem_append, List.mem_singleton]
    right
    rfl
  have htail := graphWalkSubstitute_support_tail_local
    (parafermionicCoverFiniteCornerCutPairingGraph n hn A)
    parafermionicCoverGraph parafermionicCoverRefinedPairingEmbedding
    (fun {a b} h => parafermionicCoverRefinedPairingRoute n hn A h) p
  have hmidroute : parafermionicCoverRefinedClosedCapMiddle sink.1.1.1 ∈
      (parafermionicCoverRefinedPairingRoute n hn A d.adj).support.tail := by
    rw [parafermionicCoverRefinedPairingRoute_support]
    simp [parafermionicCoverRefinedPairingRouteSupport, d, sink, src,
      hiLabel, hjLabel, hstate]
  have hmidtail : parafermionicCoverRefinedClosedCapMiddle sink.1.1.1 ∈
      (parafermionicCoverRefinedPairingWalk n hn A p).support.tail := by
    change parafermionicCoverRefinedClosedCapMiddle sink.1.1.1 ∈
      (graphWalkSubstitute (parafermionicCoverFiniteCornerCutPairingGraph n hn A)
        parafermionicCoverGraph parafermionicCoverRefinedPairingEmbedding
        (fun {a b} h => parafermionicCoverRefinedPairingRoute n hn A h) p).support.tail
    rw [htail]
    exact List.mem_flatMap.mpr ⟨d, hd, hmidroute⟩
  rw [← Walk.cons_tail_support]
  exact List.mem_cons_of_mem _ hmidtail

end
end PottsContinuity.FKC.Medial
