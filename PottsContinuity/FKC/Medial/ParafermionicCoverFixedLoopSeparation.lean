-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverFixedLoopSeparation.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverFixedLoopCapEdge
public import PottsContinuity.FKC.Medial.ParafermionicCoverFixedLoopPrimalIntersection
public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceTransverseFillingStep
public import PottsContinuity.FKC.Medial.GraphWalkSingleMembershipFlip
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPortPrimalCrossing
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPrimalRayPath
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
open SimpleGraph
noncomputable section

 theorem fixedLoopSeparation_cycle_in_box
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal)
    (hi : i ≠ 0)
    (hfix : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i = i)
    (N : ℕ) (hR : ∀ z ∈ (parafermionicCoverRefinedPairingWalk n hn A
      (parafermionicCoverFiniteEdgeCutFixedLoop n hn A e i hi hfix)).support,
      z ∈ parafermionicCoverBoxVertices N) :
    (parafermionicCoverRefinedPairingWalk n hn A
      (parafermionicCoverFiniteEdgeCutFixedLoop n hn A e i hi hfix)).induce
        (parafermionicCoverBoxVertices N) hR |>.IsCycle := by
  let R := parafermionicCoverRefinedPairingWalk n hn A
    (parafermionicCoverFiniteEdgeCutFixedLoop n hn A e i hi hfix)
  have hRcycle : R.IsCycle := parafermionicCoverRefinedPairingWalk_isCycle n hn A _
    (parafermionicCoverFiniteEdgeCutFixedLoop_isCycle n hn A e i hi hfix)
  have hmap : (R.induce (parafermionicCoverBoxVertices N) hR).map
      (SimpleGraph.Embedding.induce (G := parafermionicCoverGraph)
        (parafermionicCoverBoxVertices N)).toHom = R := by
    simpa [R, parafermionicCoverBoxGraph] using SimpleGraph.Walk.map_induce R hR
  have hcycleMapped : ((R.induce (parafermionicCoverBoxVertices N) hR).map
      (SimpleGraph.Embedding.induce (G := parafermionicCoverGraph)
        (parafermionicCoverBoxVertices N)).toHom).IsCycle := by
    simpa [hmap] using hRcycle
  exact (SimpleGraph.Walk.isCycle_map_iff_of_injective
    (SimpleGraph.Embedding.induce (G := parafermionicCoverGraph)
      (parafermionicCoverBoxVertices N)).injective).mp hcycleMapped

private theorem fixedLoopSeparation_sink_query
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal)
    (hi : i ≠ 0)
    (hfix : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i = i)
    (he : e ∉ A) :
    parafermionicCoverPortEdge
      ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1.1) =
      parafermionicCoverFiniteEdgeEmbedding n e := by
  obtain ⟨d, _, hf, _, _, _, hquery, _⟩ :=
    parafermionicCoverFiniteEdgeCutFixedLoop_restoredClosedDart
      n hn A e i hi hfix he
  simpa [hf] using hquery

private theorem fixedLoopSeparation_coarse_edge_query
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal)
    (hi : i ≠ 0)
    (hfix : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i = i)
    (he : e ∉ A) :
    let c := (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1.1
    let u := parafermionicCoverPortVertex c
    let v := parafermionicCoverPortOtherVertex c
    let d := parafermionicCoverCompassDirection u v
      (parafermionicCoverPortVertex_otherEndpoint_adj c)
    (⟨s(u, parafermionicCoverCompassNeighbor u d), by
      apply parafermionicCoverGraph.mem_edgeSet.mpr
      exact ⟨(parafermionicCoverCompassNeighbor_adj u d).1, rfl⟩⟩ :
        parafermionicCoverGraph.edgeSet) = parafermionicCoverFiniteEdgeEmbedding n e := by
  dsimp
  let c := (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
    (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1.1
  let u := parafermionicCoverPortVertex c
  let v := parafermionicCoverPortOtherVertex c
  let d := parafermionicCoverCompassDirection u v
    (parafermionicCoverPortVertex_otherEndpoint_adj c)
  have hnbr := parafermionicCoverCompassDirection_neighbor u v
    (parafermionicCoverPortVertex_otherEndpoint_adj c)
  have hport := parafermionicCoverPortEdge_eq_incident_pair c
  have hquery := fixedLoopSeparation_sink_query n hn A e i hi hfix he
  apply Subtype.ext
  calc
    s(u, parafermionicCoverCompassNeighbor u d) = s(u,v) := by rw [hnbr]
    _ = (parafermionicCoverPortEdge c).val := hport.symm
    _ = (parafermionicCoverFiniteEdgeEmbedding n e).val := congrArg Subtype.val hquery

private theorem capMiddle_ne_port_coarseCenters (c : ParafermionicCoverPort) :
    parafermionicCoverRefinedClosedCapMiddle c ≠
        parafermionicCoverRefinedCoarseCenter (parafermionicCoverPortVertex c) ∧
      parafermionicCoverRefinedClosedCapMiddle c ≠
        parafermionicCoverRefinedCoarseCenter (parafermionicCoverPortOtherVertex c) := by
  rcases c with ⟨⟨⟨⟨x,y⟩,ax⟩,tip,side⟩,k⟩
  cases ax <;> cases tip <;> cases side <;>
    simp [parafermionicCoverRefinedClosedCapMiddle_horizontal,
      parafermionicCoverRefinedClosedCapMiddle_vertical,
      parafermionicCoverRefinedCoarseCenter, parafermionicCoverPortVertex,
      parafermionicCoverPortOtherVertex, LatticePort.primalVertex,
      LatticeBond.endpoint, LatticeBond.source, LatticeBond.target] <;> omega

private theorem portRadialNeighbor_eq (c : ParafermionicCoverPort) :
    parafermionicCoverCompassNeighbor (parafermionicCoverPortVertex c)
      (parafermionicCoverPortRadialCompass c) = parafermionicCoverPortOtherVertex c := by
  rcases c with ⟨⟨⟨⟨x,y⟩,ax⟩,tip,side⟩,k⟩
  cases ax <;> cases tip <;> cases side <;>
    simp [parafermionicCoverCompassNeighbor, parafermionicCoverCompassBaseNeighbor,
      parafermionicCoverPortRadialCompass, parafermionicCoverPortVertex,
      parafermionicCoverPortOtherVertex, LatticePort.primalVertex,
      LatticeBond.endpoint, LatticeBond.source, LatticeBond.target,
      parafermionicCoverNeighborLift, parafermionicCoverSheetShift] <;> omega

theorem parafermionicCoverFiniteEdgeCutFixedLoop_separatesActualPortFaces
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal)
    (hi : i ≠ 0)
    (hfix : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i = i)
    (he : e ∉ A) (N : ℕ) (hN : 1 ≤ N)
    (hR : ∀ z ∈ (parafermionicCoverRefinedPairingWalk n hn A
      (parafermionicCoverFiniteEdgeCutFixedLoop n hn A e i hi hfix)).support,
      z ∈ parafermionicCoverBoxVertices N)
    (hP : ∀ z ∈ (parafermionicCoverRefinedPrimalEdgeWalk
      (parafermionicCoverPortVertex
        ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e
          (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1.1))
      (parafermionicCoverCompassDirection
        (parafermionicCoverPortVertex
          ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e
            (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1.1))
        (parafermionicCoverPortOtherVertex
          ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e
            (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1.1))
        (parafermionicCoverPortVertex_otherEndpoint_adj
          ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e
            (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1.1)))).support,
      z ∈ parafermionicCoverFiniteOrdinaryFaces N) :
    let c := (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1.1
    let u := parafermionicCoverPortVertex c
    let v := parafermionicCoverPortOtherVertex c
    let d := parafermionicCoverCompassDirection u v
      (parafermionicCoverPortVertex_otherEndpoint_adj c)
    let _P := parafermionicCoverRefinedPrimalEdgeWalk u d
    let R := parafermionicCoverRefinedPairingWalk n hn A
      (parafermionicCoverFiniteEdgeCutFixedLoop n hn A e i hi hfix)
    let C := R.induce (parafermionicCoverBoxVertices N) hR
    let hC : C.IsCycle := fixedLoopSeparation_cycle_in_box n hn A e i hi hfix N hR
    ¬ ((∃ f : ParafermionicCoverFiniteFaceTopIndex N,
        f.1 = parafermionicCoverRefinedCoarseCenter u ∧
        f ∈ parafermionicCoverSimpleCycleFillingSet hN C hC) ↔
       (∃ f : ParafermionicCoverFiniteFaceTopIndex N,
        f.1 = parafermionicCoverRefinedCoarseCenter v ∧
        f ∈ parafermionicCoverSimpleCycleFillingSet hN C hC)) := by
  dsimp only
  let c := (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
    (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1.1
  let u := parafermionicCoverPortVertex c
  let v := parafermionicCoverPortOtherVertex c
  let hAdj := parafermionicCoverPortVertex_otherEndpoint_adj c
  let radial := parafermionicCoverPortRadialCompass c
  have hradialNeighbor : parafermionicCoverCompassNeighbor u radial = v :=
    portRadialNeighbor_eq c
  have hdir : parafermionicCoverCompassDirection u v hAdj = radial :=
    parafermionicCoverCompassDirection_eq_of_neighbor hAdj radial hradialNeighbor
  let d := parafermionicCoverCompassDirection u v hAdj
  let P := parafermionicCoverRefinedPrimalEdgeWalk u d
  let R := parafermionicCoverRefinedPairingWalk n hn A
    (parafermionicCoverFiniteEdgeCutFixedLoop n hn A e i hi hfix)
  let C := R.induce (parafermionicCoverBoxVertices N) hR
  have hRcycle : R.IsCycle := parafermionicCoverRefinedPairingWalk_isCycle n hn A _
    (parafermionicCoverFiniteEdgeCutFixedLoop_isCycle n hn A e i hi hfix)
  have hmap : C.map
      (SimpleGraph.Embedding.induce (G := parafermionicCoverGraph)
        (parafermionicCoverBoxVertices N)).toHom = R := by
    simpa [C, R, parafermionicCoverBoxGraph] using
      SimpleGraph.Walk.map_induce R hR
  have hCcycle : C.IsCycle := by
    have hmapped : (C.map
        (SimpleGraph.Embedding.induce (G := parafermionicCoverGraph)
          (parafermionicCoverBoxVertices N)).toHom).IsCycle := by
      simpa [hmap] using hRcycle
    exact (SimpleGraph.Walk.isCycle_map_iff_of_injective
      (SimpleGraph.Embedding.induce (G := parafermionicCoverGraph)
        (parafermionicCoverBoxVertices N)).injective).mp hmapped
  have hboxP : ∀ z ∈ P.support, z ∈ parafermionicCoverBoxVertices N := by
    intro z hz
    have hmem := hP z hz
    exact (Finset.mem_filter.mp hmem).1
  have hmapEdges : C.edges.map (Sym2.map Subtype.val) = R.edges := by
    have heq := congrArg Walk.edges hmap
    rw [Walk.edges_map] at heq
    change C.edges.map (Sym2.map Subtype.val) = R.edges
    exact heq
  have hcapP : parafermionicCoverRefinedClosedCapMiddle c ∈ P.support := by
    simpa [P, d, u, v, hdir] using
      parafermionicCoverRefinedClosedCapMiddle_mem_port_primalRay c
  have hcapR : parafermionicCoverRefinedClosedCapMiddle c ∈ R.support := by
    simpa [R, c] using
      parafermionicCoverFiniteEdgeCutFixedLoop_closed_capMiddle_mem_support
        n hn A e i hi hfix he
  have hnotEndpoints := capMiddle_ne_port_coarseCenters c
  have hnotStart : parafermionicCoverRefinedClosedCapMiddle c ≠
      parafermionicCoverRefinedCoarseCenter u := hnotEndpoints.1
  have hnotEnd : parafermionicCoverRefinedClosedCapMiddle c ≠
      parafermionicCoverRefinedCoarseCenter v := hnotEndpoints.2
  have hPpath : P.IsPath := parafermionicCoverRefinedPrimalEdgeWalk_isPath u d
  have hcoarse : (⟨s(u, parafermionicCoverCompassNeighbor u d), by
      apply parafermionicCoverGraph.mem_edgeSet.mpr
      exact ⟨(parafermionicCoverCompassNeighbor_adj u d).1, rfl⟩⟩ :
        parafermionicCoverGraph.edgeSet) = parafermionicCoverFiniteEdgeEmbedding n e := by
    simpa [c, u, v, d, hAdj] using
      fixedLoopSeparation_coarse_edge_query n hn A e i hi hfix he
  let marked := parafermionicCoverRefinedClosedCapMiddle c
  let S := parafermionicCoverSimpleCycleFillingSet hN C hCcycle
  let F : ParafermionicCoverVertex → Prop := fun z =>
    ∃ f : ParafermionicCoverFiniteFaceTopIndex N, f.1 = z ∧ f ∈ S
  have hmarked : marked ∈ P.support := by simpa [marked] using hcapP
  have hmarkedNeStart : marked ≠ parafermionicCoverRefinedCoarseCenter u := by
    simpa [marked] using hnotStart
  have hmarkedNeEnd : marked ≠ parafermionicCoverRefinedCoarseCenter v := by
    simpa [marked] using hnotEnd
  have hintersection : ∀ z, z ∈ R.support → z ∈ P.support → z = marked := by
    intro z hzR hzP
    exact parafermionicCoverFiniteEdgeCutFixedLoop_primalWalk_intersection
      n hn A e i hi hfix u d hcoarse hzR hzP
  have hcapEdge : s(marked, parafermionicCoverCompassNeighbor marked
      (if c.1.1.bond.axis = LatticeAxis.horizontal then 1 else 0)) ∈ R.edges := by
    simpa [marked, R] using
      parafermionicCoverFiniteEdgeCutFixedLoop_positive_capHalfEdge_mem_edges
        n hn A e i hi hfix he
  have hcriterion : ∀ x ∈ P.darts,
      (¬ (F x.fst ↔ F x.snd) ↔
        (if d = 0 ∨ d = 1 then x.snd else x.fst) = marked) := by
    intro x hx
    have hxFst := Walk.dart_fst_mem_support_of_mem_darts P hx
    have hxSnd := Walk.dart_snd_mem_support_of_mem_darts P hx
    have hxboxFst : x.fst ∈ parafermionicCoverFiniteOrdinaryFaces N := hP x.fst hxFst
    have hxboxSnd : x.snd ∈ parafermionicCoverFiniteOrdinaryFaces N := hP x.snd hxSnd
    let a : ParafermionicCoverFiniteFaceTopIndex N := ⟨x.fst, hxboxFst⟩
    let b : ParafermionicCoverFiniteFaceTopIndex N := ⟨x.snd, hxboxSnd⟩
    have hxdirMem : parafermionicCoverCompassDirection x.fst x.snd x.adj ∈
        List.replicate 9 d := by
      rw [← parafermionicCoverRefinedPrimalEdgeWalk_compassDirections u d]
      change parafermionicCoverCompassDirection x.fst x.snd x.adj ∈
        P.darts.map (fun y => parafermionicCoverCompassDirection y.fst y.snd y.adj)
      exact List.mem_map.mpr ⟨x, hx, rfl⟩
    have hxdir : parafermionicCoverCompassDirection x.fst x.snd x.adj = d := by
      simpa using hxdirMem
    have hxnext := parafermionicCoverCompassDirection_neighbor x.fst x.snd x.adj
    rw [hxdir] at hxnext
    have hab : b.1 = parafermionicCoverCompassNeighbor a.1 d := by
      simpa [a, b] using hxnext.symm
    have hFst : F x.fst ↔ a ∈ S := by
      constructor
      · rintro ⟨f, hf, hfm⟩
        have : f = a := Subtype.ext hf
        subst f
        exact hfm
      · intro hmem
        exact ⟨a, rfl, hmem⟩
    have hSnd : F x.snd ↔ b ∈ S := by
      constructor
      · rintro ⟨f, hf, hfm⟩
        have : f = b := Subtype.ext hf
        subst f
        exact hfm
      · intro hmem
        exact ⟨b, rfl, hmem⟩
    have hcross := parafermionicCoverSimpleCycleFillingSet_adjacent_disagree_iff_rawMappedEdge
      hN C hCcycle a b d hab
    let base := if d = 0 ∨ d = 1 then x.snd else x.fst
    let perp : Fin 4 := if d = 0 ∨ d = 2 then 1 else 0
    have hcross' : ¬ (a ∈ S ↔ b ∈ S) ↔
        s(base, parafermionicCoverCompassNeighbor base perp) ∈
          C.edges.map (Sym2.map Subtype.val) := by
      constructor
      · intro hdis
        have hmem := hcross.mp (by simpa [S, a, b] using hdis)
        rcases List.mem_map.mp hmem with ⟨edge, hedge, heq⟩
        apply List.mem_map.mpr
        refine ⟨edge, hedge, ?_⟩
        exact heq
      · intro hmem
        apply hcross.mpr
        rcases List.mem_map.mp hmem with ⟨edge, hedge, heq⟩
        apply List.mem_map.mpr
        refine ⟨edge, hedge, ?_⟩
        exact heq
    have hbaseP : base ∈ P.support := by
      by_cases hor : d = 0 ∨ d = 1
      · simp [base, hor, hxSnd]
      · simp [base, hor, hxFst]
    have hbaseR : s(base, parafermionicCoverCompassNeighbor base perp) ∈ R.edges ↔
        base = marked := by
      constructor
      · intro hedge
        have hzR : base ∈ R.support := Walk.fst_mem_support_of_mem_edges R hedge
        exact hintersection base hzR hbaseP
      · intro hbase
        have hperp : perp =
            (if c.1.1.bond.axis = LatticeAxis.horizontal then 1 else 0) := by
          subst base
          rcases c with ⟨⟨⟨⟨⟨x0,y0⟩,ax⟩,tip,side⟩,k⟩,hcbox⟩
          cases ax <;> cases tip <;> cases side <;>
            simp_all [perp, d, radial, parafermionicCoverPortRadialCompass]
        simpa [hbase, hperp] using hcapEdge
    have hbaseMapped : s(base, parafermionicCoverCompassNeighbor base perp) ∈
        C.edges.map (Sym2.map Subtype.val) ↔ base = marked := by
      rw [hmapEdges]
      exact hbaseR
    have hdisagree : ¬ (F x.fst ↔ F x.snd) ↔
        (if d = 0 ∨ d = 1 then x.snd else x.fst) = marked := by
      rw [hFst, hSnd]
      simpa [base, S] using hcross'.trans hbaseMapped
    exact hdisagree
  by_cases hor : d = 0 ∨ d = 1
  · have hstep : ∀ x ∈ P.darts,
        ((F x.fst ↔ F x.snd) ↔ x.snd ≠ marked) := by
      intro x hx
      have hc := hcriterion x hx
      have hc' : ¬ (F x.fst ↔ F x.snd) ↔ x.snd = marked := by
        simpa [hor] using hc
      constructor
      · intro hagree hne
        exact (hc'.mpr hne) hagree
      · intro hne
        by_contra hnagree
        exact hne (hc'.mp hnagree)
    have hnot := graphWalk_endpoint_not_iff_of_unique_support_flip
      P hPpath hmarked hmarkedNeStart F hstep
    have hPend : parafermionicCoverRefinedCoarseCenter
        (parafermionicCoverCompassNeighbor u d) =
          parafermionicCoverRefinedCoarseCenter v := by
      dsimp [d]
      rw [hdir, hradialNeighbor]
    have hnotEndpoints : ¬ (F (parafermionicCoverRefinedCoarseCenter u) ↔
        F (parafermionicCoverRefinedCoarseCenter v)) := by
      simpa only [hPend] using hnot
    change ¬ (F (parafermionicCoverRefinedCoarseCenter u) ↔
      F (parafermionicCoverRefinedCoarseCenter v))
    exact hnotEndpoints
  · have hstep : ∀ x ∈ P.darts,
        ((F x.fst ↔ F x.snd) ↔ x.fst ≠ marked) := by
      intro x hx
      have hc := hcriterion x hx
      have hc' : ¬ (F x.fst ↔ F x.snd) ↔ x.fst = marked := by
        simpa [hor] using hc
      constructor
      · intro hagree hne
        exact (hc'.mpr hne) hagree
      · intro hne
        by_contra hnagree
        exact hne (hc'.mp hnagree)
    have hPend : parafermionicCoverRefinedCoarseCenter
        (parafermionicCoverCompassNeighbor u d) =
          parafermionicCoverRefinedCoarseCenter v := by
      dsimp [d]
      rw [hdir, hradialNeighbor]
    have hmarkedNeP : marked ≠
        parafermionicCoverRefinedCoarseCenter
          (parafermionicCoverCompassNeighbor u d) := by
      rw [hPend]
      exact hmarkedNeEnd
    have hnot := graphWalk_endpoint_not_iff_of_unique_support_source_flip
      P hPpath hmarked hmarkedNeP F hstep
    have hnotEndpoints : ¬ (F (parafermionicCoverRefinedCoarseCenter u) ↔
        F (parafermionicCoverRefinedCoarseCenter v)) := by
      simpa only [hPend] using hnot
    change ¬ (F (parafermionicCoverRefinedCoarseCenter u) ↔
      F (parafermionicCoverRefinedCoarseCenter v))
    exact hnotEndpoints
end
end PottsContinuity.FKC.Medial
