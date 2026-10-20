/- Geometric connection proof adapted from FKconvergence, an earlier formalization by the same
author that is not publicly accessible (see `related_formalizations` in formalization.yaml):
file `FiniteFK/ParafermionicCoverEdgeCutPrimalConnection.lean`.
Adaptation: namespace relocation; normalized mass factor proved directly for the real
self-dual PD law, including q=4, using actual connection before wiring.
-/
module

public import PottsContinuity.Thm4.EdgeCutRoutingWalk
public import PottsContinuity.Thm4.ExplorationPath
public import PottsContinuity.Thm4.CriticalEdgeToggle
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
open SimpleGraph
noncomputable section

private theorem edgeCutSourcePath_actualConnected
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal) :
    ActualConnected (ParafermionicAmbientGraph n) A
      (parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1.1)
      (parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
          (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1.1) := by
  let p := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i
  have hp := p.mapLe (parafermionicCoverFiniteCornerCutPairingGraph_le n hn A)
  exact parafermionicCoverFinitePairingWalk_actualConnected n A hp

private theorem fin3_eq_one_of_ne_zero_ne_two (x : ThreeTerminal)
    (h0 : x ≠ 0) (h2 : x ≠ 2) : x = 1 := by
  have hxlt : x.val < 3 := x.isLt
  have hx0 : x.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hx2 : x.val ≠ 2 := fun h => h2 (Fin.ext h)
  apply Fin.ext
  omega

private theorem fin3_eq_two_of_ne_zero_ne_one (x : ThreeTerminal)
    (h0 : x ≠ 0) (h1 : x ≠ 1) : x = 2 := by
  have hxlt : x.val < 3 := x.isLt
  have hx0 : x.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hx1 : x.val ≠ 1 := fun h => h1 (Fin.ext h)
  apply Fin.ext
  omega

private theorem fin3_eq_zero_of_ne_one_ne_two (x : ThreeTerminal)
    (h1 : x ≠ 1) (h2 : x ≠ 2) : x = 0 := by
  have hxlt : x.val < 3 := x.isLt
  have hx1 : x.val ≠ 1 := fun h => h1 (Fin.ext h)
  have hx2 : x.val ≠ 2 := fun h => h2 (Fin.ext h)
  apply Fin.ext
  omega

private theorem perm_three_return_aux
    (π : Equiv.Perm ThreeTerminal) (i : ThreeTerminal)
    (h0 : π 0 = i) (hi : i ≠ 0) (h1 : π i ≠ 0) :
    π i = threeTerminalSwap i ∧ π (π i) = 0 := by
  fin_cases i
  · exact (hi rfl).elim
  · have h11 : π 1 ≠ 1 := by
      intro hh
      have hh' := π.injective (hh.trans h0.symm)
      norm_num at hh'
    have h12 := fin3_eq_two_of_ne_zero_ne_one (π 1) h1 h11
    have h21 : π 2 ≠ 1 := by
      intro hh
      have hh' := π.injective (hh.trans h0.symm)
      norm_num at hh'
    have h22 : π 2 ≠ 2 := by
      intro hh
      have hh' := π.injective (hh.trans h12.symm)
      norm_num at hh'
    have h20 := fin3_eq_zero_of_ne_one_ne_two (π 2) h21 h22
    simp [threeTerminalSwap_one, h12, h20]
  · have h22 : π 2 ≠ 2 := by
      intro hh
      have hh' := π.injective (hh.trans h0.symm)
      norm_num at hh'
    have h21 := fin3_eq_one_of_ne_zero_ne_two (π 2) h1 h22
    have h11 : π 1 ≠ 1 := by
      intro hh
      have hh' := π.injective (hh.trans h21.symm)
      norm_num at hh'
    have h10 : π 1 ≠ 2 := by
      intro hh
      have hh' := π.injective (hh.trans h0.symm)
      norm_num at hh'
    have h10' := fin3_eq_zero_of_ne_one_ne_two (π 1) h11 h10
    simp [threeTerminalSwap_two, h21, h10']

private theorem portOtherVertex_closedPair (c : ParafermionicCoverPort) :
    parafermionicCoverPortOtherVertex (parafermionicCoverClosedPair c) =
      parafermionicCoverPortOtherVertex c := by
  rcases c with ⟨⟨b, tip, side⟩, k⟩
  cases b; cases tip <;> cases side <;>
    simp [parafermionicCoverPortOtherVertex, parafermionicCoverClosedPair,
      LatticePort.closedPair,
      LatticeBond.source, LatticeBond.target]

private theorem sourceLabel_one_port (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSourceLabels n hn e 1).1.1.1 =
      (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closedPort := by
  simp [parafermionicCoverFiniteEdgeCutSourceClosedLabel,
    parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse]

private theorem sourceLabel_two_port (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSourceLabels n hn e 2).1.1.1 =
      (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort := by
  simp [parafermionicCoverFiniteEdgeCutSourceOpenLabel,
    parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse]

private theorem sinkLabel_one_port (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e 1).1.1.1 =
      parafermionicCoverFiniteEdgeCutSeedPort n hn e := by
  simp [parafermionicCoverFiniteEdgeCutSinkSeedLabel,
    parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse]

private theorem sinkLabel_two_port (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e 2).1.1.1 =
      (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosedPort := by
  simp [parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel,
    parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse]

private theorem closedOrbitPort_vertex_seed (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closedPort =
      parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSeedPort n hn e) := by
  apply Subtype.ext
  change parafermionicCoverPortVertex
      (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closedPort.1 =
    parafermionicCoverPortVertex
      (parafermionicCoverFiniteEdgeCutSeedPort n hn e).1
  rw [(parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closed_eq,
    parafermionicCoverClosedPair_vertex]

private theorem openClosedOrbitPort_vertex_open (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosedPort =
      parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort := by
  apply Subtype.ext
  change parafermionicCoverPortVertex
      (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosedPort.1 =
    parafermionicCoverPortVertex
      (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort.1
  rw [(parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosed_eq,
    (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).open_eq,
    parafermionicCoverOpenPair_vertex, parafermionicCoverOpenPair_vertex,
    portOtherVertex_closedPair]

theorem parafermionicCoverFiniteEdgeCutThreeReturn_connectsSelectedEdgeEndpoints
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (_hclosed : e ∉ A)
    (h0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) ≠ 0) :
    ActualConnected (ParafermionicAmbientGraph n) A
      (parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSeedPort n hn e))
      (parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort) := by
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := π 0
  have hcycle := perm_three_return_aux π i rfl h0 h1
  have hi0 : i ≠ 0 := h0
  by_cases hi1 : i = 1
  · have hπi : π i = 2 := by
      rw [hcycle.1, hi1]
      decide
    have hpath := edgeCutSourcePath_actualConnected n hn A e i
    have hsource : parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1.1 =
          parafermionicCoverFinitePortPrimalVertex n
            (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closedPort := by
      simpa [hi1] using congrArg (parafermionicCoverFinitePortPrimalVertex n)
        (sourceLabel_one_port n hn e)
    have hsink : parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSinkLabels n hn e (π i)).1.1.1 =
          parafermionicCoverFinitePortPrimalVertex n
            (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosedPort := by
      simpa [hπi] using congrArg (parafermionicCoverFinitePortPrimalVertex n)
        (sinkLabel_two_port n hn e)
    have hp : ActualConnected (ParafermionicAmbientGraph n) A
        (parafermionicCoverFinitePortPrimalVertex n
          (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closedPort)
        (parafermionicCoverFinitePortPrimalVertex n
          (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosedPort) := by
      rw [← hsource, ← hsink]
      simpa [i, π] using hpath
    rw [closedOrbitPort_vertex_seed, openClosedOrbitPort_vertex_open] at hp
    exact hp

  · have hi2 : i = 2 := by
      apply fin3_eq_two_of_ne_zero_ne_one
      · exact hi0
      · exact hi1
    have hπi : π i = 1 := by
      rw [hcycle.1, hi2]
      decide
    have hpath := edgeCutSourcePath_actualConnected n hn A e i
    have hsource : parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1.1 =
          parafermionicCoverFinitePortPrimalVertex n
            (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort := by
      simpa [hi2] using congrArg (parafermionicCoverFinitePortPrimalVertex n)
        (sourceLabel_two_port n hn e)
    have hsink : parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSinkLabels n hn e (π i)).1.1.1 =
          parafermionicCoverFinitePortPrimalVertex n
            (parafermionicCoverFiniteEdgeCutSeedPort n hn e) := by
      simpa [hπi] using congrArg (parafermionicCoverFinitePortPrimalVertex n)
        (sinkLabel_one_port n hn e)
    have hp : ActualConnected (ParafermionicAmbientGraph n) A
        (parafermionicCoverFinitePortPrimalVertex n
          (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort)
        (parafermionicCoverFinitePortPrimalVertex n
          (parafermionicCoverFiniteEdgeCutSeedPort n hn e)) := by
      rw [← hsource, ← hsink]
      simpa [i, π] using hpath
    exact hp.symm

theorem selectedEdge_eq_seedOpenPort_endpoints
    (n : ℕ) (hn : 1 ≤ n) (e : (ParafermionicAmbientGraph n).edgeSet) :
    e.1 = s(
      parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSeedPort n hn e),
      parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort) := by
  let seed := parafermionicCoverFiniteEdgeCutSeedPort n hn e
  let orbit := parafermionicCoverFiniteEdgeCutSeedOrbit n hn e
  have hseedmem := (parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e).1
  have hseedEdge : parafermionicCoverPortEdge seed.1 =
      parafermionicCoverFiniteEdgeEmbedding n e := by
    simpa [seed, parafermionicCoverFiniteEdgeCutQueriedPorts] using hseedmem
  have hopen : parafermionicCoverPortVertex orbit.openPort.1 =
      parafermionicCoverPortOtherVertex seed.1 := by
    rw [orbit.open_eq, parafermionicCoverOpenPair_vertex]
  let f := parafermionicCoverBoxVertexEmbedding n
  let u := parafermionicCoverFinitePortPrimalVertex n seed
  let v := parafermionicCoverFinitePortPrimalVertex n orbit.openPort
  have hu : f u = parafermionicCoverPortVertex seed.1 := rfl
  have hv : f v = parafermionicCoverPortOtherVertex seed.1 := by
    change parafermionicCoverPortVertex orbit.openPort.1 = _
    exact hopen
  have hport : (parafermionicCoverFiniteEdgeEmbedding n e).1 =
      s(parafermionicCoverPortVertex seed.1,
        parafermionicCoverPortOtherVertex seed.1) := by
    calc
      (parafermionicCoverFiniteEdgeEmbedding n e).1 =
          (parafermionicCoverPortEdge seed.1).1 := congrArg Subtype.val hseedEdge.symm
      _ = s(parafermionicCoverPortVertex seed.1,
          parafermionicCoverPortOtherVertex seed.1) :=
        parafermionicCoverPortEdge_eq_incident_pair seed.1
  have hmap : Sym2.map f e.1 = s(f u, f v) := by
    calc
      Sym2.map f e.1 = (parafermionicCoverFiniteEdgeEmbedding n e).1 := rfl
      _ = s(parafermionicCoverPortVertex seed.1,
          parafermionicCoverPortOtherVertex seed.1) := hport
      _ = s(f u, f v) := by rw [← hu, ← hv]
  apply Sym2.map.injective f.injective
  simpa [u, v, f, Function.Embedding.sym2Map_apply] using hmap


/-- The actual three-return class has the self-dual opening mass factor sqrt(q)
for every real q ≥ 1 and every boundary partition. -/
theorem threeReturn_selfDual_probability (n : ℕ) (hn : 1 ≤ n)
    (q : Set.Ici (1 : ℝ)) (ξ : BoundaryCondition (ParafermionicAmbientVertex n))
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (hclosed : e ∉ A)
    (h0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) ≠ 0) :
    configurationProbability (ParafermionicAmbientGraph n) (selfDualParameters q) ξ
        (toggleEdgeConfiguration e A) =
      loopWeight q * configurationProbability (ParafermionicAmbientGraph n)
        (selfDualParameters q) ξ A := by
  let G := ParafermionicAmbientGraph n
  let u := parafermionicCoverFinitePortPrimalVertex n
    (parafermionicCoverFiniteEdgeCutSeedPort n hn e)
  let v := parafermionicCoverFinitePortPrimalVertex n
    (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort
  have hconn := parafermionicCoverFiniteEdgeCutThreeReturn_connectsSelectedEdgeEndpoints
    n hn A e hclosed h0 h1
  have heval := selectedEdge_eq_seedOpenPort_endpoints n hn e
  have huv : G.Adj u v := by
    apply G.mem_edgeSet.mp
    simpa [G, u, v, heval] using e.property
  have hsame : e = (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) := Subtype.ext heval
  have hnot : (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A := by
    simpa [← hsame] using hclosed
  have hrelated : (componentSetoid G ξ A).r u v :=
    actualConnected_component G ξ A (by simpa [G, u, v] using hconn)
  have hprob := configurationProbability_insert_eq_loopWeight_mul_of_related q ξ A huv hnot hrelated
  simpa only [← hsame, toggleEdgeConfiguration, ite_eq_right hclosed] using hprob

end
end PottsContinuity.Thm4
